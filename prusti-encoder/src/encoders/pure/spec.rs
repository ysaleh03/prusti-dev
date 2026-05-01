use std::{borrow::Borrow, marker::PhantomData};

use prusti_interface::{
    PrustiError,
    specs::{specifications::find_trait_method_substs, typed::Pledge},
};
use prusti_rustc_interface::{
    middle::{mir, ty},
    span::{Span, def_id::DefId},
};

use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, HasType, Reify, macros::ExprQuote};

use crate::encoders::{
    Impure, MirLocalDefEncTask, MirPureEnc, NotPure, Purified, TyUsePurifiedEnc,
    mir_fn::RustSignature,
    mir_pure::{ExprInput, PureKind},
    ty::{RustTyDecomposition, generics::GParams, use_pure::TyUsePureEnc},
};
pub struct MirSpecEnc<P: NotPure>(PhantomData<P>);

/// The VIR expression and span corresponding to either the lhs or rhs of a
/// pledge. It will be conjoined to the permission expression of the
/// corresponding side of the wand for the encoded pledge.
#[derive(Debug, Clone, Copy)]
pub struct PledgeExpr<'vir> {
    did: DefId,
    expr: vir::ExprGenBool<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>,
}

#[derive(Debug, Clone, Copy)]
pub struct PledgeArgs<'vir>(&'vir [vir::ExprSnap<'vir>]);

impl<'vir> std::ops::Index<mir::Local> for PledgeArgs<'vir> {
    type Output = vir::ExprSnap<'vir>;

    fn index(&self, index: mir::Local) -> &Self::Output {
        if index == mir::RETURN_PLACE {
            self.0.last().unwrap()
        } else {
            &self.0[index.as_usize() - 1]
        }
    }
}

impl<'vir> PledgeExpr<'vir> {
    pub fn new(
        did: DefId,
        expr: vir::ExprGenBool<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>,
    ) -> Self {
        Self { did, expr }
    }

    pub fn pledge_args<T: Borrow<vir::ExprSnap<'vir>>>(
        result: vir::ExprSnap<'vir>,
        args: impl IntoIterator<Item = T>,
    ) -> PledgeArgs<'vir> {
        let all_args = args
            .into_iter()
            .map(|a| *a.borrow())
            .chain([result])
            .collect::<Vec<_>>();
        vir::with_vcx(|vcx| PledgeArgs(vcx.alloc_slice(&all_args)))
    }

    pub fn expr(&self, args: PledgeArgs<'vir>) -> vir::ExprBool<'vir> {
        vir::with_vcx(|vcx| self.expr.reify(vcx, (self.did, args.0)))
    }

    pub fn purified_expr(&self, args: PledgeArgs<'vir>) -> vir::ExprBool<'vir> {
        vir::with_vcx(|vcx| {
            self.expr
                .purified_reify(vcx, ((self.did, args.0), (self.did, args.0)))
        })
    }

    pub fn span(&self) -> Span {
        vir::with_vcx(|vcx| vcx.tcx().def_span(self.did))
    }
}

/// VIR expressions for a pledge, including a user-written `assert_on_expiry`
/// predicate if present.
#[derive(Clone, Copy, Debug)]
pub struct EncodedPledge<'vir> {
    /// The VIR expression and span corresponding to the `assert_on_expiry`
    /// predicate, if present.
    pub expiry_obligation: Option<PledgeExpr<'vir>>,
    /// The pure rhs of the wand.
    pub expiry_postcondition: PledgeExpr<'vir>,
}

#[derive(Clone)]
pub struct MirSpecEncOutput<'vir> {
    pub pres: Vec<vir::ExprBool<'vir>>,
    pub posts: Vec<vir::ExprBool<'vir>>,
    pub pledges: Vec<EncodedPledge<'vir>>,
    pub pre_args: &'vir [vir::ExprSnap<'vir>],
    #[allow(dead_code)]
    pub post_args: &'vir [vir::ExprSnap<'vir>],
}

impl TaskEncoder for MirSpecEnc<Impure> {
    task_encoder::encoder_cache!(MirSpecEnc<Impure>);

    type TaskDescription<'tcx> = (
        DefId, // The function annotated with specs
        DefId, // Context, i.e., where the specs are emitted
        bool,  // If to encode as pure or not
    );

    type OutputFullDependency<'vir> = MirSpecEncOutput<'vir>;

    type EncodingError = <MirPureEnc<Impure> as TaskEncoder>::EncodingError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let (def_id, context_def_id, pure) = *task_key;
        deps.emit_output_ref(*task_key, ())?;

        vir::with_vcx(|vcx| {
            let base_params = GParams::from(def_id);
            let context_params = GParams::from(context_def_id);
            let substs =
                find_trait_method_substs(vcx.tcx(), context_def_id, context_params.rust_params())
                    .map(|s| s.1)
                    .unwrap_or(base_params.rust_params());
            let local_defs = deps
                .require_dep::<crate::encoders::local_def::MirLocalDefEnc<Impure>>(
                    MirLocalDefEncTask::LocalSubsts {
                        def_id,
                        context_def_id,
                        substs: if def_id == context_def_id {
                            context_params.rust_params()
                        } else {
                            substs
                        },
                        all_locals: false,
                    },
                )?;
            let specs = deps
                .require_dep::<crate::encoders::SpecEnc>(crate::encoders::SpecEncTask { def_id })?;
            let local_iter = (1..=local_defs.arg_count).map(mir::Local::from);
            let all_args: Vec<vir::ExprSnap<'vir>> = if pure {
                let result_ty = local_defs[mir::RETURN_PLACE].local_snap.ty();
                local_iter
                    .map(|local| vcx.mk_local_ex(local_defs[local].local_snap))
                    .chain([vcx.mk_result(result_ty)])
                    .collect()
            } else {
                local_iter
                    .map(|local| local_defs[local].impure_snap)
                    .collect()
            };
            let all_args = vcx.alloc_slice(&all_args);
            let pre_args = if pure {
                &all_args[..all_args.len() - 1]
            } else {
                all_args
            };

            let to_bool = deps
                .require_dep::<TyUsePureEnc>(RustTyDecomposition::from_prim_ty(
                    vcx.tcx().types.bool,
                ))?
                .expect_pure_native()
                .snap_to_prim;

            let substs = find_trait_method_substs(vcx.tcx(), def_id, substs)
                .map(|s| s.1)
                .unwrap_or(substs);

            let pres = specs
                .pres
                .iter()
                .map(|spec_def_id| {
                    let expr = deps
                        .require_dep::<crate::encoders::MirPureEnc<Impure>>(
                            crate::encoders::MirPureEncTask {
                                encoding_depth: 0,
                                kind: PureKind::Spec(specs.extern_spec),
                                parent_def_id: *spec_def_id,
                                param_env: vcx.tcx().param_env(spec_def_id),
                                substs,
                                // TODO: should this be `def_id` or `caller_def_id`
                                caller_def_id: Some(def_id),
                            },
                        )
                        .unwrap()
                        .expr
                        .downcast_ty();
                    let expr = expr.reify(vcx, (*spec_def_id, pre_args));
                    let span = vcx.tcx().def_span(spec_def_id);
                    vcx.with_span(span, |_| to_bool(expr).downcast_ty())
                })
                .collect::<Vec<vir::ExprBool<'_>>>();

            let post_args = if pure {
                all_args
            } else {
                let post_args: Vec<vir::ExprSnap<'vir>> = pre_args
                    .iter()
                    .map(|arg| vcx.mk_old_expr(arg))
                    .chain([local_defs[mir::RETURN_PLACE].impure_snap])
                    .collect();
                vcx.alloc_slice(&post_args)
            };
            let posts = specs
                .posts
                .iter()
                .map(|spec_def_id| {
                    let span = vcx.tcx().def_span(spec_def_id);
                    vcx.with_span(span, |vcx| {
                        vcx.handle_error("postcondition.violated:assertion.false", move |_| {
                            Some(vec![PrustiError::verification(
                                "postcondition might not hold",
                                span.into(),
                            )])
                        });
                        let expr = deps
                            .require_dep::<crate::encoders::MirPureEnc<Impure>>(
                                crate::encoders::MirPureEncTask {
                                    encoding_depth: 0,
                                    kind: PureKind::Spec(specs.extern_spec),
                                    parent_def_id: *spec_def_id,
                                    param_env: vcx.tcx().param_env(spec_def_id),
                                    substs,
                                    // TODO: should this be `def_id` or `caller_def_id`
                                    caller_def_id: Some(def_id),
                                },
                            )?
                            .expr
                            .downcast_ty();
                        let expr = expr.reify(vcx, (*spec_def_id, post_args));
                        Ok(to_bool(expr).downcast_ty())
                    })
                })
                .collect::<Result<Vec<vir::ExprBool<'_>>, _>>()?;
            let pledge_args = vcx.alloc_slice(
                &pre_args
                    .iter()
                    .map(|arg| vcx.mk_old_expr(arg))
                    .chain([local_defs[mir::RETURN_PLACE].impure_snap])
                    .collect::<Vec<_>>(),
            );
            let pledges = specs
                .pledges
                .iter()
                .map(
                    |Pledge {
                         lhs: lhs_def_id,
                         rhs: rhs_def_id,
                         ..
                     }| {
                        // TODO: report error locations
                        let lhs_expr = lhs_def_id.map(|lhs_def_id| {
                            deps.require_dep::<crate::encoders::MirPureEnc<Impure>>(
                                crate::encoders::MirPureEncTask {
                                    encoding_depth: 0,
                                    kind: PureKind::Spec(specs.extern_spec),
                                    parent_def_id: lhs_def_id,
                                    param_env: vcx.tcx().param_env(lhs_def_id),
                                    substs,
                                    // TODO: should this be `def_id` or `caller_def_id`
                                    caller_def_id: Some(def_id),
                                },
                            )
                            .unwrap()
                            .expr
                            .downcast_ty()
                        });
                        let rhs_expr = deps
                            .require_dep::<crate::encoders::MirPureEnc<Impure>>(
                                crate::encoders::MirPureEncTask {
                                    encoding_depth: 0,
                                    kind: PureKind::Spec(specs.extern_spec),
                                    parent_def_id: *rhs_def_id,
                                    param_env: vcx.tcx().param_env(rhs_def_id),
                                    substs,
                                    // TODO: should this be `def_id` or `caller_def_id`
                                    caller_def_id: Some(def_id),
                                },
                            )
                            .unwrap()
                            .expr
                            .downcast_ty();
                        let lhs_expr = lhs_expr.map(|lhs_expr| {
                            PledgeExpr::new(
                                lhs_def_id.unwrap(),
                                to_bool.call()(lhs_expr).downcast_ty(),
                            )
                        });
                        let rhs_span = vcx.tcx().def_span(rhs_def_id);
                        let rhs_expr = vcx.with_span(rhs_span, move |vcx| {
                            vcx.handle_error("exhale.failed:assertion.false", move |_| {
                                Some(vec![PrustiError::verification(
                                    "pledge postcondition might not hold",
                                    rhs_span.into(),
                                )])
                            });
                            to_bool.call()(rhs_expr).downcast_ty()
                        });
                        let rhs_expr = PledgeExpr::new(*rhs_def_id, rhs_expr);
                        EncodedPledge {
                            expiry_obligation: lhs_expr,
                            expiry_postcondition: rhs_expr,
                        }
                    },
                )
                .collect::<Vec<_>>();
            let data = MirSpecEncOutput {
                pres,
                posts,
                pledges,
                pre_args,
                post_args,
            };
            Ok(((), data))
        })
    }
}

impl TaskEncoder for MirSpecEnc<Purified> {
    task_encoder::encoder_cache!(MirSpecEnc<Purified>);

    type TaskDescription<'tcx> = (
        DefId, // The function annotated with specs
        DefId, // Context, i.e., where the specs are emitted
        bool,  // If to encode as pure or not
    );

    type OutputFullDependency<'vir> = MirSpecEncOutput<'vir>;

    type EncodingError = <MirPureEnc<Purified> as TaskEncoder>::EncodingError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let (def_id, context_def_id, pure) = *task_key;
        let signature = RustSignature::new(def_id);

        deps.emit_output_ref(*task_key, ())?;

        let local_defs = deps.require_dep::<crate::encoders::local_def::MirLocalDefEnc<Purified>>(
            MirLocalDefEncTask::Local {
                def_id,
                all_locals: false,
            },
        )?;

        vir::with_vcx(|vcx| {
            let base_params = GParams::from(def_id);
            let context_params = GParams::from(context_def_id);
            let substs =
                find_trait_method_substs(vcx.tcx(), context_def_id, context_params.rust_params())
                    .map(|s| s.1)
                    .unwrap_or(base_params.rust_params());
            let local_defs = deps
                .require_dep::<crate::encoders::local_def::MirLocalDefEnc<Purified>>(
                    MirLocalDefEncTask::LocalSubsts {
                        def_id,
                        context_def_id,
                        substs: if def_id == context_def_id {
                            context_params.rust_params()
                        } else {
                            substs
                        },
                        all_locals: false,
                    },
                )?;
            let specs = deps
                .require_dep::<crate::encoders::SpecEnc>(crate::encoders::SpecEncTask { def_id })?;
            let local_iter = (1..=local_defs.arg_count).map(mir::Local::from);
            let all_args: Vec<vir::ExprSnap<'vir>> = if pure {
                let result_ty = local_defs[mir::RETURN_PLACE].local_snap.ty();
                local_iter
                    .map(|local| local_defs[local].local_snap_ex)
                    .chain([vcx.mk_result(result_ty)])
                    .collect()
            } else {
                local_iter
                    .map(|local| local_defs[local].local_snap_ex)
                    .collect()
            };
            let all_args = vcx.alloc_slice(&all_args);
            let pre_args = if pure {
                &all_args[..all_args.len() - 1]
            } else {
                let pre_args: Vec<vir::ExprSnap<'vir>> = local_defs
                    .local_decl_args()
                    .map(|decl| {
                        vcx.mk_local_decl(
                            vir::vir_format_identifier!(vcx, "{}_param", decl.name).to_str(),
                            decl.ty,
                        )
                        .expr(vcx)
                    })
                    .collect();
                vcx.alloc_slice(&pre_args)
            };

            let to_bool = deps
                .require_dep::<TyUsePurifiedEnc>(RustTyDecomposition::from_prim_ty(
                    vcx.tcx().types.bool,
                ))?
                .expect_purified_native()
                .snap_to_prim;

            let substs = find_trait_method_substs(vcx.tcx(), def_id, substs)
                .map(|s| s.1)
                .unwrap_or(substs);

            let pres = specs
                .pres
                .iter()
                .map(|spec_def_id| {
                    let expr = deps
                        .require_dep::<crate::encoders::MirPureEnc<Purified>>(
                            crate::encoders::MirPureEncTask {
                                encoding_depth: 0,
                                kind: PureKind::Spec(specs.extern_spec),
                                parent_def_id: *spec_def_id,
                                param_env: vcx.tcx().param_env(spec_def_id),
                                substs,
                                // TODO: should this be `def_id` or `caller_def_id`
                                caller_def_id: Some(def_id),
                            },
                        )
                        .unwrap()
                        .expr
                        .downcast_ty();
                    let expr = expr.reify(vcx, (*spec_def_id, pre_args));
                    let span = vcx.tcx().def_span(spec_def_id);
                    vcx.with_span(span, |_| to_bool(expr).downcast_ty())
                })
                .collect::<Vec<vir::ExprBool<'_>>>();

            fn contains_mut_ref<'vir>(ty: ty::Ty<'vir>, tcx: ty::TyCtxt<'vir>) -> bool {
                match ty.kind() {
                    ty::TyKind::Ref(_, _, ty::Mutability::Mut) => true,
                    ty::TyKind::Adt(adt_def, substs) => adt_def
                        .all_fields()
                        .any(|f| contains_mut_ref(f.ty(tcx, substs), tcx)),
                    ty::TyKind::Tuple(tys) => tys.iter().any(|t| contains_mut_ref(t, tcx)),
                    _ => false,
                }
            }

            let post_args = if pure {
                all_args
            } else {
                let post_args: Vec<vir::ExprSnap<'vir>> = local_defs
                    .local_decl_args()
                    .zip(signature.inputs.iter())
                    .map(|(decl, ty)| {
                        let suffix = if contains_mut_ref(ty.0, vcx.tcx()) {
                            "_return"
                        } else {
                            "_param"
                        };
                        vcx.mk_local_decl(
                            vir::vir_format_identifier!(vcx, "{}{}", decl.name, suffix).to_str(),
                            decl.ty,
                        )
                        .expr(vcx)
                    })
                    .chain([local_defs.ret().local_snap_ex])
                    .collect();
                vcx.alloc_slice(&post_args)
            };
            let posts = specs
                .posts
                .iter()
                .map(|spec_def_id| {
                    let span = vcx.tcx().def_span(spec_def_id);
                    vcx.with_span(span, |vcx| {
                        vcx.handle_error("postcondition.violated:assertion.false", move |_| {
                            Some(vec![PrustiError::verification(
                                "postcondition might not hold",
                                span.into(),
                            )])
                        });
                        let expr = deps
                            .require_dep::<crate::encoders::MirPureEnc<Purified>>(
                                crate::encoders::MirPureEncTask {
                                    encoding_depth: 0,
                                    kind: PureKind::Spec(specs.extern_spec),
                                    parent_def_id: *spec_def_id,
                                    param_env: vcx.tcx().param_env(spec_def_id),
                                    substs,
                                    // TODO: should this be `def_id` or `caller_def_id`
                                    caller_def_id: Some(def_id),
                                },
                            )?
                            .expr
                            .downcast_ty();
                        let expr = expr.purified_reify(
                            vcx,
                            ((*spec_def_id, pre_args), (*spec_def_id, post_args)),
                        );
                        Ok(to_bool(expr).downcast_ty())
                    })
                })
                .collect::<Result<Vec<vir::ExprBool<'_>>, _>>()?;

            let mk_pf_expr = |decl: vir::LocalDeclSnap<'vir>| {
                let pf_name = vir::vir_format!(vcx, "_pf{}", decl.name);
                vcx.mk_local_decl(pf_name, decl.ty()).expr(vcx)
            };

            let pledge_args = vcx.alloc_slice(
                &(1..=local_defs.arg_count)
                    .map(|i| local_defs[mir::Local::from(i)].local_snap_ex)
                    .chain([mk_pf_expr(local_defs[mir::RETURN_PLACE].local_snap)])
                    .collect::<Vec<_>>(),
            );

            let pledges = specs
                .pledges
                .iter()
                .map(
                    |Pledge {
                         lhs: lhs_def_id,
                         rhs: rhs_def_id,
                         ..
                     }| {
                        // TODO: report error locations
                        let lhs_expr = lhs_def_id.map(|lhs_def_id| {
                            deps.require_dep::<crate::encoders::MirPureEnc<Purified>>(
                                crate::encoders::MirPureEncTask {
                                    encoding_depth: 0,
                                    kind: PureKind::Spec(specs.extern_spec),
                                    parent_def_id: lhs_def_id,
                                    param_env: vcx.tcx().param_env(lhs_def_id),
                                    substs,
                                    // TODO: should this be `def_id` or `caller_def_id`
                                    caller_def_id: Some(def_id),
                                },
                            )
                            .unwrap()
                            .expr
                            .downcast_ty()
                        });
                        let rhs_expr = deps
                            .require_dep::<crate::encoders::MirPureEnc<Purified>>(
                                crate::encoders::MirPureEncTask {
                                    encoding_depth: 0,
                                    kind: PureKind::Spec(specs.extern_spec),
                                    parent_def_id: *rhs_def_id,
                                    param_env: vcx.tcx().param_env(rhs_def_id),
                                    substs,
                                    // TODO: should this be `def_id` or `caller_def_id`
                                    caller_def_id: Some(def_id),
                                },
                            )
                            .unwrap()
                            .expr
                            .downcast_ty();
                        let lhs_expr = lhs_expr.map(|lhs_expr| {
                            PledgeExpr::new(
                                lhs_def_id.unwrap(),
                                to_bool.call()(lhs_expr).downcast_ty(),
                            )
                        });
                        let rhs_span = vcx.tcx().def_span(rhs_def_id);
                        let rhs_expr = vcx.with_span(rhs_span, move |vcx| {
                            vcx.handle_error("exhale.failed:assertion.false", move |_| {
                                Some(vec![PrustiError::verification(
                                    "pledge postcondition might not hold",
                                    rhs_span.into(),
                                )])
                            });
                            to_bool.call()(rhs_expr).downcast_ty()
                        });
                        let rhs_expr = PledgeExpr::new(*rhs_def_id, rhs_expr);
                        EncodedPledge {
                            expiry_obligation: lhs_expr,
                            expiry_postcondition: rhs_expr,
                        }
                    },
                )
                .collect::<Vec<_>>();
            let data = MirSpecEncOutput {
                pres,
                posts,
                pledges,
                pre_args,
                post_args,
            };
            Ok(((), data))
        })
    }
}
