use prusti_interface::{
    PrustiError,
    specs::{specifications::find_trait_method_substs, typed::Pledge},
};
use prusti_rustc_interface::{
    middle::{mir, ty},
    span::def_id::DefId,
};

use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, Reify, macros::ExprQuote};

use crate::encoders::{
    MirPureEnc, PurifiedMirLocalDefEncTask, TyUsePurifiedEnc,
    mir_fn::RustSignature,
    mir_pure::PureKind,
    pure::spec::{EncodedPledge, PledgeExpiryObligation},
    ty::{RustTyDecomposition, generics::GParams},
};

pub struct PurifiedMirSpecEnc;

#[derive(Clone)]
pub struct PurifiedMirSpecEncOutput<'vir> {
    pub pres: Vec<vir::ExprBool<'vir>>,
    pub posts: Vec<vir::ExprBool<'vir>>,
    pub pledges: Vec<EncodedPledge<'vir>>,
    pub pre_args: &'vir [vir::ExprSnap<'vir>],
    #[allow(dead_code)]
    pub post_args: &'vir [vir::ExprSnap<'vir>],
}

impl TaskEncoder for PurifiedMirSpecEnc {
    task_encoder::encoder_cache!(PurifiedMirSpecEnc);

    type TaskDescription<'tcx> = (
        DefId, // The function annotated with specs
        bool,  // If to encode as pure or not
    );

    type OutputFullDependency<'vir> = PurifiedMirSpecEncOutput<'vir>;

    type EncodingError = <MirPureEnc as TaskEncoder>::EncodingError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let (def_id, pure) = *task_key;
        let signature = RustSignature::new(def_id);
        let params = GParams::from(def_id);

        deps.emit_output_ref(*task_key, ())?;

        let local_defs = deps
            .require_dep::<crate::encoders::purified_local_def::PurifiedMirLocalDefEnc>(
                PurifiedMirLocalDefEncTask::Local {
                    def_id,
                    all_locals: false,
                },
            )?;
        let specs =
            deps.require_dep::<crate::encoders::SpecEnc>(crate::encoders::SpecEncTask { def_id })?;

        vir::with_vcx(|vcx| {
            let substs = ty::GenericArgs::identity_for_item(vcx.tcx(), def_id);
            let local_iter = (1..=local_defs.arg_count).map(mir::Local::from);
            let all_args: Vec<vir::ExprSnap<'vir>> = if pure {
                let result_ty = local_defs.snap_ty_return();
                local_iter
                    .map(|local| local_defs[local].local_ex)
                    .chain([vcx.mk_result(result_ty)])
                    .collect()
            } else {
                local_iter.map(|local| local_defs[local].local_ex).collect()
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
                        .require_dep::<crate::encoders::MirPureEnc>(
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
                let post_args: Vec<vir::ExprSnap<'vir>> = local_defs
                    .local_decl_args()
                    .zip(signature.inputs.iter())
                    .map(|(decl, ty)| {
                        let suffix = if Self::contains_mut_ref(ty.0, vcx.tcx()) {
                            "_param"
                        } else {
                            "_return"
                        };
                        vcx.mk_local_decl(
                            vir::vir_format_identifier!(vcx, "{}{}", decl.name, suffix).to_str(),
                            decl.ty,
                        )
                        .expr(vcx)
                    })
                    .chain([local_defs.ret().local_ex])
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
                            .require_dep::<crate::encoders::MirPureEnc>(
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
            let pre_pledge_args = vcx
                .alloc_slice(&[pre_args, &[vcx.mk_local_ex(local_defs.ret().local_snap)]].concat());
            let post_pledge_args = vcx.alloc_slice(
                &[post_args, &[vcx.mk_local_ex(local_defs.ret().local_snap)]].concat(),
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
                            deps.require_dep::<crate::encoders::MirPureEnc>(
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
                            .require_dep::<crate::encoders::MirPureEnc>(
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
                            lhs_expr.purified_reify(
                                vcx,
                                (
                                    (lhs_def_id.unwrap(), pre_pledge_args),
                                    (lhs_def_id.unwrap(), post_pledge_args),
                                ),
                            )
                        });
                        let rhs_expr = rhs_expr.purified_reify(
                            vcx,
                            (
                                (*rhs_def_id, pre_pledge_args),
                                (*rhs_def_id, post_pledge_args),
                            ),
                        );
                        let rhs_span = vcx.tcx().def_span(rhs_def_id);
                        EncodedPledge::new(
                            lhs_expr.map(|lhs_expr| {
                                let lhs_span = vcx.tcx().def_span(lhs_def_id.unwrap());
                                PledgeExpiryObligation::new(
                                    vcx.with_span(lhs_span, |_| to_bool(lhs_expr).downcast_ty()),
                                    lhs_span,
                                )
                            }),
                            vcx.with_span(rhs_span, |vcx| {
                                vcx.handle_error("exhale.failed:assertion.false", move |_| {
                                    Some(vec![PrustiError::verification(
                                        "pledge postcondition might not hold",
                                        rhs_span.into(),
                                    )])
                                });
                                to_bool(rhs_expr).downcast_ty()
                            }),
                            rhs_span,
                        )
                    },
                )
                .collect::<Vec<_>>();
            let data = PurifiedMirSpecEncOutput {
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

impl<'vir> PurifiedMirSpecEnc {
    fn contains_mut_ref(ty: ty::Ty<'vir>, tcx: ty::TyCtxt<'vir>) -> bool {
        match ty.kind() {
            ty::TyKind::Ref(_, _, ty::Mutability::Mut) => true,
            ty::TyKind::Adt(adt_def, substs) => adt_def
                .all_fields()
                .any(|f| Self::contains_mut_ref(f.ty(tcx, substs), tcx)),
            ty::TyKind::Tuple(tys) => tys.iter().any(|t| Self::contains_mut_ref(t, tcx)),
            _ => false,
        }
    }
}
