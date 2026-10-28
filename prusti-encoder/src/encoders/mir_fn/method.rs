use pcg::borrow_pcg::FunctionData;
use prusti_interface::PrustiError;
use prusti_rustc_interface::{
    middle::{mir, ty},
    span::def_id::DefId,
};
use task_encoder::{
    EncodeFullError, EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies,
};
use vir::{CastType, Function, MethodIdn};

use crate::encoders::{
    ImCapEnc, ImStateEnc, Impure, ImpureEncVisitor, MirLocalDefEnc, MirLocalDefEncTask, MirSpecEnc,
    WandEnc, WandEncTask,
    im_state::ImStateEncRef,
    mir_fn::{CallTaskDescription, FunctionEnc, RustSignature, SpecBlocks, SpecBlocksEnc},
    mir_impure::ImpureImData,
    pure::spec::{MirSpecClause, MirSpecEncMode, MirSpecEncTask, MirSpecExpr},
    ty::generics::{
        GArgCaster, GArgs, GArgsCastEnc, GArgsTy, GArgsTyEnc, GParams, GenericParamsEnc,
    },
};

// Method wrapper

pub struct MethodCallEnc;

#[derive(Debug, Clone)]
pub struct MethodCallEncOutput<'vir> {
    im_state: ImStateEncRef<'vir>,
    method: MethodEncOutputRef<'vir>,
    ty_args: GArgsTy<'vir>,
    inputs: Vec<GArgCaster<'vir, Impure>>,
    output: GArgCaster<'vir, Impure>,
}

impl<'vir> MethodCallEncOutput<'vir> {
    pub fn call(
        &self,
        im_state_ref: vir::ExprRef<'vir>,
        mut args: Vec<vir::ExprRef<'vir>>,
        ret: vir::ExprRef<'vir>,
    ) -> Vec<vir::Stmt<'vir>> {
        assert_eq!(self.inputs.len(), args.len());
        let generics = args.iter().zip(self.inputs.iter());

        let mut stmts: Vec<_> = generics
            .filter_map(|(arg, caster)| caster.cast_to_callee_ctx(arg))
            .collect();

        vir::with_vcx(|vcx| {
            stmts.push(vcx.mk_inhale_stmt(vcx.mk_eq_expr(
                self.im_state.modifies_idn.call()(self.im_state.get_idn.call()(im_state_ref)),
                self.method.footprint_ref.unwrap().caller_ref.call()(
                    im_state_ref,
                    &args,
                    self.ty_args.get_ty(),
                    self.ty_args.get_const(),
                ),
            )));
        });

        args.insert(0, ret);
        let call = (self.method.method_ref)(
            im_state_ref,
            &args,
            self.ty_args.get_ty(),
            self.ty_args.get_const(),
        )
        .alloc();
        stmts.push(call);

        let result = self.output.cast_to_caller_ctx(ret);
        if let Some(result) = result {
            stmts.push(result);
        }
        stmts
    }
}

impl TaskEncoder for MethodCallEnc {
    task_encoder::encoder_cache!(MethodCallEnc);
    type TaskDescription<'tcx> = CallTaskDescription<'tcx>;
    type OutputFullDependency<'vir> = MethodCallEncOutput<'vir>;

    const ENCODER_NAME: &'static str = "method call encoder";

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let (callee_def_id, assoc_enc) = task_key.trait_call(deps)?;
        let method_ref = if let Some(assoc_enc) = assoc_enc {
            MethodEncOutputRef {
                method_ref: assoc_enc.call_stub_impure.unwrap(),
                footprint_ref: assoc_enc.footprint_stub,
            }
        } else {
            deps.require_ref::<MethodEnc>(task_key.callee)?
        };
        let signature = RustSignature::new(callee_def_id);
        let ty_args = deps.require_dep::<GArgsTyEnc>(task_key.gargs)?;
        let inputs = signature
            .inputs
            .iter()
            .map(|ty| {
                let normalized = ty.decompose_compare_normalize(signature.gparams, task_key.gargs);
                deps.require_dep::<GArgsCastEnc<Impure>>(normalized)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let normalized = signature
            .output
            .decompose_compare_normalize(signature.gparams, task_key.gargs);
        let output = deps.require_dep::<GArgsCastEnc<Impure>>(normalized)?;
        let im_state = deps.require_ref::<ImStateEnc>(())?;
        Ok(((), MethodCallEncOutput {
            method: method_ref,
            ty_args,
            inputs,
            output,
            im_state,
        }))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        MethodEnc::emit_outputs(program);
    }
}

// Method encoder

pub(super) struct MethodEnc;

#[derive(Debug, Clone, Copy)]
pub struct MethodEncFootprint<'vir> {
    pub caller_ref:
        vir::FunctionIdn<'vir, (vir::Ref, vir::ManyRef, vir::ManyTyVal, vir::ManyCSnap), vir::Set>,
    pub inner_ref:
        vir::FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Set>,
}

// TODO There should (always?) be a ref-argument for the p_ImState permission
#[derive(Debug, Clone)]
pub(super) struct MethodEncOutputRef<'vir> {
    // (Interior Mutability) the first `Ref` points to the p_ImState permission
    method_ref: MethodIdn<'vir, (vir::Ref, vir::ManyRef, vir::ManyTyVal, vir::ManyCSnap)>,
    // If we are encoding a `pure_unstable` function, the footprint is the empty set. If we are encoding
    // a method with no modifies-clause provided by the user, the footprint is the set of all `s_Param`s.
    footprint_ref: Option<MethodEncFootprint<'vir>>,
}

impl<'vir> OutputRefAny for MethodEncOutputRef<'vir> {}

#[derive(Debug, Clone, Copy)]
pub(super) struct MethodEncOutput<'vir> {
    methods: &'vir [vir::Method<'vir>],
    functions: &'vir [vir::Function<'vir>],
}

#[derive(Clone, Debug)]
pub enum MethodEncError {
    /// The method cannot be encoded; this was reported as an early error.
    Reported,
}

impl TaskEncoder for MethodEnc {
    task_encoder::encoder_cache!(MethodEnc);
    const ENCODER_NAME: &'static str = "method encoder";
    type TaskDescription<'tcx> = DefId;

    type OutputRef<'vir> = MethodEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = MethodEncOutput<'vir>;

    type EncodingError = MethodEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn error_reported(error: &Self::EncodingError) -> bool {
        matches!(error, MethodEncError::Reported)
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let def_id = *task_key;
        vir::with_vcx(|vcx| {
            let span = vcx.tcx().def_span(def_id);
            let trusted = crate::encoders::is_function_trusted(def_id);

            let arg_defs = deps.require_ref_spanned::<MirLocalDefEnc>(
                MirLocalDefEncTask::Local {
                    def_id,
                    all_locals: false,
                },
                span,
            )?;

            let mut methods = Vec::new();
            let mut functions = Vec::new();

            // Argument count for the Viper method:
            // - one (`Ref`) for the return place;
            // - one (`Ref`) for each MIR argument.
            //
            // Note that the return place is modelled as an argument of the
            // Viper method. This corresponds to an execution model where the
            // method can return data to the caller without a copy--it directly
            // modifies a place provided by the caller.
            //
            // TODO IM check if ^^^ messes with our `shallow` annotations
            //
            // TODO: type parameters: for generic methods we will want to pass
            //   values of type `Type` as well`
            let arg_count = arg_defs.arg_count + 1;

            // Create the identifier and use it as an output ref. This is what
            // is used when other methods call this one.
            let method_name =
                vir::vir_format_identifier!(vcx, "m_{}", vir::ViperIdent::from_def_id(vcx, def_id));
            let ref_args = vcx.alloc_slice(&vec![vir::TYPE_REF; arg_count]);
            let params = GParams::from(def_id);
            let generics = deps.require_dep_spanned::<GenericParamsEnc>(params, span)?;
            let method_ref = MethodIdn::new(
                method_name,
                (
                    vir::TYPE_REF,
                    ref_args,
                    generics.ty_args(),
                    generics.const_args(),
                ),
            );

            enum ProcKind {
                Method,
                Pure,
                PureUnstable,
            }

            let item_params = GParams::from(def_id);
            let gargs = GArgs::new(item_params, item_params.rust_params());
            let proc_kind = if crate::encoders::is_function_pure_unstable(def_id, gargs) {
                ProcKind::PureUnstable
            } else if crate::encoders::is_function_pure(def_id, gargs) {
                ProcKind::Pure
            } else {
                ProcKind::Method
            };

            let local_defs = deps.require_dep_spanned::<MirLocalDefEnc>(
                MirLocalDefEncTask::Local {
                    def_id,
                    all_locals: false,
                },
                span,
            )?;
            let set_ty = vcx.mk_ty_set(vir::TYPE_PSNAP);
            let footprint_ref = matches!(proc_kind, ProcKind::Method).then(|| {
                let arg_types = local_defs
                    .snap_ty_args()
                    .chain([vir::TYPE_IMSTATE.upcast_ty()])
                    .collect::<Vec<_>>();
                MethodEncFootprint {
                    caller_ref: vir::FunctionIdn::new(
                        vir::vir_format_identifier!(
                            vcx,
                            "footprint_caller_{}",
                            vir::ViperIdent::from_def_id(vcx, def_id)
                        ),
                        (
                            vir::TYPE_REF,
                            vcx.alloc_slice(&vec![vir::TYPE_REF; local_defs.arg_count]),
                            generics.ty_args(),
                            generics.const_args(),
                        ),
                        set_ty,
                    ),
                    inner_ref: vir::FunctionIdn::new(
                        vir::vir_format_identifier!(
                            vcx,
                            "footprint_inner_{}",
                            vir::ViperIdent::from_def_id(vcx, def_id)
                        ),
                        (
                            vcx.alloc_slice(&arg_types),
                            generics.ty_args(),
                            generics.const_args(),
                        ),
                        set_ty,
                    ),
                }
            });

            // TODO generate a function idn for the frame
            deps.emit_output_ref(def_id, MethodEncOutputRef {
                method_ref,
                footprint_ref,
            })?;

            // Method contract. We will need to emit pre- and postconditions for
            // the permissions, the functional spec, and (in the postcondition)
            // wands in case of a reborrowing function.
            let mut pres = Vec::new();
            let mut cap_pres = Vec::new();
            let mut posts = Vec::new();
            let mut cap_posts = Vec::new();
            let spec = deps.require_dep_spanned::<MirSpecEnc>(
                MirSpecEncTask {
                    def_id,
                    context_def_id: def_id,
                    enc_mode: MirSpecEncMode::Impure,
                    is_unstable: true,
                },
                span,
            )?;
            let function_data = FunctionData::new(def_id);
            let wands = deps
                .require_dep_spanned::<WandEnc>(
                    WandEncTask {
                        data: function_data,
                    },
                    span,
                )
                .map_err(|err| {
                    // Without its wands, the method has no contract.
                    let (message, _) = super::dep_error(&err);
                    vcx.emit_early_error(PrustiError::unsupported(
                        format!(
                            "cannot encode method `{}`: {message}",
                            vcx.tcx().def_path_str(def_id),
                        ),
                        vcx.tcx().def_span(def_id).into(),
                    ));
                    EncodeFullError::EncodingError(MethodEncError::Reported, None)
                })?;

            let im_state = deps.require_ref::<ImStateEnc>(())?;
            let im_caps = deps.require_ref::<ImCapEnc>(())?;
            let im_state_ref = vcx.mk_local_ex(im_state.state_ref_decl);
            let im_state_owned = vcx.mk_predicate_app_expr((im_state.pred_idn)(im_state_ref)(None));
            pres.push(im_state_owned);
            posts.push(im_state_owned);

            // Add direct resources for inputs and outputs to the pre- and
            // postconditions, respectively. "Direct" here refers to owned
            // Viper resources that must be passed in/out given the signature,
            // without going through any dereferences.
            let mut args = Vec::with_capacity(arg_count + params.count());
            for arg_idx in (0..arg_count).map(mir::Local::from) {
                let name_p = local_defs[arg_idx].local.name;
                args.push(vir::vir_local_decl! { vcx; [name_p] : Ref });
                if arg_idx != mir::RETURN_PLACE {
                    pres.push(local_defs[arg_idx].impure_pred);
                    if matches!(proc_kind, ProcKind::Method | ProcKind::PureUnstable) {
                        cap_pres.push(local_defs[arg_idx].impure_cap)
                    }
                    pres.push(vcx.mk_eq_expr(
                        local_defs[arg_idx].spec_snap,
                        local_defs[arg_idx].im_state_snap,
                    ));
                }
            }
            posts.push(local_defs[mir::RETURN_PLACE].impure_pred);
            posts.push(vcx.mk_eq_expr(
                local_defs[mir::RETURN_PLACE].spec_snap,
                local_defs[mir::RETURN_PLACE].im_state_snap,
            ));

            // ..
            pres.extend(wands.indirect_pres(vcx, &local_defs, deps));
            posts.extend(wands.indirect_posts(vcx, &local_defs, deps));
            posts.extend(wands.wand_posts(vcx, &local_defs, deps));
            if matches!(proc_kind, ProcKind::Method | ProcKind::PureUnstable) {
                cap_posts.push(local_defs[mir::RETURN_PLACE].impure_cap);
                cap_posts.extend(wands.indirect_cap_posts(vcx, &local_defs, deps));
                // TODO for each of the shared referenes held across the call, cap_posts
                // should include the fact that the snapshot at that address remains the same
            }

            // TODO for reads-clauses can we assume that all pure_unstable functions
            // are trusted? Ah but wouldn't we like to check the well-definedness of function
            // pres?
            //
            // For (pure-unstable) functions, the modifiable set should be the reads-clause set?
            // and the modifies-set is empty.

            // TODO we could assume/assert here that modifies & reads are never both non-empty

            let curr_im_state = im_state.get_idn.call()(vcx.mk_local_ex(im_state.state_ref_decl));
            let modifies_ex = im_state.modifies_idn.call()(curr_im_state);
            let modifiable_ex = im_state.modifiable_idn.call()(curr_im_state);

            let pure_args = vcx.alloc_slice(
                &local_defs
                    .args()
                    .map(|arg| arg.impure_snap)
                    .chain([curr_im_state.upcast_ty()])
                    .collect::<Vec<_>>(),
            );

            let mut wd_pres = pres.clone();
            wd_pres.append(&mut cap_pres);
            let mut wd_posts = posts.clone();
            wd_posts.append(&mut cap_posts);

            // WD/stability checks are always in a state where no location is modified
            let none_modifies_ex =
                vcx.mk_eq_expr(modifies_ex, vcx.mk_set_literal_expr(&[], vir::TYPE_PSNAP));
            wd_pres.push(none_modifies_ex);
            wd_posts.push(none_modifies_ex);

            let mut extra_pre_checks = Vec::new();
            let mut extra_post_checks = Vec::new();

            match proc_kind {
                ProcKind::PureUnstable => {
                    assert!(spec.modifies.is_empty());
                    // When encoding a pure-unstable function, we need to check the following:
                    // - the reads-clause is well-defined (+ all reads are safe)
                    // - the reads-clause is self-framing
                    // - the pre/post-conditions are well-defined (+ all reads are safe)
                    // - everything read in the pre/post-conditions is framed by the reads-clause
                    // - no panics in the function body
                    // - everything read in the body is safe to read (that is, if we check pure-unstable function bodies)
                    // - everything read in the body is framed by the reads-clause

                    // TODO to encode/check capability annotation conditions, we need to be able to
                    // generate the methods to do the relevant checks while supplying a frame that is
                    // computed from the body
                    //
                    // there are a few ways I imagine we could do this.
                    //
                    // 1) add a special annotation on pure-unstable functions that tells the verifier to
                    // compute the frame of a function from its body and label stability conditions with this
                    //
                    // 2) force manual annotation of frames for stability conditions/force the stability condition
                    //    to be a pure-unstable function rather than an arbitrary expression
                    //
                    // 3) do some kind of ad-hoc check for stability conditions
                    //
                    // TODO each pure-unstable function should have a check in its precondition that succeeds only if the
                    // footprint computed from the function body (if there is one) is a subset of the result of calling
                    // the reads-clause computing function
                    // NOTE computing the footprint would be done by the function encoder?

                    // TODO IM if time permits, it would be good to simplify this encoding:
                    // - the well-definedness

                    // NEW STRATEGY

                    // TODO make sure that the reads-clause gets an impure encoding to check it is well-defined? (doesn't work unless
                    // we manually add pre-conditions)
                    //
                    // Add a pre-condition that checks that the frame is a superset of the frame calculated for the clause &
                    // handle the post-condition with an error message that states that the reads-clause is not self-framing
                    // Ensures that the reads-clause is well-defined and self-framing

                    // TODO compute the frame of the

                    // Add trivial preconditions that check well-definedness of the reads-clause
                    for (
                        MirSpecClause {
                            pure,
                            impure,
                            frame,
                        },
                        span,
                    ) in spec.reads.iter()
                    {
                        let span = *span;
                        wd_pres.push(vcx.mk_eq_expr(impure, impure))
                    }

                    let function_enc = deps.require_ref::<FunctionEnc>(def_id)?;
                    let reads_total = function_enc.frame_ref.unwrap().call()(
                        pure_args,
                        generics.ty_exprs(),
                        generics.const_exprs(),
                    );

                    // Add self-framing checks
                    for (
                        MirSpecExpr {
                            total,
                            partial,
                            frame,
                        },
                        span,
                    ) in spec.pres.iter()
                    {
                        let span = *span;
                        vcx.with_span(span, |vcx| {
                            vcx.handle_error("exhale.failed:assertion.false", move |_| {
                                Some(vec![PrustiError::verification(
                                    "pre-condition might not be framed by reads-clause",
                                    span.into(),
                                )])
                            });
                            extra_pre_checks.push(
                                vcx.mk_exhale_stmt(vcx.mk_set_subset_expr(frame, reads_total)),
                            )
                        });
                    }
                    for (
                        MirSpecClause {
                            pure,
                            impure,
                            frame,
                        },
                        span,
                    ) in spec.reads.iter()
                    {
                        let span = *span;
                        vcx.with_span(span, |vcx| {
                            vcx.handle_error("exhale.failed:assertion.false", move |_| {
                                Some(vec![PrustiError::verification(
                                    "reads-clause might not be self-framing",
                                    span.into(),
                                )])
                            });
                            extra_pre_checks.push(
                                vcx.mk_exhale_stmt(vcx.mk_set_subset_expr(frame, reads_total)),
                            )
                        });
                    }
                    for (
                        MirSpecExpr {
                            total,
                            partial,
                            frame,
                        },
                        span,
                    ) in spec.posts.iter()
                    {
                        let span = *span;
                        vcx.with_span(span, |vcx| {
                            vcx.handle_error("exhale.failed:assertion.false", move |_| {
                                Some(vec![PrustiError::verification(
                                    "post-condition might not be framed by reads-clause",
                                    span.into(),
                                )])
                            });
                            extra_post_checks.push(vcx.mk_exhale_stmt(
                                vcx.mk_set_subset_expr(frame, vcx.mk_old_expr(reads_total)),
                            ))
                        });
                    }
                }
                ProcKind::Method => {
                    assert!(spec.reads.is_empty());

                    let modifies_set_partial = (!spec.modifies.is_empty())
                        .then(|| {
                            spec.modifies.iter().fold(
                                vcx.mk_set_literal_expr(&[], vir::TYPE_PSNAP),
                                |acc, (clause, _)| {
                                    vcx.mk_anyset_op_expr(
                                        vir::CollectionBinOpKind::Union,
                                        acc,
                                        clause.impure,
                                    )
                                    .downcast_ty()
                                },
                            )
                        })
                        .unwrap_or(im_state.top_set_idn.call()());

                    // Contract well-definedness is checked assuming that the set of modifiable locations is
                    // a superset of the modifies-clause.
                    let modifiable_pre_partial =
                        vcx.mk_set_subset_expr(modifies_set_partial, modifiable_ex);
                    wd_pres.push(modifiable_pre_partial);

                    // The caller method's precondition requires the the modifies-clause to be a subset of the current
                    // set of modifiable locations, but the body is checked assuming that the modifiable locations
                    // are *exactly* the modifies-clause.
                    let modifies_set_total = footprint_ref.unwrap().inner_ref.call()(
                        pure_args,
                        generics.ty_exprs(),
                        generics.const_exprs(),
                    );

                    let modifiable_pre_total = vcx.mk_inhale_exhale_expr(
                        vcx.mk_eq_expr(modifies_set_total, modifiable_ex),
                        vcx.mk_set_subset_expr(modifies_set_total, modifiable_ex),
                    );
                    pres.push(modifiable_pre_total);

                    let modifies_set_pure = (!spec.modifies.is_empty())
                        .then(|| {
                            spec.modifies.iter().fold(
                                vcx.mk_set_literal_expr(&[], vir::TYPE_PSNAP),
                                |acc, (clause, _)| {
                                    vcx.mk_anyset_op_expr(
                                        vir::CollectionBinOpKind::Union,
                                        acc,
                                        clause.pure,
                                    )
                                    .downcast_ty()
                                },
                            )
                        })
                        .unwrap_or(im_state.top_set_idn.call()());

                    let footprint_inner_params = (1..=local_defs.arg_count)
                        .map(mir::Local::from)
                        .map(|local| local_defs[local].local_snap)
                        .chain([im_state.state_decl.upcast_ty()])
                        .collect::<Vec<_>>();

                    functions.push(vcx.mk_function(
                        footprint_ref.unwrap().inner_ref,
                        (
                            &footprint_inner_params,
                            generics.ty_decls(),
                            generics.const_decls(),
                        ),
                        &[],
                        &[],
                        None,
                        Some(modifies_set_pure),
                    ));

                    let footprint_caller_params = (1..=local_defs.arg_count)
                        .map(mir::Local::from)
                        .map(|local| {
                            let name_p = local_defs[local].local.name;
                            vir::vir_local_decl! { vcx; [name_p] : Ref }
                        })
                        .collect::<Vec<_>>();

                    let footprint_inner_args = (1..=local_defs.arg_count)
                        .map(mir::Local::from)
                        .map(|local| local_defs[local].impure_snap)
                        .collect::<Vec<_>>();

                    functions.push(
                        vcx.mk_function(
                            footprint_ref.unwrap().caller_ref,
                            (
                                im_state.state_ref_decl,
                                &footprint_caller_params,
                                generics.ty_decls(),
                                generics.const_decls(),
                            ),
                            vcx.alloc_slice(
                                &(1..=local_defs.arg_count)
                                    .map(mir::Local::from)
                                    .map(|local| local_defs[local].impure_pred)
                                    .chain([vcx.mk_predicate_app_expr((im_state.pred_idn)(
                                        vcx.mk_local_ex(im_state.state_ref_decl),
                                    )(
                                        None
                                    ))])
                                    .collect::<Vec<_>>(),
                            ),
                            &[],
                            None,
                            Some(modifies_set_total),
                        ),
                    );
                }
                ProcKind::Pure => {
                    assert!(spec.modifies.is_empty() && spec.reads.is_empty());
                }
            }

            // NOTE: be careful about the order in which we add pre/post-conditions.

            // TODO the new design for stability checks should be:
            // check well-definedness in a single state (read-capability required for read locations)
            // THEN assuming that the condition holds, check stability by either
            // 1) checking for stable_read/read for all elements of the frame or
            // 2) given a state in which the condition holds, havoc and check that the condition holds post-havoc.
            //
            // i.e. the stability condition for assertions is that they are stable WHEN TRUE
            // we go with option 1 because it means that the semantics of assertions match the semantics of runtime
            // code.

            // TODO we need:
            //
            // the frame of the pre/post condition
            // a 'partial/wd' version of each where functions check their preconditions (but not stability)
            // and .to_ref() checks for the right capability

            // I guess the question is whether it should be well-defined to produce a spec-mode shared reference
            // using read-capability alone

            // Extend stab pres/posts with the partial pre/post-conditions
            wd_pres.extend(spec.pres.iter().map(|(cond, _)| cond.partial));
            wd_posts.extend(spec.posts.iter().map(|(cond, _)| cond.partial));

            // TODO for both pres and posts, first inhale wd_pres/posts to check well_definedness and then
            // ask if every location in their frames are stable_read

            // TODO IM if time permits, should we enforce that the frame of the pres/posts
            // is a subset of the set calculated by the reads-clause?

            let mut wd_pre_stmts = Vec::new();
            for (
                MirSpecExpr {
                    total,
                    partial,
                    frame,
                },
                span,
            ) in spec.pres.iter()
            {
                let span = *span;
                vcx.with_span(span, |vcx| {
                    vcx.handle_error("exhale.failed:assertion.false", move |_| {
                        Some(vec![PrustiError::verification(
                            "pre-condition might not be stable",
                            span.into(),
                        )])
                    });
                    let addr_decl = vcx.mk_local_decl("l", vir::TYPE_REF);
                    let addr_ex = vcx.mk_local_ex(addr_decl);
                    let type_decl = vcx.mk_local_decl("t", vir::TYPE_TYVAL);
                    let type_ex = vcx.mk_local_ex(type_decl);
                    let aloc_ex = im_state.mk_aloc_psnap_idn.call()(type_ex, addr_ex);
                    wd_pre_stmts.push(
                        vcx.mk_exhale_stmt(
                            vcx.mk_forall_expr(
                                vcx.alloc_slice(&[addr_decl.as_dyn(), type_decl.as_dyn()]),
                                &[],
                                vcx.mk_bin_op_expr(
                                    vir::BinOpKind::Implies,
                                    vcx.mk_set_in_expr(aloc_ex, frame),
                                    im_caps.stable_read_idn.call()(type_ex, curr_im_state, addr_ex),
                                )
                                .downcast_ty(),
                            ),
                        ),
                    );
                });
            }

            wd_pre_stmts.append(&mut extra_pre_checks);
            // HACK: we exhale the pre-conditions in reverse order to clear our state so we can check
            // the post-condition
            for wd_pre in wd_pres.iter().rev() {
                wd_pre_stmts.push(vcx.mk_exhale_stmt(wd_pre))
            }

            let wd_pre_block = vcx.mk_cfg_block(
                &vir::CfgBlockLabelData::Start,
                &[],
                vcx.alloc_slice(&wd_pre_stmts),
                vcx.mk_goto_stmt(&vir::CfgBlockLabelData::End),
            );

            let mut wd_post_stmts = Vec::new();
            for post in wd_posts {
                wd_post_stmts.push(vcx.mk_inhale_stmt(post));
            }
            for (
                MirSpecExpr {
                    total,
                    partial,
                    frame,
                },
                span,
            ) in spec.posts.iter()
            {
                let span = *span;
                vcx.with_span(span, |vcx| {
                    vcx.handle_error("exhale.failed:assertion.false", move |_| {
                        Some(vec![PrustiError::verification(
                            "post-condition might not be stable",
                            span.into(),
                        )])
                    });
                    let addr_decl = vcx.mk_local_decl("l", vir::TYPE_REF);
                    let addr_ex = vcx.mk_local_ex(addr_decl);
                    let type_decl = vcx.mk_local_decl("t", vir::TYPE_TYVAL);
                    let type_ex = vcx.mk_local_ex(type_decl);
                    let aloc_ex = im_state.mk_aloc_psnap_idn.call()(type_ex, addr_ex);
                    wd_post_stmts.push(
                        vcx.mk_exhale_stmt(
                            vcx.mk_forall_expr(
                                vcx.alloc_slice(&[addr_decl.as_dyn(), type_decl.as_dyn()]),
                                &[],
                                vcx.mk_bin_op_expr(
                                    vir::BinOpKind::Implies,
                                    vcx.mk_set_in_expr(aloc_ex, frame),
                                    im_caps.stable_read_idn.call()(type_ex, curr_im_state, addr_ex),
                                )
                                .downcast_ty(),
                            ),
                        ),
                    );
                });
            }
            wd_post_stmts.append(&mut extra_post_checks);

            let wd_post_block = vcx.mk_cfg_block(
                &vir::CfgBlockLabelData::End,
                &[],
                vcx.alloc_slice(&wd_post_stmts),
                vcx.mk_assume_false_stmt(),
            );

            let wd_method_name = vir::vir_format_identifier!(
                vcx,
                "m_contract_wd_{}",
                vir::ViperIdent::from_def_id(vcx, def_id)
            );
            let wd_method_ref: MethodIdn<
                'vir,
                (vir::Ref, vir::ManyRef, vir::ManyTyVal, vir::ManyCSnap),
            > = MethodIdn::new(
                wd_method_name,
                (
                    vir::TYPE_REF,
                    ref_args,
                    generics.ty_args(),
                    generics.const_args(),
                ),
            );
            methods.push(vcx.mk_method(
                wd_method_ref,
                (
                    im_state.state_ref_decl,
                    &args,
                    generics.ty_decls(),
                    generics.const_decls(),
                ),
                &[],
                vcx.alloc_slice(&wd_pres),
                &[],
                Some(vcx.alloc_slice(&[wd_pre_block, wd_post_block])),
            ));

            // Trusted functions, call stubs, external functions and trait
            // functions without a default implementation have no body to
            // encode; only their contract is emitted.
            let blocks = if let Some(body_with_facts) =
                crate::encoders::impure_body_with_facts(def_id)
            {
                let body = &body_with_facts.body;
                let local_defs = deps.require_dep_spanned::<MirLocalDefEnc>(
                    MirLocalDefEncTask::Local {
                        def_id,
                        all_locals: true,
                    },
                    span,
                )?;

                let pcg_creator = pcg::PcgCtxtCreator::new(vcx.tcx());
                let pcg_ctxt = pcg_creator.new_nll_ctxt(&body_with_facts);
                let fpcs_analysis = pcg::run_pcg(pcg_ctxt);
                pcg_ctxt.update_debug_visualization_metadata();

                let block_count = body.basic_blocks.len();

                let mut encoded_blocks = Vec::with_capacity(
                    // extra blocks: Start, End
                    2 + block_count,
                );
                let mut start_stmts = Vec::new();
                for local in (arg_count..body.local_decls.len()).map(mir::Local::from) {
                    // Spec-only locals have no definition.
                    let Some(local_def) = local_defs.get(local) else {
                        continue;
                    };
                    let name_p = local_def.local.name;
                    start_stmts.push(
                        vcx.mk_local_decl_stmt(vir::vir_local_decl! { vcx; [name_p] : Ref }, None),
                    );
                    start_stmts.push(vcx.mk_inhale_stmt(local_defs[local].impure_cap));
                }

                let im_data = {
                    let prev_im_state_decl = vir::vir_local_decl! { vcx; prev_im_st : ImState };
                    start_stmts.push(vcx.mk_local_decl_stmt(prev_im_state_decl, None));
                    let prev_im_state = vcx.mk_local_ex(prev_im_state_decl);
                    ImpureImData {
                        im_state_ref,
                        curr_im_state,
                        prev_im_state,
                    }
                };

                // This will be overwritten later.
                encoded_blocks.push(vcx.mk_cfg_block(
                    &vir::CfgBlockLabelData::Start,
                    &[],
                    &[],
                    vcx.mk_goto_stmt(&vir::CfgBlockLabelData::BasicBlock(0)),
                ));

                let spec_blocks = SpecBlocks::new(
                    deps.require_dep::<SpecBlocksEnc>(def_id)?,
                    body,
                    fpcs_analysis.analysis().loop_analysis(),
                );

                deps.check_cycle()?;
                let mut visitor = ImpureEncVisitor {
                    vcx,
                    deps,
                    def_id,
                    local_decls: &body.local_decls,
                    fpcs_analysis,
                    local_defs,
                    spec_blocks,
                    body,

                    wands,

                    abstract_ptrs: Default::default(),

                    tmp_ctr: 0,
                    label_ctr: 0,
                    call_labels: Default::default(),
                    wandless_calls: Default::default(),
                    from_to_vars: Default::default(),

                    current_block: None,
                    current_block_pres: None,
                    current_block_succs: None,
                    current_block_label: None,
                    current_fpcs: None,

                    current_stmts: None,
                    current_terminator: None,
                    encoded_blocks,

                    im_mode: true, // TODO pull this from elsewhere
                    im_data,

                    cached_tyvals: Default::default(),
                    tyval_decls: Default::default(),
                };
                // if we encountered an error/cycle during encoding, we don't
                // emit a method body; encoding errors additionally surface as
                // early errors rather than silently degrading to a stub
                match visitor.visit_body(body) {
                    Ok(()) => {
                        start_stmts.extend(
                            visitor
                                .from_to_vars
                                .decls()
                                .map(|v| vcx.mk_local_decl_stmt(v, Some(vcx.mk_bool::<false>()))),
                        );
                        start_stmts.extend(visitor.tyval_decls);
                        visitor.encoded_blocks[0] = vcx.mk_cfg_block(
                            &vir::CfgBlockLabelData::Start,
                            &[],
                            vcx.alloc_slice(&start_stmts),
                            vcx.mk_goto_stmt(&vir::CfgBlockLabelData::BasicBlock(0)),
                        );

                        visitor.encoded_blocks.push(vcx.mk_cfg_block(
                            vcx.alloc(vir::CfgBlockLabelData::End),
                            &[],
                            &[],
                            vcx.alloc(vir::TerminatorStmtData::Exit),
                        ));

                        visitor.deps.check_cycle()?;

                        Some(visitor.encoded_blocks)
                    }
                    Err(EncodeFullError::AlreadyEncoded) => None,
                    Err(err) => {
                        let (message, span) = super::dep_error(&err);
                        vcx.emit_early_error(PrustiError::unsupported(
                            format!(
                                "cannot encode method body `{}`: {message}",
                                vcx.tcx().def_path_str(def_id),
                            ),
                            span.unwrap_or_else(|| vcx.tcx().def_span(def_id)).into(),
                        ));
                        None
                    }
                }
            } else {
                None
            };

            // Add functional specification as the last pre- and postconditions.
            pres.extend(spec.pres.iter().map(|(cond, _)| cond.total));
            posts.extend(spec.posts.iter().map(|(cond, _)| cond.total));

            methods.push(vcx.mk_method(
                method_ref,
                (
                    im_state.state_ref_decl,
                    &args,
                    generics.ty_decls(),
                    generics.const_decls(),
                ),
                &[],
                vcx.alloc_slice(&pres),
                vcx.alloc_slice(&posts),
                blocks.map(|blocks| vcx.alloc_slice(&blocks)),
            ));
            Ok((
                MethodEncOutput {
                    methods: &vcx.alloc(methods)[..],
                    functions: &vcx.alloc(functions)[..],
                },
                (),
            ))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors(program) {
            output
                .methods
                .iter()
                .for_each(|method| program.add_method(method));
            output
                .functions
                .iter()
                .for_each(|function| program.add_function(function));
        }
    }
}

// fn has_interior_mutability<'tcx>(tcx: ty::TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
//     struct InteriorMutabilityTyVisitor<'tcx>(ty::TyCtxt<'tcx>, HashSet<ty::Ty<'tcx>>);

//     impl<'tcx> ty::TypeVisitor<ty::TyCtxt<'tcx>> for InteriorMutabilityTyVisitor<'tcx> {
//         type Result = std::ops::ControlFlow<()>;

//         fn visit_ty(&mut self, t: ty::Ty<'tcx>) -> Self::Result {
//             println!("checking {t:?}");
//             match t.kind() {
//                 ty::TyKind::RawPtr(..) => std::ops::ControlFlow::Break(()),
//                 ty::TyKind::Adt(adt_def, _) if adt_def.is_unsafe_cell() => {
//                     std::ops::ControlFlow::Break(())
//                 }
//                 ty::TyKind::Adt(adt_def, args)
//                     if !self.1.contains(&t)
//                         && adt_def.all_fields().any(|f| {
//                             let t = f.ty(self.0, args);
//                             ty::TypeVisitable::visit_with(&t, self).is_break()
//                         }) =>
//                 {
//                     std::ops::ControlFlow::Break(())
//                 }
//                 _ => {
//                     self.1.insert(t);
//                     ty::TypeSuperVisitable::super_visit_with(&t, self)
//                 }
//             }
//         }
//     }

//     let visited = HashSet::new();
//     let cf = ty::TypeVisitable::visit_with(&ty, &mut InteriorMutabilityTyVisitor(tcx, visited));
//     cf.is_break()
// }
