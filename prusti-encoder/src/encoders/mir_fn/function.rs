use prusti_interface::PrustiError;
use prusti_rustc_interface::span::def_id::DefId;
use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, FunctionIdn, Reify};

use crate::encoders::{
    ImCapEnc, ImStateEnc, MirLocalDefEnc, MirLocalDefEncTask, MirPureEnc, MirPureEncTask,
    MirSpecEnc, Pure, PureKind, TyUsePureEnc,
    mir_fn::{CallTaskDescription, RustSignature},
    pure::spec::{MirSpecEncMode, MirSpecEncTask},
    ty::{
        generics::{
            GArgCaster, GArgs, GArgsCastEnc, GArgsTy, GArgsTyEnc, GParams, GenericParamsEnc,
        },
        use_pure::TyUsePure,
    },
};

// Function wrapper

// TODO can we sneak in the pure_unstable function encoding here by adding the state as a
// snapshot argument to the function?

pub struct FunctionCallEnc;

#[derive(Debug, Clone)]
pub struct FunctionCallEncOutput<'vir> {
    function: FunctionEncOutputRef<'vir>,
    ty_args: GArgsTy<'vir>,
    arg_tys: Vec<TyUsePure<'vir>>,
    inputs: Vec<GArgCaster<'vir, Pure>>,
    output: GArgCaster<'vir, Pure>,
    is_pure_unstable: bool,
}

// TODO IM I think there are some more cases that we add.
// 1) you might call a function unchecked to encode trait axioms
// 2) you might call a function with pre-conditions but no stab checks for a method spec
// 3) you might call a function with both pre-conditions and stab check for stab/WD checks
//
//
// is 2) necessary? if we have a pure-partial mode that checks stability/wd, then can we
// do a total encoding for actual verification?
// we might call a function in pure-partial context if we want to check stability

impl<'vir> FunctionCallEncOutput<'vir> {
    /// Calls the definitional function `f_`, used in axioms.
    pub fn call_total<Curr, Next>(
        &self,
        args: Vec<vir::ExprGenSnap<'vir, Curr, Next>>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        self.call_casted(self.function.total_ref, args)
    }

    /// Calls the caller wrapper `cf_`, used when encoding impure assignments.
    pub fn call_partial<Curr, Next>(
        &self,
        args: Vec<vir::ExprGenSnap<'vir, Curr, Next>>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        self.call_casted(self.function.partial_ref, args)
    }

    // TODO in impure contexts we need to call a function that doesn't do stability checks but still checks
    // the pre-condition
    pub fn call_impure<Curr, Next>(
        &self,
        args: Vec<vir::ExprGenSnap<'vir, Curr, Next>>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        self.call_casted(self.function.impure_ref, args)
    }

    fn call_casted<Curr, Next>(
        &self,
        function: FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>,
        mut args: Vec<vir::ExprGenSnap<'vir, Curr, Next>>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        assert_eq!(
            if self.is_pure_unstable {
                self.inputs.len() + 1
            } else {
                self.inputs.len()
            },
            args.len()
        );
        for ((arg, caster), ty) in args
            .iter_mut()
            .zip(self.inputs.iter())
            .zip(self.arg_tys.iter())
        {
            *arg = caster.cast_to_callee_ctx(ty.dummy_ref_address(*arg));
        }
        let call = function.call()(&args, self.ty_args.get_ty(), self.ty_args.get_const());
        self.output.cast_to_caller_ctx(call)
    }

    pub fn is_pure_unstable(&self) -> bool {
        self.is_pure_unstable
    }
}

impl TaskEncoder for FunctionCallEnc {
    task_encoder::encoder_cache!(FunctionCallEnc);
    const ENCODER_NAME: &'static str = "function call encoder";
    type TaskDescription<'tcx> = CallTaskDescription<'tcx>;
    type OutputFullDependency<'vir> = FunctionCallEncOutput<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let (callee_def_id, assoc_enc) = task_key.trait_call(deps)?;
        let total_ref = if let Some(assoc_enc) = assoc_enc {
            FunctionEncOutputRef {
                partial_ref: assoc_enc.call_stub_pure_partial.unwrap(),
                total_ref: assoc_enc.call_stub_pure_total.unwrap(),
                impure_ref: assoc_enc.call_stub_pure_impure.unwrap(),
                frame_ref: assoc_enc.frame_stub,
            }
        } else {
            deps.require_ref::<FunctionEnc>(task_key.callee)?
        };
        let signature = RustSignature::new(callee_def_id);
        let ty_args = deps.require_dep::<GArgsTyEnc>(task_key.gargs)?;
        let inputs = signature
            .inputs
            .iter()
            .map(|ty| {
                let normalized = ty.decompose_compare_normalize(signature.gparams, task_key.gargs);
                deps.require_dep::<GArgsCastEnc<Pure>>(normalized)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let normalized = signature
            .output
            .decompose_compare_normalize(signature.gparams, task_key.gargs);
        let output = deps.require_dep::<GArgsCastEnc<Pure>>(normalized)?;
        let arg_tys = signature
            .inputs
            .iter()
            .map(|ty| {
                let ty_task = ty.decompose_normalize(task_key.gargs);
                deps.require_dep::<TyUsePureEnc>(ty_task)
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(((), FunctionCallEncOutput {
            function: total_ref,
            ty_args,
            inputs,
            output,
            arg_tys,
            is_pure_unstable: crate::encoders::is_function_pure_unstable(
                callee_def_id,
                task_key.gargs,
            ),
        }))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        FunctionEnc::emit_outputs(program);
    }
}

// Function encoder

pub struct FunctionEnc;

#[derive(Debug, Clone)]
pub struct FunctionEncOutputRef<'vir> {
    // (Interior Mutability) pure_unstable functions are encoded to take an extra ImState argument
    partial_ref: FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>,
    total_ref: FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>,
    impure_ref: FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>,
    pub frame_ref:
        Option<FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Set>>,
}

impl<'vir> OutputRefAny for FunctionEncOutputRef<'vir> {}

#[derive(Debug, Clone, Copy)]
pub struct FunctionEncOutput<'vir> {
    functions: &'vir [vir::Function<'vir>],
}

#[derive(Clone, Debug)]
pub enum FunctionEncError {}

impl TaskEncoder for FunctionEnc {
    task_encoder::encoder_cache!(FunctionEnc);
    const ENCODER_NAME: &'static str = "function encoder";
    type TaskDescription<'tcx> = DefId;

    type OutputRef<'vir> = FunctionEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = FunctionEncOutput<'vir>;

    type EncodingError = FunctionEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let def_id = *task_key;
            let local_defs = deps.require_dep::<MirLocalDefEnc>(MirLocalDefEncTask::Local {
                def_id,
                all_locals: true,
            })?;

            tracing::debug!("encoding {def_id:?}");

            let name = vir::ViperIdent::from_def_id(vcx, def_id);
            let partial_ident = vir::vir_format_identifier!(vcx, "partial_f_{name}");
            let total_ident = vir::vir_format_identifier!(vcx, "total_f_{name}");
            let impure_ident = vir::vir_format_identifier!(vcx, "impure_f_{name}");
            let return_type = local_defs.snap_ty_return();
            let params = GParams::from(def_id);
            let generics = deps.require_dep::<GenericParamsEnc>(params)?;

            let is_pure_unstable = crate::encoders::is_function_pure_unstable(
                def_id,
                GArgs::new(params, params.rust_params()),
            );
            let im_state = deps.require_ref::<ImStateEnc>(())?;
            let arg_types = vcx.alloc_slice(
                &local_defs
                    .snap_ty_args()
                    .chain(is_pure_unstable.then(|| vir::TYPE_IMSTATE.upcast_ty()))
                    .collect::<Vec<_>>(),
            );

            let partial_ref = FunctionIdn::new(
                partial_ident,
                (arg_types, generics.ty_args(), generics.const_args()),
                return_type,
            );
            let total_ref = FunctionIdn::new(
                total_ident,
                (arg_types, generics.ty_args(), generics.const_args()),
                return_type,
            );
            let impure_ref = FunctionIdn::new(
                impure_ident,
                (arg_types, generics.ty_args(), generics.const_args()),
                return_type,
            );

            let set_ty = vcx.mk_ty_set(vir::TYPE_PSNAP);
            let frame_ref = is_pure_unstable.then(|| {
                FunctionIdn::new(
                    vir::vir_format_identifier!(vcx, "ff_{name}"),
                    (arg_types, generics.ty_args(), generics.const_args()),
                    set_ty,
                )
            });

            deps.emit_output_ref(def_id, FunctionEncOutputRef {
                partial_ref,
                total_ref,
                impure_ref,
                frame_ref,
            })?;

            let spec = deps.require_dep::<MirSpecEnc>(MirSpecEncTask {
                def_id,
                context_def_id: def_id,
                enc_mode: MirSpecEncMode::PureWithResult,
                is_unstable: is_pure_unstable,
            })?;

            let expr = if !crate::encoders::encodes_body(def_id) {
                None
            } else {
                // Encode the body of the function. If it cannot be encoded (e.g. it
                // uses an unsupported feature), report it and emit the function
                // abstractly (keeping its contract) rather than failing entirely
                // (which would leave a dangling reference for callers).
                match deps.require_dep::<MirPureEnc>(MirPureEncTask {
                    encoding_depth: 0,
                    kind: PureKind::Pure,
                    parent_def_id: def_id,
                    gargs: params.identity_args(),
                    is_partial: false,
                    is_unstable: is_pure_unstable,
                }) {
                    Ok(out) => {
                        let expr = out.expr.reify(
                            vcx,
                            (def_id, spec.pre_args, None, vir::OldLabel::None, None),
                        ); // TODO pass im_state if this is a pure_unstable function
                        assert!(
                            expr.ty() == return_type,
                            "expected {:?}, got {:?}",
                            return_type,
                            expr.ty()
                        );
                        Some(expr)
                    }
                    Err(err) => {
                        let (message, span) = super::dep_error(&err);
                        vcx.emit_early_error(PrustiError::unsupported(
                            format!(
                                "cannot encode function body `{}`: {message}",
                                vcx.tcx().def_path_str(def_id),
                            ),
                            span.unwrap_or_else(|| vcx.tcx().def_span(def_id)).into(),
                        ));
                        None
                    }
                }
            };

            tracing::debug!("finished {def_id:?}");

            // TODO do we need to add a precondition that checks for stability here?
            // and/or have a partial and total version of this. Maybe if we encode
            // things with is_partial on.
            //
            // In the impure stab encoding we should already have checked that the
            // function spec is stable, but we still need to encode the version of
            // this function which we can reason about a call being stable.
            //
            // I guess the way we would do this is by requiring stab_read for all
            // elements of the reads-clause.
            //
            // TODO also note that we DONT want to emit the address-stripping operation
            // at call-sites for these functions

            // TODO encode the framing axiom

            // TODO we need to generate a partial/total version of each pure-unstable function anyhow in order to
            // encode specs. The partial version could check that the pre/post-condition and reads-clause are self-framing
            //

            let mut functions = Vec::new();

            let func_params = local_defs
                .local_decl_args()
                .chain(is_pure_unstable.then(|| im_state.state_decl.upcast_ty()))
                .collect::<Vec<_>>();
            let func_args = func_params
                .iter()
                .map(|arg| vcx.mk_local_ex(arg))
                .collect::<Vec<_>>();
            let mut partial_pres = spec.pre_exprs().collect::<Vec<_>>();
            let mut total_posts = spec
                .posts
                .iter()
                .map(|(post, _)| {
                    // use inhale-exhale expression to prevent viper checking that
                    // the function body expression satisfies the postcondition:
                    // that's checked in the method encoding of this function.
                    vcx.mk_inhale_exhale_expr(post.total, vcx.mk_bool::<true>())
                })
                .collect::<Vec<_>>();
            let wrapped_call =
                total_ref.call()(&func_args, generics.ty_exprs(), generics.const_exprs());

            // TODO OH it's tricky because we might call a pure_unstable function in a
            // situation where it's not necessarily stable.
            // This means that we can't always require the stability-check version of the function for impure contexts
            if is_pure_unstable {
                // Until we have a good way to check the bodies of pure_unstable functions, disallow non-trusted functions
                assert!(expr.is_none());

                // Encode function that calculates this function's frame
                let frame_body = (!spec.reads.pure.is_empty())
                    .then(|| {
                        spec.reads.pure.iter().fold(
                            vcx.mk_set_literal_expr(&[], vir::TYPE_PSNAP),
                            |acc, spec_ex| {
                                vcx.mk_anyset_op_expr(vir::CollectionBinOpKind::Union, acc, spec_ex)
                                    .downcast_ty()
                            },
                        )
                    })
                    .unwrap_or(im_state.top_set_idn.call()());
                functions.push(vcx.mk_function(
                    frame_ref.unwrap(),
                    (&func_params, generics.ty_decls(), generics.const_decls()),
                    &[],
                    &[],
                    None,
                    Some(frame_body),
                ));

                let frame_ex = frame_ref.unwrap().call()(
                    &func_args,
                    generics.ty_exprs(),
                    generics.const_exprs(),
                );
                let im_caps = deps.require_ref::<ImCapEnc>(())?;
                partial_pres.push(vir::expr! {
                    forall t: Type, l: Ref ::
                    { ([im_state.mk_aloc_psnap_idn](t, l)) } // TODO is this the right trigger
                    (([im_state.mk_aloc_psnap_idn](t, l)) in ([frame_ex])) ==> ([im_caps.stable_read_idn](t, ([im_state.state_decl]), l))
                });

                // Encode the function's framing axiom as a post-condition
                let future_decl = vcx.mk_local_decl("s_future", vir::TYPE_IMSTATE);
                let future_args = local_defs
                    .local_decl_args()
                    .chain([future_decl.upcast_ty()])
                    .map(|arg| vcx.mk_local_ex(arg))
                    .collect::<Vec<_>>();
                let future_call =
                    total_ref.call()(&future_args, generics.ty_exprs(), generics.const_exprs());
                total_posts.push(vir::expr! {
                  forall [future_decl] :: { ([future_call]) }
                  (forall t: Type, l: Ref :: { ([im_state.get_snap_idn](t, ([future_decl]), l)) }
                  (([im_state.mk_aloc_psnap_idn](t, l)) in (frame_ex)) ==>
                      (([im_state.get_snap_idn](t, ([im_state.state_decl]), l)) == ([im_state.get_snap_idn](t, ([future_decl]), l)))) ==>
                          (([wrapped_call]) == ([future_call]))
                });
            }

            let posts = vcx.alloc_slice(
                &spec
                    .posts
                    .iter()
                    .map(|(post, _)| {
                        // use inhale-exhale expression to prevent viper checking that
                        // the function body expression satisfies the postcondition:
                        // that's checked in the method encoding of this function.
                        vcx.mk_inhale_exhale_expr(post.total, vcx.mk_bool::<true>())
                    })
                    .collect::<Vec<_>>(),
            );
            let partial_pres = vcx.alloc_slice(&partial_pres);
            functions.push(vcx.mk_function(
                partial_ref,
                (&func_params, generics.ty_decls(), generics.const_decls()),
                partial_pres,
                posts,
                None,
                Some(wrapped_call),
            ));

            let total_posts = vcx.alloc_slice(&total_posts);
            functions.push(vcx.mk_function(
                total_ref,
                (&func_params, generics.ty_decls(), generics.const_decls()),
                &[],
                total_posts,
                expr.is_none().then_some(&vir::DecreasesGenData::Star),
                expr,
            ));

            let pres = vcx.alloc_slice(&spec.pre_exprs().collect::<Vec<_>>());
            functions.push(vcx.mk_function(
                impure_ref,
                (&func_params, generics.ty_decls(), generics.const_decls()),
                pres,
                posts,
                None,
                Some(wrapped_call),
            ));
            Ok((
                FunctionEncOutput {
                    functions: &vcx.alloc(functions)[..],
                },
                (),
            ))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors(program) {
            output
                .functions
                .iter()
                .for_each(|function| program.add_function(function));
        }
    }
}
