use prusti_interface::PrustiError;
use prusti_rustc_interface::span::def_id::DefId;
use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies};
use vir::{FunctionIdn, Reify};

use crate::encoders::{
    MirLocalDefEnc, MirLocalDefEncTask, MirPureEnc, MirPureEncTask, MirSpecEnc, Pure, PureKind,
    TyUsePureEnc,
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
}

impl<'vir> FunctionCallEncOutput<'vir> {
    /// Calls the definitional function `f_`, used in pure/spec contexts.
    pub fn call_pure<Curr, Next>(
        &self,
        args: Vec<vir::ExprGenSnap<'vir, Curr, Next>>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        self.call_casted(self.function.function_ref, args)
    }

    /// Calls the caller wrapper `cf_`, used when encoding impure assignments.
    pub fn call_impure<Curr, Next>(
        &self,
        args: Vec<vir::ExprGenSnap<'vir, Curr, Next>>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        self.call_casted(self.function.caller_ref, args)
    }

    fn call_casted<Curr, Next>(
        &self,
        function: FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>,
        mut args: Vec<vir::ExprGenSnap<'vir, Curr, Next>>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        assert_eq!(self.inputs.len(), args.len());
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
        let function_ref = if let Some(assoc_enc) = assoc_enc {
            FunctionEncOutputRef {
                caller_ref: assoc_enc.call_stub_pure_caller.unwrap(),
                function_ref: assoc_enc.call_stub_pure_function.unwrap(),
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
            function: function_ref,
            ty_args,
            inputs,
            output,
            arg_tys,
        }))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        FunctionEnc::emit_outputs(program);
    }
}

// Function encoder

struct FunctionEnc;

#[derive(Debug, Clone)]
struct FunctionEncOutputRef<'vir> {
    caller_ref: FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>,
    function_ref: FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>,
}

impl<'vir> OutputRefAny for FunctionEncOutputRef<'vir> {}

#[derive(Debug, Clone, Copy)]
struct FunctionEncOutput<'vir> {
    caller: vir::Function<'vir>,
    function: vir::Function<'vir>,
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
            let caller_ident = vir::vir_format_identifier!(vcx, "cf_{name}");
            let function_ident = vir::vir_format_identifier!(vcx, "f_{name}");
            let arg_types = vcx.alloc_slice(&local_defs.snap_ty_args().collect::<Vec<_>>());
            let return_type = local_defs.snap_ty_return();
            let params = GParams::from(def_id);
            let generics = deps.require_dep::<GenericParamsEnc>(params)?;
            let caller_ref = FunctionIdn::new(
                caller_ident,
                (arg_types, generics.ty_args(), generics.const_args()),
                return_type,
            );
            let function_ref = FunctionIdn::new(
                function_ident,
                (arg_types, generics.ty_args(), generics.const_args()),
                return_type,
            );
            deps.emit_output_ref(def_id, FunctionEncOutputRef {
                caller_ref,
                function_ref,
            })?;

            let is_pure_unstable = crate::encoders::is_function_pure_unstable(
                def_id,
                GArgs::new(params, params.rust_params()),
            );

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
                    do_stability_checks: false,
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
            // things with do_stability_checks on.
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

            if false {
                // because we are precise (i.e. we require stab_read directly to the location being
                // read from) we don't have to worry about transitive capability bs
                // TODO forall l, t :: stab_read(s, l, t) iff (mk_thing(l, t) in reads_ex)

                // TODO is this right? shouldn't we further restrict this set by what the signature implies is
                // readable? Hmmmm
                // Do we want to allow someone to write a specification where the pure-unstable function's result
                // includes locations that the pre-condition might not be strong enough to guarantee readability for?
                // Is it enough to *only* check (stability?)

                // TODO do we need to make sure that the reads-clause is stable? or just that it depends on itself?
                // TODO we could even enforce that frames in general are `pure`, does this buy us anything?
                // TODO I'm skeptical of this, and if you have frames that grow when you call methods on the immutable
                // interface this seems overly strict

                // TODO what is the downside to having pure_unstable reads-clauses?

                // TODO pre-condition contains stable_read for all elements of the reads-clause.

                // TODO we need to encode the reads-clause of the function in such a way that we can
                // ensure that only the locations that are in the reads-clause are read in the spec +
                // that the expression that computes the reads clause doesn't read anything not in the
                // reads-clause.
                //
                // TODO maybe for pure functions we don't assume capabilities for arguments? instead we
                // would just assume stable_read for every element of the reads-clause?

                // TODO generate

                // TODO check that the frame is self-framing
                // TODO check that the frame expression is stable
                // TODO possibly? check that the pre-and postconditions are framed by the reads-set
                // let reads_set_partial = spec.reads.iter().fold(
                //     vcx.mk_set_literal_expr(&[], vir::TYPE_PSNAP),
                //     |acc, (spec_ex, _)| {
                //         let MirSpecExpr { total, partial } = *spec_ex;
                //         vcx.mk_anyset_op_expr(vir::CollectionBinOpKind::Union, acc, partial)
                //             .downcast_ty()
                //     },
                // );

                // // TODO is this right? shouldn't we further restrict this set by what the signature implies is
                // // readable? Hmmmm
                // // Do we want to allow someone to write a specification where the pure-unstable function's result
                // // includes locations that the pre-condition might not be strong enough to guarantee readability for?
                // // Is it enough to *only* check (stability?)

                // // TODO do we need to make sure that the reads-clause is stable? or just that it depends on itself?
                // // TODO we could even enforce that frames in general are `pure`, does this buy us anything?
                // // TODO I'm skeptical of this, and if you have frames that grow when you call methods on the immutable
                // // interface this seems overly strict

                // // TODO what is the downside to having pure_unstable reads-clauses?

                // // TODO check that the frame is self-framing
                // // TODO check that the frame expression is stable
                // // TODO possibly? check that the pre-and postconditions are framed by the reads-set

                // let readable_pre_partial = vir::expr! {
                //     forall l: Ref, t: Type :: { ([im_caps.stable_read_idn](t, im_state_ex, l)) }
                //     ((([im_state.mk_aloc_psnap](l, t)) in ([reads_set_partial])) ==> ([im_caps.stable_read_idn](t, im_state_ex, l))) &&
                //     (([im_caps.stable_read_idn](t, im_state_ex, l)) ==> (([im_state.mk_aloc_psnap](l, t)) in ([reads_set_partial])))
                // };
                // stab_pres.push(readable_pre_partial);
            }

            let posts = spec
                .posts
                .iter()
                .map(|(post, _)| {
                    // use inhale-exhale expression to prevent viper checking that
                    // the function body expression satisfies the postcondition:
                    // that's checked in the method encoding of this function.
                    vcx.mk_inhale_exhale_expr(post.total, vcx.mk_bool::<true>())
                })
                .collect::<Vec<_>>();
            let posts = vcx.alloc_slice(&posts);

            let func_args = local_defs.local_decl_args().collect::<Vec<_>>();
            let wrapped_call_args = func_args
                .iter()
                .map(|arg| vcx.mk_local_ex(arg))
                .collect::<Vec<_>>();
            let wrapped_call = function_ref.call()(
                &wrapped_call_args,
                generics.ty_exprs(),
                generics.const_exprs(),
            );
            let caller = vcx.mk_function(
                caller_ref,
                (&func_args, generics.ty_decls(), generics.const_decls()),
                vcx.alloc_slice(&spec.pre_exprs().collect::<Vec<_>>()),
                posts,
                None,
                Some(wrapped_call),
            );
            let function = vcx.mk_function(
                function_ref,
                (&func_args, generics.ty_decls(), generics.const_decls()),
                &[],
                posts,
                expr.is_none().then_some(&vir::DecreasesGenData::Star),
                expr,
            );
            Ok((FunctionEncOutput { caller, function }, ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors(program) {
            program.add_function(output.caller);
            program.add_function(output.function);
        }
    }
}
