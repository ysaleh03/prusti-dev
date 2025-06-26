use prusti_rustc_interface::{
    index::IndexVec,
    middle::{mir, ty},
    span::def_id::DefId,
};

use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};

use crate::{
    encoders::{
        rust_ty_predicates::{RustTyPredicatesEnc, RustTyPredicatesEncOutputRef},
        PredicateEncOutputRef,
    },
    trait_support::is_function_with_body,
};

pub struct PurifiedLocalDefEnc;
#[derive(Clone, Copy)]
pub struct PurifiedLocalDefEncOutput<'vir> {
    pub locals: &'vir IndexVec<mir::Local, PurifiedLocalDef<'vir>>,
    pub arg_count: usize,
}
pub type PurifiedLocalDefEncError = ();

#[derive(Clone, Copy)]
pub struct PurifiedLocalDef<'vir> {
    pub local: vir::Local<'vir>,
    pub local_ex: vir::Expr<'vir>,
    pub ty: &'vir PredicateEncOutputRef<'vir>,
}

impl TaskEncoder for PurifiedLocalDefEnc {
    task_encoder::encoder_cache!(PurifiedLocalDefEnc);

    type TaskDescription<'vir> = (
        DefId,                    // ID of the function
        ty::GenericArgsRef<'vir>, // ? this should be the "signature", after applying the env/substs
        Option<DefId>,            // ID of the caller function, if any
    );

    type OutputFullLocal<'vir> = PurifiedLocalDefEncOutput<'vir>;

    type EncodingError = PurifiedLocalDefEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let (def_id, substs, caller_def_id) = *task_key;
        deps.emit_output_ref(*task_key, ())?;

        fn mk_local_def<'vir>(
            vcx: &'vir vir::VirCtxt<'vir>,
            name: &'vir str,
            ty: RustTyPredicatesEncOutputRef<'vir>,
        ) -> PurifiedLocalDef<'vir> {
            let local = vcx.mk_local(name, ty.snapshot());
            let local_ex = vcx.mk_local_ex_local(local);
            PurifiedLocalDef {
                local,
                local_ex,
                ty: vcx.alloc(ty.generic_predicate),
            }
        }

        let trusted = crate::encoders::spec::is_function_trusted(def_id, substs);
        vir::with_vcx(|vcx| {
            let data = if !trusted
                && let Some(local_def_id) = def_id.as_local()
                && is_function_with_body(vcx.tcx(), def_id)
            {
                let body = vcx
                    .body_mut()
                    .get_impure_fn_body(local_def_id, substs, caller_def_id);
                let locals = IndexVec::from_fn_n(
                    |arg: mir::Local| {
                        let local = vir::vir_format!(vcx, "_{}s", arg.index());
                        let ty = deps
                            .require_ref::<RustTyPredicatesEnc>(body.local_decls[arg].ty)
                            .unwrap();
                        mk_local_def(vcx, local, ty)
                    },
                    body.local_decls.len(),
                );
                PurifiedLocalDefEncOutput {
                    locals: vcx.alloc(locals),
                    arg_count: body.arg_count,
                }
            } else {
                let typing_env =
                    ty::TypingEnv::post_analysis(vcx.tcx(), caller_def_id.unwrap_or(def_id));
                let sig = vcx.tcx().instantiate_and_normalize_erasing_regions(
                    substs,
                    typing_env,
                    vcx.tcx().fn_sig(def_id),
                );
                let sig = sig.skip_binder();

                let locals = IndexVec::from_fn_n(
                    |arg: mir::Local| {
                        let local = vir::vir_format!(vcx, "_{}s", arg.index());
                        let ty = if arg.index() == 0 {
                            sig.output()
                        } else {
                            sig.inputs()[arg.index() - 1]
                        };
                        let ty = deps.require_ref::<RustTyPredicatesEnc>(ty).unwrap();
                        mk_local_def(vcx, local, ty)
                    },
                    sig.inputs_and_output.len(),
                );

                PurifiedLocalDefEncOutput {
                    locals: vcx.alloc(locals),
                    arg_count: sig.inputs().len(),
                }
            };
            Ok((data, ()))
        })
    }
}
