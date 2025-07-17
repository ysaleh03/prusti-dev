use prusti_rustc_interface::{middle::ty::GenericArgs, span::def_id::DefId};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};

/// Encodes a Rust function as a Viper method using the monomorphic encoding of generics.
pub struct MirMonoPurifiedEnc;

use crate::{
    encoder_traits::{
        function_enc::FunctionEnc,
        purified_function_enc::{
            PurifiedFunctionEnc, PurifiedFunctionEncError, PurifiedFunctionEncOutput,
            PurifiedFunctionEncOutputRef,
        },
    },
    encoders::FunctionCallTaskDescription,
};

impl FunctionEnc for MirMonoPurifiedEnc {
    fn get_def_id(task_key: &Self::TaskKey<'_>) -> DefId {
        task_key.def_id
    }

    fn get_caller_def_id(task_key: &Self::TaskKey<'_>) -> Option<DefId> {
        Some(task_key.caller_def_id)
    }

    fn get_substs<'tcx>(
        _vcx: &vir::VirCtxt<'tcx>,
        task_key: &Self::TaskKey<'tcx>,
    ) -> &'tcx GenericArgs<'tcx> {
        task_key.substs
    }
}

impl PurifiedFunctionEnc for MirMonoPurifiedEnc {
    fn mk_method_ident<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        task_key: &Self::TaskKey<'tcx>,
    ) -> vir::ViperIdent<'vir> {
        task_key.vir_method_ident(vcx)
    }

    fn mk_conditions<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        task_key: &Self::TaskKey<'vir>,
        arg: &crate::encoders::PurifiedLocalDef<'vir>,
        idx: usize,
    ) -> Option<vir::ExprBool<'vir>> {
        Some(vcx.mk_todo_expr("TODO", vir::TYPE_BOOL))
    }
}

impl TaskEncoder for MirMonoPurifiedEnc {
    task_encoder::encoder_cache!(MirMonoPurifiedEnc);

    type TaskDescription<'tcx> = FunctionCallTaskDescription<'tcx>;

    type OutputRef<'vir> = PurifiedFunctionEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = PurifiedFunctionEncOutput<'vir>;

    type EncodingError = PurifiedFunctionEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        <Self as PurifiedFunctionEnc>::encode(*task_key, deps).map(|r| (r, ()))
    }
}
