use crate::encoders::ty::{
    LazyRustTy,
    impure::{PredicateBuilder, TyImpureEnc},
    pure::{DomainBuilder, PureTyDatas, TyPureEnc, TyPureRepData},
};
use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::VirCtxt;

pub(crate) fn ty_pure<'vir>(
    _vcx: &'vir VirCtxt<'vir>,
    _data: &LazyRustTy<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<(), EncodeFullError<'vir, TyPureEnc>> {
    // TODO do we want to put the mk_rep & rep_eq functions in here instead?
    Ok(())
}

pub(crate) fn ty_impure<'vir>(
    builder: &mut PredicateBuilder<'vir>,
) -> Result<(), EncodeFullError<'vir, TyImpureEnc>> {
    super::primitive::set_primitive(builder);
    builder.mk_snap_function(None, &[]);
    Ok(())
}
