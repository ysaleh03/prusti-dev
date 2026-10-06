use crate::encoders::ty::{
    LazyRustTy, RustAbsPtr,
    impure::{PredicateBuilder, TyImpureEnc},
    pure::{DomainBuilder, PureTyDatas, TyPureEnc, TyPureRepData},
};
use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::VirCtxt;

pub(crate) fn ty_pure<'vir>(
    _vcx: &'vir VirCtxt<'vir>,
    _data: &RustAbsPtr<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<(), EncodeFullError<'vir, TyPureEnc>> {
    Ok(())
}

// pub(crate) fn ty_impure<'vir>(
//     _data: &(&'vir LazyRustTy<'vir>, &'vir TyPureRepData<'vir>),
//     _deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
//     builder: &mut PredicateBuilder<'vir>,
// ) -> Result<TyImpureRepData<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
//     super::primitive::set_primitive(builder);
//     Ok(())
// }
