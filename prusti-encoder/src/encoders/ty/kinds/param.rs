use crate::encoders::{
    Pure, Purified,
    ty::{
        RustParam,
        builder::DomainBuilder,
        impure::{PredicateBuilder, TyImpureEnc, TyImpureParam},
        pure::{TyPureEnc, TyPureParam},
        purified::{TyPurifiedEnc, TyPurifiedParam},
    },
};
use task_encoder::{EncodeFullError, TaskEncoderDependencies};

pub(crate) fn ty_pure<'vir>(
    _data: &RustParam<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    _builder: &mut DomainBuilder<'vir, Pure>,
) -> Result<TyPureParam<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    Ok(())
}

pub(crate) fn ty_impure<'vir>(
    _data: &(&RustParam<'vir>, &TyPureParam<'vir>),
    _deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<TyImpureParam<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    super::opaque::set_opaque(builder);
    Ok(())
}

pub(crate) fn ty_purified<'vir>(
    _data: &RustParam<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, TyPurifiedEnc>,
    _builder: &mut DomainBuilder<'vir, Purified>,
) -> Result<TyPurifiedParam<'vir>, EncodeFullError<'vir, TyPurifiedEnc>> {
    Ok(())
}
