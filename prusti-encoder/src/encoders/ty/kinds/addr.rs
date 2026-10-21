use crate::encoders::{
    ty::{
        data::TyData, impure::{PredicateBuilder, TyImpureAddr, TyImpureAddrDyn, TyImpureEnc}, pure::{AdtBuilder, DomainBuilder, TyPureAddrCommon, TyPureAddrData, TyPureEnc}, use_pure::TyUsePure, LazyRustTy, RustAddr, RustAddrData, RustTyDatas, TySpecifics
    }, TyUsePureEnc
};
use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::{CastType, VirCtxt};

pub(crate) fn ty_pure_dyn<'vir>(
    builder: &mut AdtBuilder<'vir>,
) -> Result<TyPureAddrCommon<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    let (mk_addr, destructors) =
        builder.constructor("mk", (vir::TYPE_REF, vir::TYPE_TYVAL), None);

    Ok(TyPureAddrCommon {
        mk_addr,
        addr_access: destructors[0].downcast_ty(),
        type_access: destructors[1].downcast_ty(),
    })
}

pub(crate) fn ty_pure_typed<'vir>(
    task_key: &TyData<'vir, RustTyDatas>,
    deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    data: &RustAddrData<'vir>,
    builder: &mut AdtBuilder<'vir>,
) -> Result<TyPureAddrData<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    let (mk_addr, destructors) =
        builder.constructor("mk", (vir::TYPE_REF, vir::TYPE_TYVAL), None);

    let addr_access = destructors[0].downcast_ty();
    let type_access = destructors[1].downcast_ty();

    let self_snap_decl = builder.vcx.mk_local_decl("s", builder.self_type());
    let self_snap_ex = builder.vcx.mk_local_ex(self_snap_decl);

    let tyval_decl = builder.vcx.mk_local_decl("ty", vir::TYPE_TYVAL);

    let dyn_ty = data.dyn_ty.decompose(task_key.params);
    let dyn_use = deps.require_dep::<TyUsePureEnc>(dyn_ty)?;
    let dyn_common = dyn_use.expect_addrdyn();
    let to_dyn = builder.function(
        "to_dyn",
        builder.self_type(),
        dyn_use.snapshot.downcast_ty(),
        (self_snap_decl,),
        &[],
        &[],
        Some(dyn_common.mk_addr.call()(
            addr_access.call()(self_snap_ex),
            type_access.call()(self_snap_ex),
        )),
    );

    Ok(TyPureAddrData {
        to_dyn,
        common: TyPureAddrCommon {
            mk_addr,
            addr_access,
            type_access,
        },
    })
}

pub(crate) fn ty_impure_typed<'vir>(
    builder: &mut PredicateBuilder<'vir>,
) -> Result<TyImpureAddr<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    super::primitive::set_primitive(builder);
    builder.mk_snap_function(None, &[]);
    Ok(())
}

pub(crate) fn ty_impure_dyn<'vir>(
    builder: &mut PredicateBuilder<'vir>,
) -> Result<TyImpureAddrDyn<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    super::primitive::set_primitive(builder);
    builder.mk_snap_function(None, &[]);
    Ok(())
}
