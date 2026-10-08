use crate::encoders::ty::{
    LazyRustTy, RustAddr,
    impure::{PredicateBuilder, TyImpureAddr, TyImpureAddrData, TyImpureEnc},
    pure::{AdtBuilder, TyPureAddrData, TyPureEnc},
};
use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::{CastType, VirCtxt};

pub(crate) fn ty_pure<'vir>(
    _vcx: &'vir VirCtxt<'vir>,
    _data: &RustAddr<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut AdtBuilder<'vir>,
) -> Result<TyPureAddrData<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    // TODO we should be able to construct an Addr<T> from a Ref and TyVal

    let (mk_addr, destructors) =
        builder.constructor("mk_Addr", (vir::TYPE_REF, vir::TYPE_TYVAL), None);

    // let immref_type = todo!();
    // let addr_to_immref = builder.function("s_ImmRef_to_Addr", vir::TYPE_REF, immref_type);
    // let immref_to_addr = builder.function("Addr_to_s_ImmRef", immref_type, vir::TYPE_REF);

    // let capability_input_type = (vir::TYPE_REF, vir::TYPE_INT);
    // let unique = builder.function("unique", capability_input_type, vir::TYPE_BOOL);
    // let shared = builder.function("shared", capability_input_type, vir::TYPE_BOOL);
    // let local_unique = builder.function(
    //     "local_unique",
    //     (vir::TYPE_REF, vir::TYPE_REF, vir::TYPE_INT),
    //     vir::TYPE_BOOL,
    // );
    // let atomic_unique = builder.function("atomic_unique", capability_input_type, vir::TYPE_BOOL);

    // builder.axiom("unique", vir::expr! {
    //     forall l: [vir::TYPE_REF], pc: Int :: {[unique](l, pc)} ([unique](l, pc)) ==> ([unique](l, pc))
    //  });
    // builder.axiom("shared", vir::expr! {
    //     forall l: [vir::TYPE_REF], pc: Int :: {[shared](l, pc)} ([shared](l, pc)) ==> ([shared](l, pc))
    //  });
    // builder.axiom("local_unique", vir::expr! {
    //     forall ld: [vir::TYPE_REF], l: [vir::TYPE_REF], pc: Int :: {[local_unique](ld, l, pc)} ([local_unique](ld, l, pc)) ==> ([local_unique](ld, l, pc))
    //  });
    // builder.axiom("unique", vir::expr! {
    //     forall s: [vir::TYPE_REF], pc: Int :: {[unique](s, pc)} ([unique](s, pc)) ==> ([unique](s, pc))
    //  });

    Ok(TyPureAddrData {
        mk_addr,
        addr_access: destructors[0].downcast_ty(),
        type_access: destructors[1].downcast_ty(),
        // addr_to_immref,
        // immref_to_addr,
        // unique,
        // shared,
        // local_unique,
        // atomic_unique,
    })
}

pub(crate) fn ty_impure<'vir>(
    _data: &(&'vir (), &'vir TyPureAddrData<'vir>),
    _deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<TyImpureAddr<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    super::primitive::set_primitive(builder);
    Ok(TyImpureAddrData {})
}
