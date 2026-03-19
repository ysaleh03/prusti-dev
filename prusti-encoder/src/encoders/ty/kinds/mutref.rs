use crate::encoders::ty::{
    RustMutRef, RustTyDatas,
    builder::AdtBuilder,
    data::TyData,
    impure::{PredicateBuilder, TyImpureEnc, TyImpureMutRef, TyImpureMutRefData},
    lifted::{TyConstructorEnc, TypeOfEnc},
    pure::{TyPureEnc, TyPureMutRef, TyPureMutRefData},
    purified::{TyPurifiedEnc, TyPurifiedMutRef, TyPurifiedMutRefData},
};
use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::{CastType, HasType};

pub(crate) fn ty_pure<'vir>(
    builder: &mut AdtBuilder<'vir, crate::encoders::Pure>,
) -> Result<TyPureMutRef<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    let (field_snaps_to_snap, field_access) = builder.constructor("", vir::TYPE_REF, None);

    Ok(TyPureMutRefData {
        prim_to_snap: field_snaps_to_snap,
        deref_access: field_access[0].downcast_ty(),
    })
}

pub(crate) fn ty_impure<'vir>(
    data: &(&RustMutRef<'vir>, &TyPureMutRef<'vir>),
    _deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<TyImpureMutRef<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    let snap_type = builder.snap_type();

    let ref_self_decl = builder.ref_self_decl();
    let ref_self = builder.vcx.mk_local_ex(ref_self_decl);

    // fields
    let ref_field = builder.field("val", snap_type);

    // main predicate
    let self_pred = builder
        .inner
        .predicate::<(vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>(
            "",
            (
                ref_self_decl.ty(),
                builder.params.ty_args(),
                builder.params.const_args(),
            ),
            (
                ref_self_decl,
                builder.params.ty_decls(),
                builder.params.const_decls(),
            ),
            Some(vir::expr! { acc((ref_self).[ref_field]) }),
        );

    // Ref-to-snap
    builder.function_snap = Some(
        builder
            .mk_function::<(vir::Ref, vir::ManyTyVal, vir::ManyCSnap), _>(
                "snap",
                (ref_self_decl.ty(), builder.params.ty_args(), builder.params.const_args()),
                snap_type,
                (ref_self_decl, builder.params.ty_decls(), builder.params.const_decls()),
                &[vir::expr! { acc([self_pred](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]])) }],
                &[],
                Some(vir::expr! {
                    unfolding ([self_pred](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]])) in ([ref_field](ref_self))
                }),
            )
            .1,
    );

    // Ref-to-Ref
    let deref_func = builder.inner.function(
        "deref",
        (ref_self_decl.ty(), builder.params.ty_args(), builder.params.const_args()),
        vir::TYPE_REF,
        (ref_self_decl, builder.params.ty_decls(), builder.params.const_decls()),
        &[vir::expr! { acc([self_pred](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]])) }],
        &[],
        Some(vir::expr! {
            unfolding ([self_pred](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]])) in ([data.1.deref_access](([ref_field](ref_self)) as CSnap))
        }),
    );

    Ok(TyImpureMutRefData { deref_func })
}

pub(crate) fn ty_purified<'vir>(
    task_key: &'vir TyData<'vir, RustTyDatas>,
    data: &RustMutRef<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, TyPurifiedEnc>,
    builder: &mut AdtBuilder<'vir, crate::encoders::Purified>,
) -> Result<TyPurifiedMutRef<'vir>, EncodeFullError<'vir, TyPurifiedEnc>> {
    let vcx = builder.vcx;
    let ty_constructor = deps.require_ref::<TyConstructorEnc>(task_key)?;
    let type_constructor = ty_constructor.ty_constructor;
    let typeof_function = ty_constructor.typeof_data.typeof_function;
    let generic_typeof = deps
        .require_ref::<TypeOfEnc>(data.decompose(task_key.params).ty)?
        .typeof_function;

    let (field_snaps_to_snap, field_access) = builder.constructor("", vir::TYPE_PSNAP, None);

    builder.axiom(
        vir::vir_format!(vcx, "typeof"),
        vir::expr! {
            forall p: [field_access[0].ty()] :: {[typeof_function((field_snaps_to_snap(p.downcast_ty())).upcast_ty())]} ([typeof_function((field_snaps_to_snap(p.downcast_ty())).upcast_ty())]) == ([type_constructor(vcx.alloc_slice(&[generic_typeof(p.downcast_ty())]), &[])])
        },
    );

    Ok(TyPurifiedMutRefData {
        value_to_snap: field_snaps_to_snap,
        value_access: field_access[0].downcast_ty(),
    })
}
