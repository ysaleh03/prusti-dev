use crate::encoders::{
    domain::{AdtBuilder, FieldTy},
    predicate::PredicateBuilder,
    rust_ty_predicates::RustTyPredicatesEncOutputRef,
    snapshot::SnapshotEncOutput,
    PredicateEnc,
};
use prusti_rustc_interface::middle::ty::ParamTy;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{vir_format, CastType, FunctionIdn, HasType, PredicateIdn};

pub fn domain<'vir>(
    prefix: &str,
    fields: &[FieldTy<'vir>],
    builder: &mut AdtBuilder<'vir>,
    discr: Option<vir::ExprCSnap<'vir>>,
) -> (
    FunctionIdn<'vir, vir::ManySnap, vir::CSnap>,
    &'vir [vir::AdtDestructorSnap<'vir>],
) {
    let field_tys = builder
        .vcx
        .alloc_slice(&fields.iter().map(|f| f.ty).collect::<Vec<_>>());
    let (cons, des) = builder.constructor(prefix, field_tys, discr);
    (cons, builder.vcx.alloc_slice(&des).downcast_ty())
}

pub(crate) fn predicate<'vir>(
    prefix: &str,
    fields: &[RustTyPredicatesEncOutputRef<'vir>],
    typarams: &[LiftedTy<'vir, LiftedGeneric<'vir>>],
    task_key: <PredicateEnc as TaskEncoder>::TaskKey<'vir>,
    _snap: &SnapshotEncOutput<'vir>,
    variant_field_snaps_to_snap: FunctionIdn<'vir, (vir::ManyTyVal, vir::ManySnap), vir::CSnap>,
    _deps: &mut TaskEncoderDependencies<'vir, PredicateEnc>,
    generic_decls: &[vir::LocalDeclTyVal<'vir>],
    generic_exprs: &[vir::ExprTyVal<'vir>],
    builder: &mut PredicateBuilder<'vir>,
) -> Result<
    (
        Vec<FunctionIdn<'vir, (vir::Ref, vir::ManyTyVal), vir::Ref>>,
        PredicateIdn<'vir, (vir::Ref, vir::ManyTyVal)>,
        vir::ExprCSnap<'vir>,
    ),
    EncodeFullError<'vir, PredicateEnc>,
> {
    let ref_self = builder.vcx.mk_local("self", vir::TYPE_REF);
    let ref_self_decl = builder.vcx.mk_local_decl_local(ref_self);
    let ref_self_ex = builder.vcx.mk_local_ex_local(ref_self);

    let generic_decls_tys = builder.vcx.alloc_slice(
        generic_decls
            .iter()
            .copied()
            .map(vir::LocalDeclData::ty)
            .collect::<Vec<_>>()
            .as_slice(),
    );
    // Ref-to-Ref function for every field
    let field_accessors: Vec<FunctionIdn<'vir, (vir::Ref, vir::ManyTyVal), vir::Ref>> = fields
        .iter()
        .enumerate()
        .map(|(idx, _field)| {
            builder.function::<(vir::Ref, vir::ManyTyVal), vir::Ref>(
                &format!("{prefix}field_{idx}"),
                (ref_self_decl.ty(), generic_decls_tys),
                vir::TYPE_REF,
                (ref_self_decl, generic_decls),
                &[], // TODO: should have a read permission here!
                &[vir::expr! { ((ref_self) == (null)) == ((result: Ref) == (null)) }],
                None,
            )
        })
        .collect::<Vec<_>>();

    // main variant predicate
    let mut pred_name = String::new();
    if !prefix.is_empty() {
        pred_name = format!("{prefix}owned");
    }
    let pred_owned = builder.predicate::<(vir::Ref, vir::ManyTyVal)>(
        &pred_name,
        (ref_self_decl.ty(), generic_decls_tys),
        (ref_self_decl, generic_decls),
        Some(
            builder.vcx.mk_conj(
                &fields
                    .iter()
                    .zip(&field_accessors)
                    .map(|(field, accessor)| {
                        field.ref_to_pred(builder.vcx, accessor(ref_self_ex, &generic_exprs), None)
                    })
                    .collect::<Vec<_>>(),
            ),
        ),
    );

    // Ref-to-snap
    let snap_args = fields
        .iter()
        .zip(&field_accessors)
        .map(|(field, accessor)| {
            field.ref_to_snap(builder.vcx, (accessor)(ref_self_ex, &generic_exprs))
        })
        .collect::<Vec<_>>();

    let ty_args = typarams
        .iter()
        .map(|typ| typ.expr(builder.vcx))
        .collect::<Vec<_>>();

    let variant_snap_expr = vir::expr! {
        unfolding ([pred_owned](ref_self, ..[generic_exprs])) in ([variant_field_snaps_to_snap]([..[ty_args.as_slice()]], [..[snap_args.as_slice()]]))
    };

    Ok((field_accessors, pred_owned, variant_snap_expr))
}
