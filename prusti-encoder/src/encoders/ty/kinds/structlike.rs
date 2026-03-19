use crate::encoders::ty::{
    RustTyDatas,
    builder::AdtBuilder,
    data::{StructData, TyData},
    generics::GenericParamsEnc,
    impure::{ImpureTyDatas, PredicateBuilder, TyImpureEnc, TyImpureFieldData},
    lifted::{TyConstructorEnc, TypeOfEnc},
    pure::{PureTyDatas, TyPureEnc, TyPureFieldData, TyPureStructData},
    purified::{PurifiedTyDatas, TyPurifiedEnc, TyPurifiedFieldData, TyPurifiedStructData},
    use_impure::TyUseImpureEnc,
    use_pure::TyUsePureEnc,
    use_purified::TyUsePurifiedEnc,
};
use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::{CastType, HasType, PredicateIdn, Snap, macros::ExprQuote};

pub(crate) fn ty_pure<'vir>(
    task_key: &TyData<'vir, RustTyDatas>,
    data: &StructData<'vir, RustTyDatas>,
    deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut AdtBuilder<'vir, crate::encoders::Pure>,
) -> Result<StructData<'vir, PureTyDatas>, EncodeFullError<'vir, TyPureEnc>> {
    ty_pure_variant("", None, task_key, data, deps, builder)
}

pub(super) fn ty_pure_variant<'vir>(
    prefix: &str,
    discr: Option<vir::ExprCSnap<'vir>>,
    task_key: &TyData<'vir, RustTyDatas>,
    data: &StructData<'vir, RustTyDatas>,
    deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut AdtBuilder<'vir, crate::encoders::Pure>,
) -> Result<StructData<'vir, PureTyDatas>, EncodeFullError<'vir, TyPureEnc>> {
    let field_tys = data
        .fields
        .iter()
        .map(|f| {
            let ty = f.decompose(task_key.params);
            Ok(deps.require_ref::<TyUsePureEnc>(ty)?.snapshot)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let field_tys = builder.vcx.alloc_slice(&field_tys);
    let (field_snaps_to_snap, des) = builder.constructor(prefix, field_tys, discr);
    assert_eq!(des.len(), data.fields.len());
    let des = des
        .iter()
        .map(|read| TyPureFieldData {
            read: read.downcast_ty(),
        })
        .collect::<Vec<_>>();
    Ok(StructData::new(
        TyPureStructData {
            field_snaps_to_snap,
        },
        data.inhabited,
        des,
    ))
}

pub(crate) fn ty_impure<'vir>(
    task_key: &TyData<'vir, (RustTyDatas, PureTyDatas)>,
    data: &StructData<'vir, (RustTyDatas, PureTyDatas)>,
    deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<StructData<'vir, ImpureTyDatas>, EncodeFullError<'vir, TyImpureEnc>> {
    let (data, self_pred, snap_expr) = ty_impure_variant("", task_key, data, deps, builder)?;

    let ref_self_decl = builder.ref_self_decl();
    let ref_self = builder.vcx.mk_local_ex(ref_self_decl);

    // Ref-to-snap
    builder.function_snap = Some(
        builder
            .mk_function::<(vir::Ref, vir::ManyTyVal, vir::ManyCSnap), _>(
                "snap",
                (ref_self_decl.ty(), builder.params.ty_args(), builder.params.const_args()),
                builder.csnap_type(),
                (ref_self_decl, builder.params.ty_decls(), builder.params.const_decls()),
                &[vir::expr! { acc([self_pred](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]])) }],
                &[],
                Some(snap_expr),
            )
            .1,
    );
    Ok(data)
}

pub(super) type ImpureVariant<'vir> = (
    StructData<'vir, ImpureTyDatas>,
    PredicateIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>,
    vir::ExprCSnap<'vir>,
);

pub(crate) fn ty_impure_variant<'vir>(
    prefix: &str,
    task_key: &TyData<'vir, (RustTyDatas, PureTyDatas)>,
    data: &StructData<'vir, (RustTyDatas, PureTyDatas)>,
    deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<ImpureVariant<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    let fields = data
        .fields
        .iter()
        .map(|f| {
            let ty = f.0.decompose(task_key.0.params);
            deps.require_dep::<TyUseImpureEnc>(ty)
        })
        .collect::<Result<Vec<_>, _>>()?;

    let ref_self_decl = builder.ref_self_decl();
    let ref_self = builder.vcx.mk_local_ex(ref_self_decl);

    // Ref-to-Ref function for every field
    let field_accessors = fields
        .iter()
        .enumerate()
        .map(|(idx, _field)| {
            let ref_to_field_ref = builder
                .inner
                .function::<(vir::Ref, vir::ManyTyVal, vir::ManyCSnap), vir::Ref>(
                    &format!("{prefix}field_{idx}"),
                    (
                        ref_self_decl.ty(),
                        builder.params.ty_args(),
                        builder.params.const_args(),
                    ),
                    vir::TYPE_REF,
                    (
                        ref_self_decl,
                        builder.params.ty_decls(),
                        builder.params.const_decls(),
                    ),
                    &[], // TODO: should have a read permission here!
                    &[vir::expr! { ((ref_self) == (null)) == ((result: Ref) == (null)) }],
                    None,
                );
            TyImpureFieldData { ref_to_field_ref }
        })
        .collect::<Vec<_>>();

    // main variant predicate
    let mut pred_name = String::new();
    if !prefix.is_empty() {
        pred_name = format!("{prefix}owned");
    }
    let pred_owned = builder
        .inner
        .predicate::<(vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>(
            &pred_name,
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
            Some(
                builder.vcx.mk_conj(
                    &fields
                        .iter()
                        .zip(&field_accessors)
                        .map(|(field, accessor)| {
                            let TyImpureFieldData { ref_to_field_ref } = accessor;
                            field.ref_to_pred(
                                builder.vcx,
                                ref_to_field_ref(
                                    ref_self,
                                    builder.params.ty_exprs(),
                                    builder.params.const_exprs(),
                                ),
                                None,
                            )
                        })
                        .collect::<Vec<_>>(),
                ),
            ),
        );

    // Ref-to-snap
    let snap_args: Vec<&'vir vir::ExprGenData<'vir, (), !, vir::Snap>> = fields
        .iter()
        .zip(&field_accessors)
        .map(|(field, accessor)| {
            let TyImpureFieldData { ref_to_field_ref } = accessor;
            field.ref_to_snap(ref_to_field_ref(
                ref_self,
                builder.params.ty_exprs(),
                builder.params.const_exprs(),
            ))
        })
        .collect::<Vec<_>>();
    let variant_snap_expr = vir::expr! {
        unfolding ([pred_owned](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]])) in ([data.1.field_snaps_to_snap](..[snap_args.as_slice()]))
    };

    Ok((
        StructData::new((), data.inhabited, field_accessors),
        pred_owned,
        variant_snap_expr,
    ))
}

pub(crate) fn ty_purified<'vir>(
    task_key: &'vir TyData<'vir, RustTyDatas>,
    data: &StructData<'vir, RustTyDatas>,
    deps: &mut TaskEncoderDependencies<'vir, TyPurifiedEnc>,
    builder: &mut AdtBuilder<'vir, crate::encoders::Purified>,
) -> Result<StructData<'vir, PurifiedTyDatas>, EncodeFullError<'vir, TyPurifiedEnc>> {
    ty_purified_variant("", None, task_key, data, deps, builder)
}

pub(super) fn ty_purified_variant<'vir>(
    prefix: &str,
    discr: Option<vir::ExprCSnap<'vir>>,
    task_key: &'vir TyData<'vir, RustTyDatas>,
    data: &StructData<'vir, RustTyDatas>,
    deps: &mut TaskEncoderDependencies<'vir, TyPurifiedEnc>,
    builder: &mut AdtBuilder<'vir, crate::encoders::Purified>,
) -> Result<StructData<'vir, PurifiedTyDatas>, EncodeFullError<'vir, TyPurifiedEnc>> {
    let vcx = builder.vcx;
    let ty_constructor = deps.require_ref::<TyConstructorEnc>(task_key)?;
    let type_constructor = ty_constructor.ty_constructor;
    let typeof_function = ty_constructor.typeof_data.typeof_function;
    let mut field_tys = Vec::new();
    let mut field_typeofs = Vec::new();
    for f in data.fields.iter() {
        let ty = f.decompose(task_key.params);
        field_tys.push(deps.require_ref::<TyUsePurifiedEnc>(ty)?.snapshot);
        field_typeofs.push(deps.require_ref::<TypeOfEnc>(ty.ty)?.typeof_function);
    }
    let field_tys = vcx.alloc_slice(&field_tys);
    let field_typeofs = vcx.alloc_slice(&field_typeofs);
    let (field_snaps_to_snap, des) = builder.constructor(prefix, field_tys, discr);
    assert_eq!(des.len(), data.fields.len());
    let des = des
        .iter()
        .map(|read| TyPurifiedFieldData {
            read: read.downcast_ty(),
        })
        .collect::<Vec<_>>();

    for (idx, field_typeof) in field_typeofs.iter().enumerate() {
        let field_accessor = des[idx].read;
        builder.axiom(
            vir::vir_format!(vcx, "typaram{}", field_accessor.name),
            vir::expr! {
                forall s: [builder.self_type()] :: {[ty_constructor.ty_param_from_snap(idx, s)]} ([ty_constructor.ty_param_from_snap(idx, s)]) == ([field_typeof]([field_accessor](s)))
            },
        );
    }

    let axiom_expr = if des.is_empty() {
        vcx.mk_eq_expr(
            typeof_function(field_snaps_to_snap(vcx.alloc_slice(&[])).upcast_ty()),
            type_constructor(&[], &[]),
        )
    } else {
        let decls = des
            .iter()
            .map(|field| {
                vcx.mk_local_decl(
                    vir::vir_format!(vcx, "p{}", field.read.name),
                    field.read.ty(),
                )
            })
            .collect::<Vec<_>>();
        let apps = decls
            .iter()
            .zip(field_typeofs.iter())
            .map(|(decl, param_typeof)| param_typeof.call()(decl.expr(vcx)))
            .collect::<Vec<_>>();
        let snaps = decls.iter().map(|decl| decl.expr(vcx)).collect::<Vec<_>>();
        vcx.mk_forall_expr(
            vcx.alloc_slice(&decls),
            vcx.alloc_slice(&[vcx.mk_trigger(&[typeof_function(
                field_snaps_to_snap(vcx.alloc_slice(&snaps)).upcast_ty(),
            )])]),
            vcx.mk_eq_expr(
                typeof_function(field_snaps_to_snap(vcx.alloc_slice(&snaps)).upcast_ty()),
                type_constructor(&apps, vcx.alloc_slice(&builder.params.const_exprs())),
            ),
        )
    };

    builder.axiom(vir::vir_format!(vcx, "typeof"), axiom_expr);

    Ok(StructData::new(
        TyPurifiedStructData {
            field_snaps_to_snap,
        },
        data.inhabited,
        des,
    ))
}
