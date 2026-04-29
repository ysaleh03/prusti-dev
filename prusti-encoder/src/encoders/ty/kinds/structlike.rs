use crate::encoders::{
    ConstEnc, Purified,
    r#const::ConstEncTask,
    ty::{
        RustTyDatas, RustTyDecomposition,
        builder::AdtBuilder,
        data::{StructData, TyData, TySpecifics},
        generics::{
            GArgs, GArgsTy, GParamVariant, GenericParams, GenericParamsEnc, traits::TraitEnc,
        },
        impure::{ImpureTyDatas, PredicateBuilder, TyImpureEnc, TyImpureFieldData},
        lifted::{TyConstructorEnc, TypeOfEnc},
        pure::{PureTyDatas, TyPureEnc, TyPureFieldData, TyPureStructData},
        purified::{PurifiedTyDatas, TyPurifiedEnc, TyPurifiedFieldData, TyPurifiedStructData},
        use_impure::TyUseImpureEnc,
        use_pure::TyUsePureEnc,
        use_purified::TyUsePurifiedEnc,
    },
};
use prusti_rustc_interface::{data_structures::fx::FxHashMap, middle::ty};
use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::{CastType, ExprSnap, HasType, PredicateIdn, macros::ExprQuote};

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
    let params = &data.data;
    let ty_constructor_enc = deps.require_ref::<TyConstructorEnc>(task_key)?;
    let type_constructor = ty_constructor_enc.ty_constructor;
    let typeof_function = ty_constructor_enc.typeof_data.typeof_function;

    let mut field_ty_refs = Vec::new();
    let mut field_typeofs = Vec::new();
    let mut typaram_to_field_idx = FxHashMap::default();

    for f in data.fields.iter() {
        let decomposition = f.decompose(task_key.params);
        let field_typeof = deps
            .require_ref::<TypeOfEnc>(decomposition.ty)?
            .typeof_function;
        field_ty_refs.push(deps.require_ref::<TyUsePurifiedEnc>(decomposition)?);
        field_typeofs.push(field_typeof);

        for &p in params {
            if f.ty().0.contains(p.0) {
                typaram_to_field_idx.insert(p, f.fid);
            }
        }
    }

    let tyvals = vcx.alloc_slice(&params.iter().map(|_| vir::TYPE_TYVAL).collect::<Vec<_>>());
    let field_tys = vcx.alloc_slice(&field_ty_refs.iter().map(|t| t.snapshot).collect::<Vec<_>>());
    let (field_snaps_to_snap, des) = builder.constructor(prefix, (tyvals, field_tys), discr);
    let (ty_des, field_des) = des.split_at(params.len());

    assert_eq!(ty_des.len(), data.data.len());
    let typarams = ty_des
        .iter()
        .map(|read| TyPurifiedFieldData {
            read: read.downcast_ty(),
        })
        .collect::<Vec<_>>();

    // typaram_i axioms
    for idx in 0..params.len() {
        let typaram_accessor = typarams[idx].read;
        builder.axiom(
            vir::vir_format!(vcx, "{prefix}typaram_{idx}"),
            vir::expr! {
                forall s: [builder.self_type()] :: {[ty_constructor_enc.ty_param_from_snap(idx, s)]} ([ty_constructor_enc.ty_param_from_snap(idx, s).as_dyn()]) == ([typaram_accessor.call()(s).as_dyn()])
            });
    }

    assert_eq!(field_des.len(), data.fields.len());
    let fields = field_des
        .iter()
        .map(|read| TyPurifiedFieldData {
            read: read.downcast_ty(),
        })
        .collect::<Vec<_>>();

    let generics = deps.require_dep::<GenericParamsEnc>(task_key.params)?;

    // field_i axioms
    for (idx, field_typeof) in field_typeofs.iter().enumerate() {
        let field_accessor = fields[idx].read;
        let mut mk_field_ty_expr = |snap: ExprSnap<'vir>| {
            ty_expr_from_source(
                &generics,
                task_key,
                deps,
                snap,
                data.fields[idx].decompose(task_key.params),
            )
        };
        builder.axiom(
            vir::vir_format!(vcx, "{prefix}field_{idx}"),
            vir::expr! {
                forall s: [builder.self_type()] :: {[field_typeof]([field_accessor](s))} ([field_typeof]([field_accessor](s))) == ([mk_field_ty_expr(s.upcast_ty())])
            });
    }

    // cons axiom
    let tyvar_decls = params.iter().map(|ty| {
        let ty::TyKind::Param(p) = ty.0.kind() else {
            unreachable!()
        };
        vcx.mk_local_decl(
            vir::vir_format!(vcx, "{}${}", p.name, p.index),
            vir::TYPE_TYVAL,
        )
    });
    let tyvar_exprs = &tyvar_decls
        .clone()
        .map(|decl| decl.expr(vcx))
        .collect::<Vec<_>>();
    let field_decls = fields
        .iter()
        .enumerate()
        .map(|(idx, field)| vcx.mk_local_decl(vir::vir_format!(vcx, "p_{}", idx), field.read.ty()));
    let field_exprs = field_decls
        .clone()
        .map(|decl| decl.expr(vcx))
        .collect::<Vec<_>>();
    let quantified_decls = tyvar_decls
        .map(|decl| decl.as_dyn())
        .chain(field_decls.map(|decl| decl.as_dyn()))
        .collect::<Vec<_>>();
    builder.axiom(
        vir::vir_format!(vcx, "{prefix}typeof"),
        vcx.mk_forall_expr(
            vcx.alloc_slice(&quantified_decls),
            vcx.alloc_slice(&[vcx.mk_trigger(
                vcx.alloc_slice(&[typeof_function(
                    field_snaps_to_snap(
                        vcx.alloc_slice(&tyvar_exprs),
                        vcx.alloc_slice(&field_exprs),
                    )
                    .upcast_ty(),
                )]),
            )]),
            vcx.mk_eq_expr(
                typeof_function(
                    field_snaps_to_snap(
                        vcx.alloc_slice(&tyvar_exprs),
                        vcx.alloc_slice(&field_exprs),
                    )
                    .upcast_ty(),
                ),
                type_constructor(vcx.alloc_slice(&tyvar_exprs), vcx.alloc_slice(&[])),
            ),
        ),
    );

    Ok(StructData::new(
        TyPurifiedStructData {
            field_snaps_to_snap,
        },
        data.inhabited,
        fields,
    ))
}

fn ty_expr_from_source<'vir>(
    generics: &GenericParams<'vir>,
    task_key: &'vir TyData<'vir, RustTyDatas>,
    deps: &mut TaskEncoderDependencies<'vir, TyPurifiedEnc>,
    snap: ExprSnap<'vir>,
    ty: RustTyDecomposition<'vir>,
) -> vir::ExprTyVal<'vir> {
    if let TySpecifics::Param(()) = &ty.ty.specifics {
        let param = ty.args.expect_param();
        return match param {
            GParamVariant::Param(p) => deps
                .require_ref::<TyConstructorEnc>(task_key)
                .unwrap()
                .ty_param_from_snap(generics.map_idx(p.index).unwrap(), snap.downcast_ty()),
            GParamVariant::Alias(a) => vir::with_vcx(|vcx| {
                let tcx = vcx.tcx();
                let trait_did = tcx.associated_item(a.def_id).container_id(tcx);
                let trait_data = deps.require_dep::<TraitEnc>(trait_did).unwrap();
                let tys = &a
                    .args
                    .iter()
                    .map(|arg| match arg.expect_ty().kind() {
                        ty::TyKind::Param(p) => deps
                            .require_ref::<TyConstructorEnc>(task_key)
                            .unwrap()
                            .ty_param_from_snap(
                                generics.map_idx(p.index).unwrap(),
                                snap.downcast_ty(),
                            ),
                        _ => ty_expr_from_source(
                            generics,
                            task_key,
                            deps,
                            snap,
                            RustTyDecomposition::from_ty(arg.expect_ty(), tcx, ty.args.context()),
                        ),
                    })
                    .collect::<Vec<_>>();
                (trait_data.type_did_fun_mapping.get(&a.def_id).unwrap())(tys)
            }),
        };
    }
    let ty_constructor = deps
        .require_ref::<TyConstructorEnc>(ty.ty)
        .unwrap()
        .ty_constructor;
    let args = arg_ty_exprs_from_source(generics, ty.args, deps, task_key, snap);
    ty_constructor(args.get_ty(), args.get_const())
}

fn arg_ty_exprs_from_source<'vir>(
    generics: &GenericParams<'vir>,
    task_key: GArgs<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, TyPurifiedEnc>,
    source: &'vir TyData<'vir, RustTyDatas>,
    snap: ExprSnap<'vir>,
) -> GArgsTy<'vir> {
    let ty_args = task_key
        .args()
        .iter()
        .copied()
        .filter_map(ty::GenericArg::as_type)
        .map(|arg| {
            let decomp = vir::with_vcx(|vcx| {
                RustTyDecomposition::from_ty(arg, vcx.tcx(), task_key.context())
            });
            ty_expr_from_source(generics, source, deps, snap, decomp)
            // generics.ty_expr(deps, decomp)
        })
        .collect::<Vec<_>>();
    let const_args = task_key
        .args()
        .iter()
        .copied()
        .enumerate()
        .filter_map(|(i, a)| ty::GenericArg::as_const(a).map(|a| (i, a)))
        .map(|(i, const_)| {
            // If the constant is a value, we already know its type.
            // Otherwise, we will look it up in the param environment.
            // TODO: what about the other ConstKind variants?
            let ty = match const_.kind() {
                ty::ConstKind::Value(v) => v.ty,
                _ => task_key.context().expect_const(i).1,
            };
            let task = ConstEncTask::Ty {
                const_,
                ty,
                context: task_key.context(),
            };
            deps.require_dep::<ConstEnc<Purified>>(task).unwrap()
        })
        .collect::<Vec<_>>();
    vir::with_vcx(|vcx| GArgsTy {
        ty_args: vcx.alloc_slice(&ty_args),
        const_args: vcx.alloc_slice(&const_args),
    })
}
