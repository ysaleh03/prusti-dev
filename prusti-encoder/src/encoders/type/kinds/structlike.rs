use crate::encoders::{
    domain::{
        DomainBuilder, DomainEnc, DomainEncOutputRef, FieldFunctions, FieldTy, LiftedRustTyData,
        TyParam, TyParamFunction,
    },
    lifted::{generic::LiftedGeneric, ty::LiftedTy, ty_constructor::TyConstructorEnc},
    most_generic_ty,
    predicate::PredicateBuilder,
    rust_ty_predicates::RustTyPredicatesEncOutputRef,
    snapshot::SnapshotEncOutput,
    GenericEnc, PredicateEnc,
};
use prusti_rustc_interface::middle::ty::{ParamTy, TyKind};
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{macros::ExprQuote, vir_format, CastType, FunctionIdn, HasType, PredicateIdn};

/// Recurisvely visits all types in `task_key` and extracts the corresponding typeof function
fn extract_typeof<'vir: 'tcx, 'tcx, 'a>(
    vcx: &'vir vir::VirCtxt<'tcx>,
    deps: &'a mut TaskEncoderDependencies<'vir, DomainEnc>,
    output_ref: &'a DomainEncOutputRef<'vir>,
    task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
) -> impl FnMut(vir::ExprCSnap<'vir>) -> vir::ExprTyVal<'vir> + use<'vir, 'a, 'tcx> {
    let ty_constructor = deps
        .require_ref::<TyConstructorEnc>(task_key)
        .unwrap()
        .ty_constructor;

    move |variable| match task_key.kind() {
        TyKind::Param(param_ty) => {
            let param_idx = param_ty.index as usize;
            (output_ref.ty_param_accessors[param_idx])((output_ref.typeof_function)(
                variable.upcast_ty(),
            ))
        }
        TyKind::Adt(_, args) => {
            let rhss = args
                .types()
                .map(|ty| most_generic_ty::extract_type_params(vcx.tcx(), ty).0)
                .map(|mg_ty| extract_typeof(vcx, deps, output_ref, mg_ty)(variable))
                .collect::<Vec<_>>();
            (ty_constructor)(&rhss)
        }
        TyKind::Array(ty, _)
        | TyKind::Pat(ty, _)
        | TyKind::Slice(ty)
        | TyKind::RawPtr(ty, _)
        | TyKind::Ref(_, ty, _) => {
            let mg_ty = most_generic_ty::extract_type_params(vcx.tcx(), *ty).0;
            (ty_constructor)(&[extract_typeof(vcx, deps, output_ref, mg_ty)(variable)])
        }
        TyKind::Tuple(tys) => {
            let rhss = tys
                .iter()
                .map(|ty| most_generic_ty::extract_type_params(vcx.tcx(), ty).0)
                .map(|mg_ty| extract_typeof(vcx, deps, output_ref, mg_ty)(variable))
                .collect::<Vec<_>>();
            (ty_constructor)(&rhss)
        }
        _ => (ty_constructor)(&[]),
    }
}

pub fn domain<'vir>(
    prefix: &str,
    fields: &[FieldTy<'vir>],
    typarams: &[TyParam<'vir>],
    task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    output_ref: &DomainEncOutputRef<'vir>,
    generics: &[ParamTy],
    deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<
    (
        FunctionIdn<'vir, (vir::ManyTyVal, vir::ManySnap), vir::CSnap>,
        &'vir [FieldFunctions<'vir>],
        &'vir [TyParamFunction<'vir>],
        Vec<vir::LocalSnap<'vir>>,
        Vec<vir::LocalTyVal<'vir>>,
    ),
    EncodeFullError<'vir, DomainEnc>,
> {
    // constructor
    let cons_ident: FunctionIdn<'vir, (vir::ManyTyVal, vir::ManySnap), vir::CSnap> = builder
        .function(
            &format!("{prefix}cons"),
            (
                builder
                    .vcx
                    .alloc_slice(&typarams.iter().map(|typ| typ.ty).collect::<Vec<_>>()),
                builder
                    .vcx
                    .alloc_slice(&fields.iter().map(|fty| fty.ty).collect::<Vec<_>>()),
            ),
            builder.self_type(),
        );

    // field accessors
    let field_reads = fields
        .iter()
        .enumerate()
        .map(|(idx, ty)| {
            builder.function(&format!("{prefix}read_{idx}"), builder.self_type(), ty.ty)
        })
        .collect::<Vec<_>>();
    let field_writes = fields
        .iter()
        .enumerate()
        .map(|(idx, ty)| {
            builder.function(
                &format!("{prefix}write_{idx}"),
                (builder.self_type(), ty.ty),
                builder.self_type(),
            )
        })
        .collect::<Vec<_>>();

    // typaram accessors
    let typaram_reads = typarams
        .iter()
        .enumerate()
        .map(|(idx, ty)| {
            builder.function(&format!("{prefix}type_{idx}"), builder.self_type(), ty.ty)
        })
        .collect::<Vec<_>>();

    // variables for quantifiers
    let field_vars = fields
        .iter()
        .enumerate()
        .map(|(idx, ty)| {
            builder
                .vcx
                .mk_local(vir_format!(builder.vcx, "f{idx}"), ty.ty)
        })
        .collect::<Vec<_>>();
    let typaram_vars = typarams
        .iter()
        .enumerate()
        .map(|(idx, ty)| {
            builder
                .vcx
                .mk_local(vir_format!(builder.vcx, "arg_{idx}"), ty.ty)
        })
        .collect::<Vec<_>>();

    let param_idx_offset = typarams
        .iter()
        .find(|typ| matches!(typ.rust_ty.kind(), TyKind::Param(_)))
        .map_or(0, |typ| {
            let TyKind::Param(idx) = typ.rust_ty.kind() else {
                unreachable!()
            };
            idx.index
        }) as usize;

    // TODO: typeof and read_type axioms
    /*
    // for struct U<T> { x: T, y: i32 }
    // this one forwards the generic
    axiom ax_s_U_read_0_type {
        forall self: s_U :: {s_U_read_0(self)} (typ(s_U_read_0(self))) == (s_U_typaram_T(typeof_s_U(self)))
    }
    // this one seems less useful: this could be an axiom over s_Int_i32_typeof generally?
    axiom ax_s_U_read_1_type {
        forall self: s_U :: {s_U_read_1(self)} (s_Int_i32_typeof(s_U_read_1(self))) == (s_Int_i32_type())
    }
    axiom ax_typeof_s_U {
        forall self: s_U :: {s_U_typaram_T(typeof_s_U(self))} (typeof_s_U(self)) == (s_U_type(s_U_typaram_T(typeof_s_U(self))))
    }
    */

    if prefix.is_empty() {
        // TODO: this ensures that we only produce one axiom for enums, but the
        //   check based on prefix is not very clean
        let ty_cons = deps.require_ref::<TyConstructorEnc>(task_key)?;
        builder.axiom("typeof", vir::expr! {
            forall s: [builder.self_type()] ::
                {[output_ref.typeof_function]((s) as Snap)}
                ([output_ref.typeof_function]((s) as Snap)) == ([ty_cons.ty_constructor](..[generics.iter()
                    .enumerate()
                    .map(|(param_idx, _)| {
                        vir::expr! { [output_ref.ty_param_accessors[param_idx - param_idx_offset]]([output_ref.typeof_function]((s) as Snap)) }
                    })
                    .collect::<Vec<_>>()
                    .as_slice()]))
        });
    }

    let generic_enc = deps.require_ref::<GenericEnc>(())?;

    // field accessor axioms
    for idx in 0..fields.len() {
        builder.axiom(
            &format!("{prefix}cons_read_{idx}"),
            vir::expr! {
                forall ..[typaram_vars], ..[field_vars] ::
                    {[cons_ident]([..[typaram_vars]], [..[field_vars]])}
                    ([field_reads[idx]]([cons_ident]([..[typaram_vars]], [..[field_vars]]))) == ([field_vars[idx]])
            },
        );
        let field_ty = fields[idx].rust_ty;
        let field_ty_constructor = deps
            .require_ref::<TyConstructorEnc>(
                most_generic_ty::extract_type_params(builder.vcx.tcx(), field_ty).0,
            )
            .unwrap();
        let field_typeof = deps
            .require_ref::<crate::encoders::domain::DomainEnc>(
                most_generic_ty::extract_type_params(builder.vcx.tcx(), field_ty).0,
            )
            .unwrap()
            .typeof_function;
        let type_read_name = format!("{prefix}type_read_{idx}");
        match field_ty.kind() {
            TyKind::Param(p) => {
                let param_idx = p.index as usize;
                builder.axiom(&type_read_name, vir::expr! {
                        forall s: [builder.self_type()] ::
                            {[field_reads[idx]](s)}
                            ([generic_enc.param_type_function](([field_reads[idx]](s)) as PSnap)) == ([output_ref.ty_param_accessors[param_idx - param_idx_offset]]([output_ref.typeof_function]((s) as Snap)))
                        })
            }
            TyKind::Adt(_, args) => {
                let mut ty_cons = |var| {
                    args.types()
                        .map(|ty| most_generic_ty::extract_type_params(builder.vcx.tcx(), ty).0)
                        .map(|gen_ty| extract_typeof(builder.vcx, deps, output_ref, gen_ty)(var))
                        .collect::<Vec<_>>()
                };
                builder.axiom(&type_read_name, vir::expr! {
                    forall s: [builder.self_type()] ::
                        {[field_reads[idx]](s)}
                        ([field_typeof]([field_reads[idx]](s))) == ([(field_ty_constructor.ty_constructor)(&ty_cons(s))])
                })
            }
            TyKind::Array(ty, _)
            | TyKind::Pat(ty, _)
            | TyKind::Slice(ty)
            | TyKind::RawPtr(ty, _)
            | TyKind::Ref(_, ty, _) => {
                let mut ty_con = |var| {
                    extract_typeof(
                        builder.vcx,
                        deps,
                        output_ref,
                        most_generic_ty::extract_type_params(builder.vcx.tcx(), *ty).0,
                    )(var)
                };
                builder.axiom(&type_read_name, vir::expr! {
                    forall s: [builder.self_type()] ::
                        {[field_reads[idx]](s)}
                        ([field_typeof]([field_reads[idx]](s))) == ([(field_ty_constructor.ty_constructor)(&[ty_con(s)])])
                })
            }
            TyKind::Tuple(tys) => {
                let mut ty_cons = |var| {
                    tys.iter()
                        .map(|ty| most_generic_ty::extract_type_params(builder.vcx.tcx(), ty).0)
                        .map(|gen_ty| extract_typeof(builder.vcx, deps, output_ref, gen_ty)(var))
                        .collect::<Vec<_>>()
                };
                builder.axiom(&type_read_name, vir::expr! {
                    forall s: [builder.self_type()] ::
                        {[field_reads[idx]](s)}
                        ([field_typeof]([field_reads[idx]](s))) == ([(field_ty_constructor.ty_constructor)(&ty_cons(s))])
                })
            }
            _ => {}
        };
    }
    for write_idx in 0..fields.len() {
        for read_idx in 0..fields.len() {
            // TODO: is the trigger here too specific? we could trigger on the read already?
            builder.axiom(&format!("{prefix}write_{write_idx}_read_{read_idx}"), if read_idx == write_idx {
            vir::expr! {
                forall s: [builder.self_type()], value: [fields[write_idx].ty] ::
                    {[field_reads[read_idx]]([field_writes[write_idx]](s, value))}
                    ([field_reads[read_idx]]([field_writes[write_idx]](s, value))) == (value)
            }
        } else {
            vir::expr! {
                forall s: [builder.self_type()], value: [fields[write_idx].ty] ::
                    {[field_reads[read_idx]]([field_writes[write_idx]](s, value))}
                    ([field_reads[read_idx]]([field_writes[write_idx]](s, value))) == ([field_reads[read_idx]](s))
            }
        });
        }
    }

    // typaram accessor axioms
    for idx in 0..typarams.len() {
        builder.axiom(
            &format!("{prefix}cons_type_{idx}"),
            vir::expr! {
                forall ..[typaram_vars], ..[field_vars] ::
                    {[cons_ident]([..[typaram_vars]], [..[field_vars]])}
                    ([typaram_reads[idx]]([cons_ident]([..[typaram_vars]], [..[field_vars]]))) == ([typaram_vars[idx]])
            },
        );
        let typaram_ty = typarams[idx].rust_ty;
        let typaram_ty_constructor = deps
            .require_ref::<TyConstructorEnc>(
                most_generic_ty::extract_type_params(builder.vcx.tcx(), typaram_ty).0,
            )
            .unwrap();
        let type_read_name = format!("{prefix}type_type_{idx}");
        match typaram_ty.kind() {
            TyKind::Param(p) => {
                let param_idx = p.index as usize;
                builder.axiom(&type_read_name, vir::expr! {
                    forall s: [builder.self_type()] ::
                        {[typaram_reads[idx]](s)}
                        ([typaram_reads[idx]](s)) == ([output_ref.ty_param_accessors[param_idx - param_idx_offset]]([output_ref.typeof_function]((s) as Snap)))
                })
            }
            TyKind::Adt(_, args) => {
                let mut ty_cons = |var| {
                    args.types()
                        .map(|ty| most_generic_ty::extract_type_params(builder.vcx.tcx(), ty).0)
                        .map(|gen_ty| extract_typeof(builder.vcx, deps, output_ref, gen_ty)(var))
                        .collect::<Vec<_>>()
                };
                builder.axiom(&type_read_name, vir::expr! {
                    forall s: [builder.self_type()] ::
                        {[typaram_reads[idx]](s)}
                        ([typaram_reads[idx]](s)) == ([(typaram_ty_constructor.ty_constructor)(&ty_cons(s))])
                })
            }
            TyKind::Array(ty, _)
            | TyKind::Pat(ty, _)
            | TyKind::Slice(ty)
            | TyKind::RawPtr(ty, _)
            | TyKind::Ref(_, ty, _) => {
                let mut ty_con = |var| {
                    extract_typeof(
                        builder.vcx,
                        deps,
                        output_ref,
                        most_generic_ty::extract_type_params(builder.vcx.tcx(), *ty).0,
                    )(var)
                };
                builder.axiom(&type_read_name, vir::expr! {
                    forall s: [builder.self_type()] ::
                        {[typaram_reads[idx]](s)}
                        ([typaram_reads[idx]](s)) == ([(typaram_ty_constructor.ty_constructor)(&[ty_con(s)])])
                })
            }
            TyKind::Tuple(tys) => {
                let mut ty_cons = |var| {
                    tys.iter()
                        .map(|ty| most_generic_ty::extract_type_params(builder.vcx.tcx(), ty).0)
                        .map(|gen_ty| extract_typeof(builder.vcx, deps, output_ref, gen_ty)(var))
                        .collect::<Vec<_>>()
                };
                builder.axiom(&type_read_name, vir::expr! {
                    forall s: [builder.self_type()] ::
                        {[typaram_reads[idx]](s)}
                        ([typaram_reads[idx]](s)) == ([(typaram_ty_constructor.ty_constructor)(&ty_cons(s))])
                })
            }
            _ => {}
        };
    }

    let field_access = field_reads
        .into_iter()
        .zip(field_writes)
        .map(|(read, write)| FieldFunctions {
            read: read,
            write: write,
        })
        .collect::<Vec<_>>();

    Ok((
        cons_ident,
        builder.vcx.alloc_slice(&field_access),
        builder.vcx.alloc_slice(&typaram_reads),
        field_vars,
        typaram_vars,
    ))
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
