use std::borrow::Borrow;

use task_encoder::{
    EncodeFullError, EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies,
};

use vir::{CastType, Domain, DomainIdn, FunctionIdn, TypeData};

use crate::encoders::{
    ImCapEnc, ImStateEnc, ImTyNameEnc, Pure, TyUsePureEnc,
    mir_fn::RustSignature,
    spec::with_type_im_spec,
    ty::{
        RustParamData,
        pure::{TyPure, TyPureEnc},
    },
};

use super::{
    RustFieldData, RustTy, RustTyDecomposition, RustTyNormalized, TySpecifics,
    generics::{GArgsCastEnc, GenericParamsEnc, TyExprEnc},
    pure::TyPureFieldRef,
};

type EncResult<'vir, T> = Result<T, EncodeFullError<'vir, ImTyEnc>>;

/// Encodes a type for use in our interior mutability reasoning.
/// Generates axioms that relate snapshots to compound types to the snapshots of their
/// parts in the ImState and functions for obtaining the addresses of abstract fields.

#[derive(Debug, Clone, Copy)]
pub enum ImTySpecifics<'vir> {
    StructLike(StructLikeData<'vir>),
    ImmRef(ImmRefData<'vir>),
    Other,
}

#[derive(Debug, Clone, Copy)]
pub struct ImTyEncRef<'vir> {
    // pub common: ImTyCommon<'vir>,
    pub specifics: ImTySpecifics<'vir>,
}

#[derive(Debug, Clone, Copy)]
pub struct StructLikeData<'vir> {
    // NOTE: index 0 is always `this`
    pub abs_fields: &'vir [vir::FunctionIdn<'vir, (vir::TyVal, vir::Ref, vir::Snap), vir::CSnap>],
}

#[derive(Debug, Clone, Copy)]
pub struct ImmRefData<'vir> {
    get_immref_idn: vir::FunctionIdn<'vir, (vir::ImState, vir::TyVal, vir::Ref), vir::CSnap>,
}

#[derive(Debug, Clone, Copy)]
pub struct ImTyEncResult<'vir> {
    domain: vir::Domain<'vir>,
}

impl<'vir> OutputRefAny for ImTyEncRef<'vir> {}

pub struct ImTyEnc;

impl TaskEncoder for ImTyEnc {
    task_encoder::encoder_cache!(ImTyEnc);
    const ENCODER_NAME: &'static str = "interior mutability type encoder";
    type TaskDescription<'vir> = RustTy<'vir>;

    type OutputRef<'vir> = ImTyEncRef<'vir>;
    type OutputFullLocal<'vir> = ImTyEncResult<'vir>;
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        // TODO grab abstract fields and emit functionidn for each in ref

        // TODO encode capability annotations
        // this requires we call encoders for ghost functions/spec code so we need to have emitted
        // the ref before this
        //
        // TODO we might be able to be very careful with our trigger choices so we only have to track
        // state and capabilities for unstable memory locations we care about. e.g. triggering capability-related
        // axioms when the *target* gets accessed/dereferenced?
        vir::with_vcx(|vcx| {
            let mut axioms = Vec::new();
            let mut functions = Vec::new();
            // emits heap axioms for each type

            // TODO encode snapshot-heap axioms - requires ?
            // TODO encode abstract field getters
            // TODO encode moved axioms
            // TODO capability prop to field axioms

            // TODO does this need to be recursive?

            // TODO requires:
            // getting immref snap from heap
            //

            let im_state = deps.require_ref::<ImStateEnc>(())?;
            let self_ty_pure = deps.require_dep::<TyPureEnc>(*task_key)?;

            let self_decomp = RustTyDecomposition::identity(*task_key);
            // let self_tyval = deps.require_dep::<TyExprEnc>(*task_key)?;

            let self_name = task_key.data.name();

            // let self_ty_use_pure = deps.require_dep::<TyUsePureEnc>(*task_key)?;
            // let self_snapshot = self_ty_use_pure.snapshot.downcast_ty();
            match &task_key.specifics {
                TySpecifics::Param(RustParamData::Generic)
                | TySpecifics::Param(RustParamData::Dyn)
                | TySpecifics::Opaque(_)
                | TySpecifics::Primitive(_)
                | TySpecifics::Raw(_)
                | TySpecifics::Builtin(_) => {
                    deps.emit_output_ref(*task_key, ImTyEncRef {
                        specifics: ImTySpecifics::Other,
                    })?;
                }
                TySpecifics::ImmRef(data) => {
                    // TODO sharing an immref implies sharing its target

                    deps.emit_output_ref(*task_key, ImTyEncRef {
                        specifics: ImTySpecifics::Other,
                    })?;

                    // TODO
                    // let snapshot = self_ty.snapshot;
                    // let immref_ty = self_ty.expect_immref();
                    // let get_immref_idn = vir::FunctionIdn::new(
                    //     vir::ViperIdent::new("get_immref"),
                    //     (vir::TYPE_IMSTATE, vir::TYPE_TYVAL, vir::TYPE_REF),
                    //     snapshot.downcast_ty(),
                    // );
                    // deps.emit_output_ref(task_key, ImTyRef::ImmRef(ImmRefData { get_immref_idn }));

                    // functions.push(vcx.mk_domain_function(get_immref_idn, false, None));

                    // axioms.push(vcx.mk_domain_axiom(
                    // vir::ViperIdent::new("get_immref_get_snap"),
                    // vir::expr!{
                    //     forall t: Type, s: ImState, l: Ref ::
                    //     { [get_immref_idn](s, t, l) }
                    //     (([immref_ty.deref_access](([get_immref_idn](s, t, l)))) == (l)) &&
                    //         (([immref_ty.value_access](([get_immref_idn](s, t, l)))) == ([im_state.get_snap_idn](s, t, l)))
                    // }));

                    // self.encode_decomposition(data.referent.decompose(ty.params))?
                }
                TySpecifics::MutRef(data) => {
                    // TODO owning an mutref implies owning its target

                    // TODO sharing an mutref implies sharing its target
                    deps.emit_output_ref(*task_key, ImTyEncRef {
                        specifics: ImTySpecifics::Other,
                    })?;
                }
                TySpecifics::ArrayLike(data) => {
                    deps.emit_output_ref(*task_key, ImTyEncRef {
                        specifics: ImTySpecifics::Other,
                    })?;

                    // if data.slice {
                    //     // An empty slice value exists even if its element type is uninhabited
                    //     vir::with_vcx(|vcx| vcx.mk_bool::<true>())
                    // } else {
                    //     let params = self.deps.require_dep::<GenericParamsEnc>(ty.params)?;
                    //     assert_eq!(params.const_exprs().len(), 1);
                    //     let usize_ty = vir::with_vcx(|vcx| vcx.tcx().types.usize);
                    //     let usize_enc = self
                    //         .deps
                    //         .require_dep::<TyPureEnc>(RustTyDecomposition::from_prim_ty(usize_ty).ty)?;
                    //     let usize_prim = usize_enc.expect_primitive();
                    //     let zero = usize_prim.prim_to_snap(usize_prim.expr_from_bits(usize_ty, 0));
                    //     let len_is_zero =
                    //         vir::with_vcx(|vcx| vcx.mk_eq_expr(params.const_exprs()[0], zero));
                    //     let element = self.encode_decomposition(data.data.decompose(ty.params))?;
                    //     vir::expr! { (len_is_zero) || (element) }
                    // }
                }
                TySpecifics::StructLike(data) => {
                    let abs_fields = vcx.alloc_slice(
                        &data
                            .data
                            .map(|def_id| {
                                with_type_im_spec(def_id, |abs_fields, _| {
                                    abs_fields
                                        .iter()
                                        .enumerate()
                                        .map(|(idx, field)| {
                                            let field_sig = RustSignature::new(field.def_id);
                                            let aloc_t_ty = deps
                                                .require_dep::<TyUsePureEnc>(
                                                    field_sig.output.decompose(field_sig.gparams),
                                                )
                                                .unwrap();
                                            let field_ref = vir::FunctionIdn::new(
                                                vir::vir_format_identifier!(
                                                    vcx,
                                                    "im_{}_abstract_field_{}",
                                                    self_name,
                                                    idx
                                                ),
                                                (vir::TYPE_TYVAL, vir::TYPE_REF, self_ty_pure.snapshot),
                                                aloc_t_ty.snapshot.downcast_ty(),
                                            );
                                            functions.push(
                                                vcx.mk_domain_function(field_ref, false, None),
                                            );

                                            let ty_ex = vcx.mk_local_ex(
                                                vcx.mk_local_decl("t", vir::TYPE_TYVAL),
                                            );
                                            let ref_ex = vcx
                                                .mk_local_ex(vcx.mk_local_decl("l", vir::TYPE_REF));
                                            let snap_ex = vcx.mk_local_ex(
                                                vcx.mk_local_decl("p", self_ty_pure.snapshot),
                                            );
                                            let field_ex = field_ref.call()(ty_ex, ref_ex, snap_ex);
                                            let type_access =
                                                aloc_t_ty.expect_addr().type_access(field_ex.upcast_ty());
                                            axioms.push(vcx.mk_domain_axiom(
                                                vir::vir_format_identifier!(
                                                    vcx,
                                                    "im_{}_abstract_field_ty_{}",
                                                    self_name,
                                                    idx
                                                ),
                                                vir::expr! {
                                                forall t: Type, l: Ref, p: [self_ty_pure.snapshot] :: { [field_ex] }
                                                ([type_access]) == (t)
                                            }));
                                            // TODO at callsite (possibly in a abstractfieldcall encoder)
                                            // we cast to caller context & constrain the type field of the
                                            // aloc_t
                                            field_ref
                                        })
                                        .collect::<Vec<_>>()
                                })
                            })
                            .unwrap_or(Vec::new()),
                    );

                    deps.emit_output_ref(*task_key, ImTyEncRef {
                        specifics: ImTySpecifics::StructLike(StructLikeData { abs_fields }),
                    })?;

                    // TODO encode field addr inequality axioms?
                    // TODO moved-axioms for abstract fields

                    let struct_data = self_ty_pure.expect_structlike();

                    // Process actual public fields of the struct
                    for (idx, (field_pure, field_data)) in struct_data
                        .fields
                        .iter()
                        .zip(data.fields.iter())
                        .enumerate()
                    {
                        if field_data.is_public {
                            let params = deps.require_dep::<GenericParamsEnc>(task_key.params)?;

                            let self_addr_decl = vcx.mk_local_decl("l", vir::TYPE_REF);
                            let self_addr = vcx.mk_local_ex(self_addr_decl);
                            let self_tyval = deps.require_dep::<TyExprEnc>(self_decomp)?;

                            let state_decl = vcx.mk_local_decl("s", vir::TYPE_IMSTATE);
                            let state = vcx.mk_local_ex(state_decl);

                            // Note: downcast safe because a type with fields cannot be generic
                            let self_caster =
                                deps.require_dep::<GArgsCastEnc<Pure>>(Some(RustTyNormalized {
                                    param: RustTyDecomposition::param(),
                                    concrete: self_decomp,
                                }))?;
                            let self_lookup = self_caster
                                .cast_to_caller_ctx(
                                    im_state.get_snap_idn.call()(self_tyval, state, self_addr)
                                        .upcast_ty(),
                                )
                                .downcast_ty();
                            let field_from_self = field_pure.read.call()(self_lookup);

                            let field_addr = match field_pure.ref_to_field_ref {
                                TyPureFieldRef::Constant(f) => {
                                    f.call()(self_addr, params.ty_exprs(), params.const_exprs())
                                }
                                TyPureFieldRef::Dynamic(f) => f.call()(self_lookup),
                            };

                            let field_ty = field_data.ty().decompose(task_key.params);
                            let field_tyval = deps.require_dep::<TyExprEnc>(field_ty)?;

                            // TODO do we need to special case param
                            let field_caster =
                                deps.require_dep::<GArgsCastEnc<Pure>>(Some(RustTyNormalized {
                                    param: RustTyDecomposition::param(),
                                    concrete: field_ty,
                                }))?;
                            let field_lookup = field_caster.cast_to_caller_ctx(
                                im_state.get_snap_idn.call()(field_tyval, state, field_addr)
                                    .upcast_ty(),
                            );

                            let views_eq = vcx.mk_eq_expr(field_from_self, field_lookup);

                            let ty_decls = params.ty_decls().as_dyn();
                            let const_decls = params.const_decls().as_dyn();
                            let qvars = ty_decls
                                .iter()
                                .chain(const_decls.iter())
                                .chain([self_addr_decl.as_dyn(), state_decl.as_dyn()].iter())
                                .map(|decl| *decl)
                                .collect::<Vec<_>>();

                            axioms.push(vcx.mk_domain_axiom(
                                vir::vir_format_identifier!(vcx, "im_{}_{}_state", self_name, idx),
                                vcx.mk_forall_expr(vcx.alloc_slice(&qvars[..]), &[], views_eq),
                            ));

                            let place_idx_decl = vcx.mk_local_decl("p", vir::TYPE_INT);
                            let place_idx = vcx.mk_local_ex(place_idx_decl);
                            let qvars = ty_decls
                                .iter()
                                .chain(const_decls.iter())
                                .chain(
                                    [
                                        self_addr_decl.as_dyn(),
                                        state_decl.as_dyn(),
                                        place_idx_decl.as_dyn(),
                                    ]
                                    .iter(),
                                )
                                .map(|decl| *decl)
                                .collect::<Vec<_>>();

                            let im_caps = deps.require_ref::<ImCapEnc>(())?;

                            // TODO change
                            let self_exclusive = im_caps.exclusive_idn.call()(
                                self_tyval, state, place_idx, self_addr,
                            );
                            let field_exclusive = im_caps.exclusive_idn.call()(
                                field_tyval,
                                state,
                                place_idx,
                                field_addr,
                            );
                            axioms.push(
                                vcx.mk_domain_axiom(
                                    vir::vir_format_identifier!(
                                        vcx,
                                        "{}_{}_exclusive",
                                        self_name,
                                        idx
                                    ),
                                    vcx.mk_forall_expr(
                                        vcx.alloc_slice(&qvars[..]),
                                        &[], // TODO triggers
                                        vcx.mk_bin_op_expr(
                                            vir::BinOpKind::Implies,
                                            self_exclusive,
                                            field_exclusive,
                                        )
                                        .downcast_ty(),
                                    ),
                                ),
                            );

                            let self_shared =
                                im_caps.shared_idn.call()(self_tyval, state, place_idx, self_addr);
                            let field_shared = im_caps.shared_idn.call()(
                                field_tyval,
                                state,
                                place_idx,
                                field_addr,
                            );
                            axioms.push(
                                vcx.mk_domain_axiom(
                                    vir::vir_format_identifier!(
                                        vcx,
                                        "{}_{}_shared",
                                        task_key.name(),
                                        idx
                                    ),
                                    vcx.mk_forall_expr(
                                        vcx.alloc_slice(&qvars[..]),
                                        &[], // TODO triggers
                                        vcx.mk_bin_op_expr(
                                            vir::BinOpKind::Implies,
                                            self_shared,
                                            field_shared,
                                        )
                                        .downcast_ty(),
                                    ),
                                ),
                            );
                        }
                    }

                    if let Some(def_id) = data.data {
                        with_type_im_spec(def_id, |abs_fields, capabilities| {
                            // TODO encode capability axioms
                            // TODO encode non-aliasing axiom (we can maybe skip non-aliasing between abstract & public fields)
                            //
                            // TODO what checks do we assume have already occured for the condition?
                        })
                    }
                }
                TySpecifics::EnumLike(data) => {
                    deps.emit_output_ref(*task_key, ImTyEncRef {
                        specifics: ImTySpecifics::Other,
                    })?;

                    // let variants = data
                    //     .variants
                    //     .iter()
                    //     .map(|variant| variant.inner.fields {
                    //     });

                    //         let fields = variant
                    //             .inner
                    //             .fields
                    //             .iter()
                    //             .map(|field| self.encode_decomposition(field.ty().decompose(ty.params)))
                    //             .collect::<EncResult<'vir, Vec<_>>>()?;
                    //         Ok(vir::with_vcx(|vcx| vcx.mk_conj(&fields)))
                    //     })
                    //     .collect::<EncResult<'vir, Vec<_>>>()?;
                    // vir::with_vcx(|vcx| vcx.mk_disj(&variants))
                }
                TySpecifics::Addr(_) => {
                    deps.emit_output_ref(*task_key, ImTyEncRef {
                        specifics: ImTySpecifics::Other,
                    })?;
                }
                TySpecifics::AddrDyn(data) => {
                    deps.emit_output_ref(*task_key, ImTyEncRef {
                        specifics: ImTySpecifics::Other,
                    })?;

                    let psnap_decl = vcx.mk_local_decl("s", vir::TYPE_PSNAP);
                    let psnap_ex = vcx.mk_local_ex(psnap_decl);

                    let self_caster =
                        deps.require_dep::<GArgsCastEnc<Pure>>(Some(RustTyNormalized {
                            param: RustTyDecomposition::param(),
                            concrete: self_decomp,
                        }))?;
                    let addrdyn = self_ty_pure.expect_addrdyn();
                    // A bit of a hack but here is where we constrain the addr and ty getter functions from ImStateEnc.
                    axioms.push(
                        vcx.mk_domain_axiom(
                            vir::vir_format_identifier!(
                                vcx,
                                "{}_addr_from_psnap_defn",
                                task_key.name()
                            ),
                            vcx.mk_forall_expr(
                                vcx.alloc_slice(&[psnap_decl]),
                                &[],
                                vcx.mk_eq_expr(
                                    im_state.addr_from_psnap_idn.call()(psnap_ex),
                                    addrdyn.addr_access.call()(
                                        self_caster
                                            .cast_to_caller_ctx(psnap_ex.upcast_ty())
                                            .downcast_ty(),
                                    ),
                                ),
                            ),
                        ),
                    );
                    axioms.push(
                        vcx.mk_domain_axiom(
                            vir::vir_format_identifier!(
                                vcx,
                                "{}_ty_from_psnap_defn",
                                task_key.name()
                            ),
                            vcx.mk_forall_expr(
                                vcx.alloc_slice(&[psnap_decl]),
                                &[],
                                vcx.mk_eq_expr(
                                    im_state.ty_from_psnap_idn.call()(psnap_ex),
                                    addrdyn.type_access.call()(
                                        self_caster
                                            .cast_to_caller_ctx(psnap_ex.upcast_ty())
                                            .downcast_ty(),
                                    ),
                                ),
                            ),
                        ),
                    );

                    let ty_decl = vcx.mk_local_decl("t", vir::TYPE_TYVAL);
                    let ty_ex = vcx.mk_local_ex(ty_decl);
                    let ref_decl = vcx.mk_local_decl("l", vir::TYPE_REF);
                    let ref_ex = vcx.mk_local_ex(ref_decl);
                    let mk_psnap_ex = im_state.mk_aloc_psnap_idn.call()(ty_ex, ref_ex);
                    axioms.push(
                        vcx.mk_domain_axiom(
                            vir::vir_format_identifier!(
                                vcx,
                                "{}_ty_mk_aloc_psnap_defn",
                                task_key.name()
                            ),
                            vcx.mk_forall_expr(
                                vcx.alloc_slice(&[ty_decl.as_dyn(), ref_decl.as_dyn()]),
                                vcx.alloc_slice(&[vcx.mk_trigger(&[mk_psnap_ex])]),
                                vcx.mk_eq_expr(
                                    mk_psnap_ex,
                                    self_caster
                                        .cast_to_callee_ctx(
                                            addrdyn.mk_addr.call()(ref_ex, ty_ex).upcast_ty(),
                                        )
                                        .downcast_ty(),
                                ),
                            ),
                        ),
                    );
                }
                TySpecifics::Rep(_) => {
                    deps.emit_output_ref(*task_key, ImTyEncRef {
                        specifics: ImTySpecifics::Other,
                    })?;
                }
            };
            Ok((
                ImTyEncResult {
                    domain: vcx.mk_domain(
                        vir::vir_format_identifier!(vcx, "im_ty_{}", self_name),
                        &[],
                        vcx.alloc_slice(&axioms[..]),
                        vcx.alloc_slice(&functions[..]),
                        None,
                    ),
                },
                (),
            ))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors(program) {
            program.add_domain(output.domain);
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ImTyUseResult<'vir> {
    pub abs_fields: &'vir [vir::FunctionIdn<'vir, (vir::TyVal, vir::Ref, vir::Snap), vir::CSnap>],
    pub field_tyvals: &'vir [vir::ExprTyVal<'vir>],
}

// impl<'vir> ImTyUseResult<'vir> {
//     fn get_field_loc<Curr, Next>(
//         &self,
//         idx: usize,
//         addr: vir::ExprGenRef<'vir, Curr, Next>,
//         snap: vir::ExprGenCSnap<'vir, Curr, Next>,
//     ) -> vir::ExprGenCSnap<'vir, Curr, Next> {
//         vir::with_vcx(|vcx| {
//             let field_ty: vir::ExprGenTyVal<'_, Curr, Next> = vcx.mk_lazy_expr(
//                 "field ty",
//                 vir::TYPE_TYVAL,
//                 Box::new(move |_, _| self.field_tyvals[idx].kind),
//             );
//             self.abs_fields[idx].call()(field_ty, addr, snap)
//         })
//     }
// }

pub struct ImTyUseEnc;

impl TaskEncoder for ImTyUseEnc {
    task_encoder::encoder_cache!(ImTyUseEnc);
    const ENCODER_NAME: &'static str = "interior mutability type use-site encoder";
    type TaskDescription<'vir> = RustTyDecomposition<'vir>;

    type OutputFullDependency<'vir> = ImTyUseResult<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let im_ty = deps.require_ref::<ImTyEnc>(task_key.ty)?;
            match im_ty.specifics {
                ImTySpecifics::StructLike(data) => {
                    let def_id = task_key.ty.expect_structlike();
                    let field_tyvals = vcx.alloc_slice(
                        &def_id
                            .map(|def_id| {
                                with_type_im_spec(def_id, |abs_fields, _| {
                                    abs_fields
                                        .iter()
                                        .map(|field| {
                                            let field_sig = RustSignature::new(field.def_id);
                                            println!("params: {:?}", field_sig.gparams);
                                            println!("field sig: {:?}", field_sig.output);
                                            println!("args: {:?}", task_key.args);
                                            let field_ty =
                                                field_sig.output.decompose_normalize(task_key.args);
                                            deps.require_dep::<TyExprEnc>(field_ty).unwrap()
                                        })
                                        .collect::<Vec<_>>()
                                })
                            })
                            .unwrap_or(Vec::new()),
                    );
                    Ok(((), ImTyUseResult {
                        abs_fields: data.abs_fields,
                        field_tyvals,
                    }))
                }
                _ => Ok(((), ImTyUseResult {
                    abs_fields: &[],
                    field_tyvals: &[],
                })),
            }
        })
    }
}
