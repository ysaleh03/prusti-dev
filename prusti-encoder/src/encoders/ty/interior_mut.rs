use task_encoder::{
    EncodeFullError, EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies,
};

use vir::{CastType, Domain, DomainIdn, FunctionIdn, TypeData};

use crate::encoders::{
    ImCapEnc, ImStateEnc, ImTyNameEnc, Pure, TyUsePureEnc,
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
    abs_fields: &'vir [vir::FunctionIdn<'vir, vir::Ref, vir::Ref>],
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
                TySpecifics::Param(RustParamData::Generic) => unreachable!(),
                TySpecifics::Param(RustParamData::Dyn)
                | TySpecifics::Opaque(_)
                | TySpecifics::Primitive(_)
                | TySpecifics::Raw(_)
                | TySpecifics::Builtin(_) => {
                    deps.emit_output_ref(*task_key, ImTyEncRef {
                        specifics: ImTySpecifics::Other,
                    })?;
                }
                TySpecifics::ImmRef(data) => {
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
                    deps.emit_output_ref(*task_key, ImTyEncRef {
                        specifics: ImTySpecifics::Other,
                    })?;

                    // TODO encode field addr inequality axioms?
                    // TODO moved-axioms for abstract fields

                    let struct_data = self_ty_pure.expect_structlike();

                    for (idx, (field_pure, field_data)) in struct_data
                        .fields
                        .iter()
                        .zip(data.fields.iter())
                        .enumerate()
                    {
                        let field_data: &RustFieldData = field_data;

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
                        let self_exclusive =
                            im_caps.exclusive_idn.call()(self_tyval, state, place_idx, self_addr);
                        let field_exclusive =
                            im_caps.exclusive_idn.call()(field_tyval, state, place_idx, field_addr);
                        axioms.push(
                            vcx.mk_domain_axiom(
                                vir::vir_format_identifier!(vcx, "{}_{}_exclusive", self_name, idx),
                                vcx.mk_forall_expr(
                                    vcx.alloc_slice(&qvars[..]),
                                    &[],
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
                        let field_shared =
                            im_caps.shared_idn.call()(field_tyval, state, place_idx, field_addr);
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
                                    &[],
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
                TySpecifics::Addr(_) => todo!(),
                TySpecifics::AddrDyn(_) => todo!(),
                TySpecifics::Rep(_) => todo!(),
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
