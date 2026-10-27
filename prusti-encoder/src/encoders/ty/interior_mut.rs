use std::{borrow::Borrow, collections::HashMap};

use prusti_interface::specs::typed::{CapabilityKind, CapabilitySpecification};
use prusti_rustc_interface::middle::mir;
use rustc_hash::FxHashMap;
use task_encoder::{
    EncodeFullError, EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies,
};

use vir::{CastType, Domain, DomainIdn, FunctionIdn, Reify, TypeData};

use crate::encoders::{
    ImCapEnc, ImStateEnc, ImTyNameEnc, MirLocalDefEnc, MirLocalDefEncTask, MirPureEnc,
    MirPureEncTask, Pure, PureKind, TyUsePureEnc,
    mir_fn::RustSignature,
    spec::with_type_im_spec,
    ty::{
        RustParamData,
        pure::{TyPure, TyPureEnc},
    },
};

use super::{
    RustFieldData, RustTy, RustTyDecomposition, RustTyNormalized, TySpecifics,
    generics::{GArgsCastEnc, GParams, GenericParamsEnc, TyExprEnc},
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
            let im_caps = deps.require_ref::<ImCapEnc>(())?;
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
                    deps.emit_output_ref(*task_key, ImTyEncRef {
                        specifics: ImTySpecifics::Other,
                    })?;

                    let params = deps.require_dep::<GenericParamsEnc>(task_key.params)?;
                    let ref_tyval = deps.require_dep::<TyExprEnc>(self_decomp)?;
                    let target_ty = data.referent.decompose(task_key.params);
                    let target_tyval = deps.require_dep::<TyExprEnc>(target_ty)?;
                    let state_decl = vcx.mk_local_decl("s", vir::TYPE_IMSTATE);
                    let state = vcx.mk_local_ex(state_decl);
                    let addr_decl = vcx.mk_local_decl("l", vir::TYPE_REF);
                    let addr = vcx.mk_local_ex(addr_decl);
                    let idx_decl = vcx.mk_local_decl("p", vir::TYPE_INT);
                    let idx = vcx.mk_local_ex(idx_decl);
                    let self_caster =
                        deps.require_dep::<GArgsCastEnc<Pure>>(Some(RustTyNormalized {
                            param: RustTyDecomposition::param(),
                            concrete: self_decomp,
                        }))?;
                    let ref_snap = self_caster
                        .cast_to_caller_ctx(
                            im_state.get_snap_idn.call()(ref_tyval, state, addr).upcast_ty(),
                        )
                        .downcast_ty();
                    let ref_use = deps.require_dep::<TyUsePureEnc>(self_decomp)?.expect_immref();
                    let target_addr = ref_use.addr_access(ref_snap);
                    let shared = im_caps.shared_idn.call()(ref_tyval, state, idx, addr);
                    let target_shared =
                        im_caps.shared_idn.call()(target_tyval, state, idx, target_addr);
                    let qvars = params
                        .ty_decls()
                        .as_dyn()
                        .iter()
                        .chain(params.const_decls().as_dyn().iter())
                        .chain([state_decl.as_dyn(), addr_decl.as_dyn(), idx_decl.as_dyn()].iter())
                        .copied()
                        .collect::<Vec<_>>();

                    // shared capability to a shared reference implies shared capability to its target
                    axioms.push(
                        vcx.mk_domain_axiom(
                            vir::vir_format_identifier!(vcx, "{}_shared_target", self_name),
                            vcx.mk_forall_expr(
                                vcx.alloc_slice(&qvars[..]),
                                &[],
                                vcx.mk_bin_op_expr(vir::BinOpKind::Implies, shared, target_shared)
                                    .downcast_ty(),
                            ),
                        ),
                    );

                    let qvars = params
                        .ty_decls()
                        .as_dyn()
                        .iter()
                        .chain(params.const_decls().as_dyn().iter())
                        .chain([state_decl.as_dyn(), addr_decl.as_dyn()].iter())
                        .copied()
                        .collect::<Vec<_>>();

                    let ref_use = deps.require_dep::<TyPureEnc>(self_decomp.ty)?.expect_immref();
                    let target_snap_indirect = ref_use.value_access.call()(ref_snap);
                    let target_snap_direct = im_state.get_snap_idn.call()(target_tyval, state, target_addr);
                    axioms.push(
                        vcx.mk_domain_axiom(
                            vir::vir_format_identifier!(vcx, "{}_target_snap", self_name),
                            vcx.mk_forall_expr(
                                vcx.alloc_slice(&qvars[..]),
                                &[],
                                vcx.mk_eq_expr(target_snap_indirect, target_snap_direct)
                            ),
                        ),
                    );
                }
                TySpecifics::MutRef(data) => {
                    deps.emit_output_ref(*task_key, ImTyEncRef {
                        specifics: ImTySpecifics::Other,
                    })?;

                    // TODO we are missing the axioms that link the snapshot of a mutref to the snapshot of its target

                    let params = deps.require_dep::<GenericParamsEnc>(task_key.params)?;
                    let ref_tyval = deps.require_dep::<TyExprEnc>(self_decomp)?;
                    let target_ty = data.referent.decompose(task_key.params);
                    let target_tyval = deps.require_dep::<TyExprEnc>(target_ty)?;
                    let state_decl = vcx.mk_local_decl("s", vir::TYPE_IMSTATE);
                    let state = vcx.mk_local_ex(state_decl);
                    let addr_decl = vcx.mk_local_decl("l", vir::TYPE_REF);
                    let addr = vcx.mk_local_ex(addr_decl);
                    let idx_decl = vcx.mk_local_decl("p", vir::TYPE_INT);
                    let idx = vcx.mk_local_ex(idx_decl);
                    let self_caster =
                        deps.require_dep::<GArgsCastEnc<Pure>>(Some(RustTyNormalized {
                            param: RustTyDecomposition::param(),
                            concrete: self_decomp,
                        }))?;
                    let ref_snap = self_caster
                        .cast_to_caller_ctx(
                            im_state.get_snap_idn.call()(ref_tyval, state, addr).upcast_ty(),
                        )
                        .downcast_ty();
                    let ref_use = deps.require_dep::<TyUsePureEnc>(self_decomp)?.expect_mutref();
                    let target_addr = ref_use.deref_access(ref_snap);
                    let exclusive = im_caps.exclusive_idn.call()(ref_tyval, state, idx, addr);
                    let shared = im_caps.shared_idn.call()(ref_tyval, state, idx, addr);
                    let target_exclusive =
                        im_caps.exclusive_idn.call()(target_tyval, state, idx, target_addr);
                    let target_shared =
                        im_caps.shared_idn.call()(target_tyval, state, idx, target_addr);
                    let qvars = params
                        .ty_decls()
                        .as_dyn()
                        .iter()
                        .chain(params.const_decls().as_dyn().iter())
                        .chain([state_decl.as_dyn(), addr_decl.as_dyn(), idx_decl.as_dyn()].iter())
                        .copied()
                        .collect::<Vec<_>>();

                    // exclusive capability to a mutable reference implies exclusive capability to its target
                    axioms.push(
                        vcx.mk_domain_axiom(
                            vir::vir_format_identifier!(vcx, "{}_exclusive_target", self_name),
                            vcx.mk_forall_expr(
                                vcx.alloc_slice(&qvars[..]),
                                &[],
                                vcx.mk_bin_op_expr(
                                    vir::BinOpKind::Implies,
                                    exclusive,
                                    target_exclusive,
                                )
                                .downcast_ty(),
                            ),
                        ),
                    );
                    // shared capability to a mutable reference implies shared capability to its target
                    axioms.push(
                        vcx.mk_domain_axiom(
                            vir::vir_format_identifier!(vcx, "{}_shared_target", self_name),
                            vcx.mk_forall_expr(
                                vcx.alloc_slice(&qvars[..]),
                                &[],
                                vcx.mk_bin_op_expr(vir::BinOpKind::Implies, shared, target_shared)
                                    .downcast_ty(),
                            ),
                        ),
                    );

                    let qvars = params
                        .ty_decls()
                        .as_dyn()
                        .iter()
                        .chain(params.const_decls().as_dyn().iter())
                        .chain([state_decl.as_dyn(), addr_decl.as_dyn()].iter())
                        .copied()
                        .collect::<Vec<_>>();

                    // TODO do we need a rep-equality axiom for mutrefs?
                    let ref_use = deps.require_dep::<TyPureEnc>(self_decomp.ty)?.expect_mutref();
                    let target_snap_indirect = ref_use.value_access.call()(ref_snap);
                    let target_snap_direct = im_state.get_snap_idn.call()(target_tyval, state, target_addr);
                    axioms.push(
                        vcx.mk_domain_axiom(
                            vir::vir_format_identifier!(vcx, "{}_target_snap", self_name),
                            vcx.mk_forall_expr(
                                vcx.alloc_slice(&qvars[..]),
                                &[],
                                vcx.mk_eq_expr(target_snap_indirect, target_snap_direct)
                            ),
                        ),
                    );
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
                        let capabilities =
                            with_type_im_spec(def_id, |_, capabilities| Vec::from(capabilities));
                        // TODO encode capability axioms
                        // TODO encode non-aliasing axiom (we can maybe skip non-aliasing between abstract & public fields)
                        //
                        // TODO what checks do we assume have already occured for the condition?
                        // - if we have the pre-parser generate a dummy function for each condition, then well-definedness
                        //   is already checked
                        //
                        // Encoding strategy for capability annotatations
                        //
                        // conditions must be:
                        // - well-defined and stable (with pre-condition `true` and no locations modifiable)
                        //
                        // once we have established well-definedness, we can treat the condition as
                        // a total function of the `self` snapshot and the program state. (like a pre-condition)
                        // NOTE this means there is a relatively easy way to make Prusti do this check,
                        // by encoding the condition as a method with no pre-condition or modifies-clause
                        //
                        // NOTE this may be something good to note in the paper, that conditions must be total
                        //
                        // in order for a condition to be stable, the current state must imply that
                        // each location in its frame is stable_read. In determining whether this is
                        // the case, we may assume the RHS of the implication
                        //
                        //

                        // NOTE: At this point we assume that the well-definedness of capable! annotations has been checked.
                        // This is done by generating a dummy method in the preparser stage which includes both the side-condition
                        // and address calculation in the pre-condition of a function.
                        for (cap_idx, cap_spec) in capabilities.into_iter().enumerate() {
                            let CapabilitySpecification {
                                side_conditions,
                                addr_projection,
                                capability,
                                if_exclusive,
                            } = cap_spec;

                            // TODO for each capable! annotation, do a total encoding of its condition and address
                            // also determine its frame (the conjunction of the frames of the condition and address)

                            let cond_def_id = side_conditions.to_def_id();
                            let aloc_def_id = addr_projection.to_def_id();
                            let aloc_sig = RustSignature::new(aloc_def_id);
                            // These should be identical to the gparams of the condition def
                            let params = aloc_sig.gparams;
                            // are these the gargs we really want? what if we have trait bounds?
                            let gargs = params.identity_args();
                            let generics = deps.require_dep::<GenericParamsEnc>(params)?;

                            let addr_decl = vcx.mk_local_decl("l", vir::TYPE_REF);
                            let addr_ex = vcx.mk_local_ex(addr_decl);
                            let idx_decl = vcx.mk_local_decl("i", vir::TYPE_INT);
                            let idx_ex = vcx.mk_local_ex(idx_decl);
                            let state_ex = vcx.mk_local_ex(im_state.state_decl);

                            let self_ref_ty = aloc_sig.inputs[0].decompose(params);
                            let ref_data = self_ref_ty.ty.ref_data().unwrap();
                            let self_target_ty =
                                ref_data.referent.decompose_normalize(self_ref_ty.args);

                            let self_target_tyval =
                                deps.require_dep::<TyExprEnc>(self_target_ty)?;

                            let im_caps = deps.require_ref::<ImCapEnc>(())?;
                            let lhs_capbility_ex = (if if_exclusive {
                                im_caps.exclusive_idn
                            } else {
                                im_caps.shared_idn
                            })
                            .call()(
                                self_target_tyval, state_ex, idx_ex, addr_ex
                            );

                            let sig = vcx
                                .tcx()
                                .fn_sig(cond_def_id)
                                .instantiate(vcx.tcx(), gargs.args())
                                .skip_binder();
                            let self_metadata_ty =
                                sig.inputs()[0].pointee_metadata_ty_or_projection(vcx.tcx());
                            let self_metadata_ty = gargs.context().normalize(self_metadata_ty);
                            let metadata = deps
                                .require_dep::<TyUsePureEnc>(RustTyDecomposition::from_ty(
                                    self_metadata_ty,
                                    gargs.context(),
                                ))?
                                .zst_to_snap()
                                .ok_or_else(|| {
                                    EncodeFullError::DependencyError(vec![(
                                        ImTyEnc::ENCODER_NAME,
                                        "Interior-mutability reasoning for unsized types is not supported".to_string(),
                                        vec![vcx.tcx().def_span(cond_def_id)],
                                    )])
                                })?;

                            let self_target_snap =
                                im_state.get_snap_idn.call()(self_target_tyval, state_ex, addr_ex);
                            let self_ref_pure = deps
                                .require_dep::<TyUsePureEnc>(self_ref_ty)?
                                .expect_immref();

                            let self_ref_snap = self_ref_pure.prim_to_snap(
                                addr_ex,
                                metadata.upcast_ty(),
                                self_ref_pure.mk_inner_concrete(
                                    im_state.get_snap_idn.call()(
                                        self_target_tyval,
                                        state_ex,
                                        addr_ex,
                                    )
                                    .upcast_ty(),
                                ),
                            );

                            let local_defs =
                                deps.require_dep::<MirLocalDefEnc>(MirLocalDefEncTask::Local {
                                    def_id: aloc_def_id,
                                    all_locals: true,
                                })?;

                            let mut snap_map = vcx.alloc(
                                [(mir::Local::from(1 as usize), self_ref_snap.upcast_ty())]
                                    .into_iter()
                                    .collect(),
                            );

                            let cond_enc = deps.require_dep::<MirPureEnc>(MirPureEncTask {
                                encoding_depth: 0,
                                kind: PureKind::Pure,
                                parent_def_id: cond_def_id,
                                gargs,
                                is_partial: false,
                                is_unstable: true,
                            })?;
                            let cond_ex = cond_enc.expr.reify(
                                vcx,
                                (
                                    cond_def_id,
                                    snap_map,
                                    None,
                                    vir::OldLabel::None,
                                    Some(state_ex),
                                ),
                            );

                            let aloc_enc = deps.require_dep::<MirPureEnc>(MirPureEncTask {
                                encoding_depth: 0,
                                kind: PureKind::Pure,
                                parent_def_id: aloc_def_id,
                                gargs,
                                is_partial: false,
                                is_unstable: true,
                            })?;
                            let aloc_ex = aloc_enc.expr.reify(
                                vcx,
                                (
                                    aloc_def_id,
                                    snap_map,
                                    None,
                                    vir::OldLabel::None,
                                    Some(state_ex),
                                ),
                            );

                            let aloc_ty = aloc_sig.output.decompose(params);
                            let aloc_ty_use = deps.require_dep::<TyUsePureEnc>(aloc_ty)?;
                            let aloc_tmp = vcx.mk_local_decl("aloc", aloc_ty_use.snapshot);
                            let aloc_tmp_ex = vcx.mk_local_ex(aloc_tmp).downcast_ty();
                            let aloc_ty_use = aloc_ty_use.expect_addr();
                            let aloc_addr = aloc_ty_use.addr_access(aloc_tmp_ex);
                            let aloc_tyval = aloc_ty_use.type_access(aloc_tmp_ex);

                            let rhs_capability_ex = vcx.mk_let_expr(
                                aloc_tmp,
                                aloc_ex,
                                (match capability {
                                    CapabilityKind::Local => {
                                        let parent_loc = im_state.mk_aloc_psnap_idn.call()(
                                            self_target_tyval,
                                            addr_ex,
                                        );
                                        im_caps.local_write_idn.call()(
                                            aloc_tyval, state_ex, idx_ex, aloc_addr, parent_loc,
                                        )
                                    }
                                    CapabilityKind::Exclusive => im_caps.exclusive_idn.call()(
                                        aloc_tyval, state_ex, idx_ex, aloc_addr,
                                    ),
                                    CapabilityKind::Shared => im_caps.shared_idn.call()(
                                        aloc_tyval, state_ex, idx_ex, aloc_addr,
                                    ),
                                    CapabilityKind::Write => im_caps.write_idn.call()(
                                        aloc_tyval, state_ex, idx_ex, aloc_addr,
                                    ),
                                    CapabilityKind::Read => im_caps.read_idn.call()(
                                        aloc_tyval, state_ex, idx_ex, aloc_addr,
                                    ),
                                }),
                            );

                            let cond_frame = cond_enc.frame.reify(
                                vcx,
                                (
                                    cond_def_id,
                                    snap_map,
                                    None,
                                    vir::OldLabel::None,
                                    Some(state_ex),
                                ),
                            );
                            let aloc_frame = aloc_enc.frame.reify(
                                vcx,
                                (
                                    aloc_def_id,
                                    snap_map,
                                    None,
                                    vir::OldLabel::None,
                                    Some(state_ex),
                                ),
                            );
                            let frame = vcx
                                .mk_anyset_op_expr(
                                    vir::CollectionBinOpKind::Union,
                                    cond_frame,
                                    aloc_frame,
                                )
                                .downcast_ty();

                            let frame_ty_decl = vcx.mk_local_decl("t_frame", vir::TYPE_TYVAL);
                            let frame_ty = vcx.mk_local_ex(frame_ty_decl);
                            let frame_ref_decl = vcx.mk_local_decl("l_frame", vir::TYPE_REF);
                            let frame_ref = vcx.mk_local_ex(frame_ref_decl);
                            let frame_psnap =
                                im_state.mk_aloc_psnap_idn.call()(frame_ty, frame_ref);
                            let frame_stable =
                                im_caps.stable_read_idn.call()(frame_ty, state_ex, frame_ref);
                            let frame_stable = vcx.mk_forall_expr(
                                vcx.alloc_slice(&[frame_ty_decl.as_dyn(), frame_ref_decl.as_dyn()]),
                                &[],
                                vcx.mk_bin_op_expr(
                                    vir::BinOpKind::Implies,
                                    vcx.mk_set_in_expr(frame_psnap, frame),
                                    frame_stable,
                                )
                                .downcast_ty(),
                            );

                            let mut qvars = generics
                                .ty_decls()
                                .iter()
                                .map(|decl| (*decl).as_dyn())
                                .collect::<Vec<_>>();
                            qvars
                                .extend(generics.const_decls().iter().map(|decl| (*decl).as_dyn()));
                            qvars.extend([
                                im_state.state_decl.as_dyn(),
                                addr_decl.as_dyn(),
                                idx_decl.as_dyn(),
                            ]);
                            let axiom_body = vcx
                                .mk_bin_op_expr(
                                    vir::BinOpKind::Implies,
                                    vcx.mk_bin_op_expr(
                                        vir::BinOpKind::And,
                                        lhs_capbility_ex,
                                        vcx.mk_bin_op_expr(
                                            vir::BinOpKind::Implies,
                                            rhs_capability_ex,
                                            frame_stable,
                                        )
                                        .downcast_ty(),
                                    )
                                    .downcast_ty(),
                                    rhs_capability_ex,
                                )
                                .downcast_ty();
                            axioms.push(vcx.mk_domain_axiom(
                                vir::vir_format_identifier!(
                                    vcx,
                                    "{}_{}_capability",
                                    task_key.name(),
                                    cap_idx,
                                ),
                                vcx.mk_forall_expr(
                                    vcx.alloc_slice(&qvars),
                                    vcx.alloc_slice(&[vcx.mk_trigger(&[lhs_capbility_ex])]),
                                    axiom_body,
                                ),
                            ));

                            // TODO lhs_capability &&
                            // (capability_ex => forall i in <frame> :: stable_read(i)) => capability_ex
                            // trigger would be lhs_capability?
                        }
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

                    let addr_decl = vcx.mk_local_decl("l", vir::TYPE_REF);
                    let addr_ex = vcx.mk_local_ex(addr_decl);
                    let ty_decl = vcx.mk_local_decl("t", vir::TYPE_TYVAL);
                    let ty_ex = vcx.mk_local_ex(ty_decl);
                    axioms.push(
                        vcx.mk_domain_axiom(
                            vir::vir_format_identifier!(
                                vcx,
                                "{}_mk_aloc_psnap_defn",
                                task_key.name()
                            ),
                            vcx.mk_forall_expr(
                                vcx.alloc_slice(&[addr_decl.as_dyn(), ty_decl.as_dyn()]),
                                &[],
                                vcx.mk_eq_expr(
                                    im_state.mk_aloc_psnap_idn.call()(ty_ex, addr_ex),
                                    self_caster.cast_to_callee_ctx(addrdyn.mk_addr.call()(addr_ex, ty_ex).upcast_ty()).downcast_ty(),
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
