// TODO: this lint is something we should fix; to address there should probably
//   be an indirection in error storage somewhere, maybe even in `task-encoder`?
#![allow(clippy::result_large_err)]
use crate::encoders::{Pure, ty::builder::TyBuilder};
use prusti_rustc_interface::{
    abi,
    middle::ty::{self, IntTy, TyKind, UintTy},
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{AdtDestructor, FunctionIdn};

use super::{RustTy, ViperTyDatas, data::*, interpretation::float::FloatDomain};

pub(crate) type PureTyDatas = ViperTyDatas<Pure>;

impl<'vir> TyDatas<'vir> for PureTyDatas {
    type TyData = TyPureRef<'vir>;
    type OpaqueData = TyPureOpaqueData<'vir>;
    type PrimitiveData = TyPurePrimData<'vir>;
    type ImmRefData = TyPureImmRefData<'vir>;
    type MutRefData = TyPureMutRefData<'vir>;
    type FieldData = TyPureFieldData<'vir>;
    type StructData = TyPureStructData<'vir>;
    type VariantData = TyPureVariantData<'vir>;
    type EnumData = TyPureEnumData<'vir>;
}

pub type TyPure<'vir> = Ty<'vir, PureTyDatas>;
pub type TyPureParam<'vir> = <PureTyDatas as TyDatas<'vir>>::ParamData;
pub type TyPureOpaque<'vir> = <PureTyDatas as TyDatas<'vir>>::OpaqueData;
pub type TyPurePrimitive<'vir> = <PureTyDatas as TyDatas<'vir>>::PrimitiveData;
pub type TyPureImmRef<'vir> = <PureTyDatas as TyDatas<'vir>>::ImmRefData;
pub type TyPureMutRef<'vir> = <PureTyDatas as TyDatas<'vir>>::MutRefData;

#[derive(Debug, Clone, Copy)]
pub struct TyPureOpaqueData<'vir> {
    /// Some arbitrary value of this type. Should probably be removed
    /// eventually, but used for now in e.g. the str-const encoding.
    pub arbitrary: FunctionIdn<'vir, (), vir::CSnap>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyPurePrimData<'vir> {
    pub prim_type: vir::TypePrim<'vir>,
    /// Viper primitive value as argument. Returns domain.
    pub prim_to_snap: FunctionIdn<'vir, vir::Prim, vir::CSnap>,
    pub kind: TyPurePrimDataKind<'vir>,
}

#[derive(Debug, Clone, Copy)]
pub enum TyPurePrimDataKind<'vir> {
    Native(TyPurePrimDataNative<'vir>),
    Float(FloatDomain<'vir>),
}

#[derive(Debug, Clone, Copy)]
pub struct TyPurePrimDataNative<'vir> {
    /// Snapshot of self as argument. Returns Viper primitive value.
    pub snap_to_prim: FunctionIdn<'vir, vir::CSnap, vir::Prim>,
}

impl<'vir> TyPurePrimData<'vir> {
    pub fn expect_native(&self) -> &TyPurePrimDataNative<'vir> {
        match &self.kind {
            TyPurePrimDataKind::Native(native) => native,
            _ => panic!(),
        }
    }
}

impl<'vir, D: TyDatas<'vir, PrimitiveData = TyPurePrimData<'vir>>> TyData<'vir, D> {
    pub fn expect_pure_native(&self) -> &TyPurePrimDataNative<'vir> {
        self.expect_primitive().expect_native()
    }

    pub fn expect_pure_float(&self) -> &FloatDomain<'vir> {
        match &self.expect_primitive().kind {
            TyPurePrimDataKind::Float(fl) => fl,
            _ => panic!(),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct TyPureImmRefData<'vir> {
    /// Construct domain from a `Ref` value.
    pub(super) prim_to_snap: FunctionIdn<'vir, (vir::Ref, vir::PSnap), vir::CSnap>,
    /// Function to access the referee.
    pub(super) deref_access: AdtDestructor<'vir, vir::CSnap, vir::Ref>,
    /// Function to access the snapshot value.
    pub(super) value_access: AdtDestructor<'vir, vir::CSnap, vir::PSnap>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyPureMutRefData<'vir> {
    /// Construct domain from a `Ref` value.
    pub(super) prim_to_snap: FunctionIdn<'vir, vir::Ref, vir::CSnap>,
    /// Function to access the referee.
    pub(super) deref_access: AdtDestructor<'vir, vir::CSnap, vir::Ref>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyPureStructData<'vir> {
    /// Construct domain from snapshots of fields or for primitive types
    /// from the single Viper primitive value.
    pub(super) field_snaps_to_snap: FunctionIdn<'vir, vir::ManySnap, vir::CSnap>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyPureFieldData<'vir> {
    pub(super) read: AdtDestructor<'vir, vir::CSnap, vir::Snap>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyPureEnumData<'vir> {
    #[allow(dead_code)]
    pub(super) discr_ty: vir::TypeSnap<'vir>,
    #[allow(dead_code)]
    pub(super) discr_prim: TyPurePrimitive<'vir>,
    pub(super) snap_to_discr_snap: FunctionIdn<'vir, vir::CSnap, vir::CSnap>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyPureVariantData<'vir> {
    pub discr: vir::ExprCSnap<'vir>,
}

/// You probably never want to use this, use `TyUsePureEnc` instead.
/// Note: there should never be a dependency on `TyImpureEnc` inside this
/// encoder!
pub(super) type TyPureEnc = super::TyEnc<Pure>;

#[derive(Debug, Clone, Copy)]
pub struct TyPureRef<'vir> {
    pub domain: vir::DomainIdnSnap<'vir>,
    pub unreachable_to_snap: FunctionIdn<'vir, vir::ManyTyVal, vir::Snap>,
}

impl<'vir> task_encoder::OutputRefAny for TyPureRef<'vir> {}

#[derive(Debug, Clone, Copy)]
pub struct TyPureEncLocal<'vir> {
    pub unreachable_to_snap: vir::Function<'vir>,
    pub kind: TyPureEncLocalKind<'vir>,
}

#[derive(Debug, Clone, Copy)]
pub enum TyPureEncLocalKind<'vir> {
    Domain {
        domain: vir::Domain<'vir>,
        // functions: Vec<vir::Function<'vir>>,
    },
    Adt {
        adt: vir::Adt<'vir>,
        discr_fn: Option<vir::Function<'vir>>,
    },
}

#[derive(Debug, Clone, Copy)]
pub enum TyPureEncError {}

impl TaskEncoder for TyPureEnc {
    task_encoder::encoder_cache!(TyPureEnc);
    type TaskDescription<'vir> = RustTy<'vir>;

    type OutputRef<'vir> = TyPureRef<'vir>;
    type OutputFullDependency<'vir> = TyPure<'vir>;

    /// A domain is not encoded here for Param types, the relevant domains are
    /// encoded in [`GenericEnc`]. The reason we do not encode the domain for
    /// `Param` types here is because we don't want [`GenericEnc`] to depend on
    /// this encoder: doing so would create a cyclic dependency.
    type OutputFullLocal<'vir> = TyPureEncLocal<'vir>;

    type EncodingError = TyPureEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let mut builder = TyBuilder::<Pure>::new(deps, vcx, task_key);
            let output_ref = builder.output_ref();
            deps.emit_output_ref(*task_key, output_ref)?;

            let specifics = match &task_key.specifics {
                TySpecifics::Param(param) => {
                    let builder = builder.set_domain_builder();
                    TySpecifics::Param(super::kinds::param::ty_pure(param, deps, builder)?)
                }
                TySpecifics::Opaque(opaque) => {
                    let builder = builder.set_domain_builder();
                    TySpecifics::Opaque(super::kinds::opaque::ty_pure(opaque, deps, builder)?)
                }
                TySpecifics::Primitive(prim) => {
                    let builder = builder.set_domain_builder();
                    TySpecifics::Primitive(super::kinds::primitive::ty_pure(
                        vcx, prim, deps, builder,
                    )?)
                }
                TySpecifics::ImmRef(immref) => {
                    let builder = builder.set_adt_builder();
                    TySpecifics::ImmRef(super::kinds::immref::ty_pure(immref, deps, builder)?)
                }
                TySpecifics::MutRef(_) => {
                    let builder = builder.set_adt_builder();
                    TySpecifics::MutRef(super::kinds::mutref::ty_pure(builder)?)
                }
                TySpecifics::StructLike(structlike) => {
                    let builder = builder.set_adt_builder();
                    TySpecifics::StructLike(super::kinds::structlike::ty_pure(
                        task_key, structlike, deps, builder,
                    )?)
                }
                TySpecifics::EnumLike(enumlike) => {
                    let builder = builder.set_adt_builder();
                    TySpecifics::EnumLike(super::kinds::enumlike::ty_pure(
                        task_key, enumlike, deps, builder,
                    )?)
                }
            };
            let output = TyData::new(output_ref, task_key.inhabited, specifics).alloc();
            Ok((builder.build(), output))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in TyPureEnc::all_outputs_local_no_errors() {
            program.add_function(output.unreachable_to_snap);
            match output.kind {
                TyPureEncLocalKind::Domain { domain } => program.add_domain(domain),
                TyPureEncLocalKind::Adt { adt, discr_fn } => {
                    program.add_adt(adt);
                    if let Some(discr_fn) = discr_fn {
                        program.add_function(discr_fn);
                    }
                }
            }
        }
    }
}

impl<'vir> TyPurePrimData<'vir> {
    pub fn expr_from_bits(&self, ty: ty::Ty<'vir>, value: u128) -> vir::ExprPrim<'vir> {
        match self.prim_type.kind() {
            vir::TypeKind::Bool => {
                vir::with_vcx(|vcx| vcx.mk_const_expr(vir::ConstData::Bool(value != 0)))
            }
            vir::TypeKind::Int => {
                let (bit_width, signed) = match ty.kind() {
                    TyKind::Int(IntTy::Isize) => ((std::mem::size_of::<isize>() * 8) as u64, true),
                    TyKind::Int(ty) => (ty.bit_width().unwrap(), true),
                    TyKind::Uint(UintTy::Usize) => {
                        ((std::mem::size_of::<usize>() * 8) as u64, true)
                    }
                    TyKind::Uint(ty) => (ty.bit_width().unwrap(), false),
                    TyKind::Char => (32, false),
                    // The float prim_to_snap takes the raw bits as an unsigned integer.
                    TyKind::Float(..) => (0, false),
                    kind => unreachable!("{kind:?}"),
                };
                let size = abi::Size::from_bits(bit_width);
                let negative_value = if signed {
                    let value = size.sign_extend(value);
                    Some(value).filter(|value| value.is_negative())
                } else {
                    None
                };
                match negative_value {
                    Some(value) => vir::with_vcx(|vcx| {
                        let value = vcx.mk_const_expr(vir::ConstData::Int(value.unsigned_abs()));
                        vcx.mk_unary_op_expr(vir::UnOpKind::Neg, value)
                    }),
                    None => vir::with_vcx(|vcx| vcx.mk_const_expr(vir::ConstData::Int(value))),
                }
            }
            ref k => unreachable!("{k:?}"),
        }
    }
}
