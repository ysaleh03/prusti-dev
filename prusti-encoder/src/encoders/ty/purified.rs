// TODO: this lint is something we should fix; to address there should probably
//   be an indirection in error storage somewhere, maybe even in `task-encoder`?
#![allow(clippy::result_large_err)]
use prusti_rustc_interface::{
    abi,
    middle::ty::{self, IntTy, TyKind, UintTy},
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{AdtDestructor, FunctionIdn};

use crate::encoders::{Purified, ty::builder::TyBuilder};

use super::{RustTy, ViperTyDatas, data::*, interpretation::float::FloatDomain};

pub(crate) type PurifiedTyDatas = ViperTyDatas<Purified>;

impl<'vir> TyDatas<'vir> for PurifiedTyDatas {
    type TyData = TyPurifiedRef<'vir>;
    type OpaqueData = TyPurifiedOpaqueData<'vir>;
    type PrimitiveData = TyPurifiedPrimData<'vir>;
    type ImmRefData = TyPurifiedImmRefData<'vir>;
    type MutRefData = TyPurifiedMutRefData<'vir>;
    type FieldData = TyPurifiedFieldData<'vir>;
    type StructData = TyPurifiedStructData<'vir>;
    type VariantData = TyPurifiedVariantData<'vir>;
    type EnumData = TyPurifiedEnumData<'vir>;
}

pub type TyPurified<'vir> = Ty<'vir, PurifiedTyDatas>;
pub type TyPurifiedParam<'vir> = <PurifiedTyDatas as TyDatas<'vir>>::ParamData;
pub type TyPurifiedOpaque<'vir> = <PurifiedTyDatas as TyDatas<'vir>>::OpaqueData;
pub type TyPurifiedPrimitive<'vir> = <PurifiedTyDatas as TyDatas<'vir>>::PrimitiveData;
pub type TyPurifiedImmRef<'vir> = <PurifiedTyDatas as TyDatas<'vir>>::ImmRefData;
pub type TyPurifiedMutRef<'vir> = <PurifiedTyDatas as TyDatas<'vir>>::MutRefData;

#[derive(Debug, Clone, Copy)]
pub struct TyPurifiedOpaqueData<'vir> {
    /// Some arbitrary value of this type. Should probably be removed
    /// eventually, but used for now in e.g. the str-const encoding.
    pub arbitrary: FunctionIdn<'vir, (), vir::CSnap>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyPurifiedPrimData<'vir> {
    pub prim_type: vir::TypePrim<'vir>,
    /// Viper primitive value as argument. Returns domain.
    pub prim_to_snap: FunctionIdn<'vir, vir::Prim, vir::CSnap>,
    pub kind: TyPurifiedPrimDataKind<'vir>,
}

#[derive(Debug, Clone, Copy)]
pub enum TyPurifiedPrimDataKind<'vir> {
    Native(TyPurifiedPrimDataNative<'vir>),
    Float(FloatDomain<'vir>),
}

#[derive(Debug, Clone, Copy)]
pub struct TyPurifiedPrimDataNative<'vir> {
    /// Snapshot of self as argument. Returns Viper primitive value.
    pub snap_to_prim: FunctionIdn<'vir, vir::CSnap, vir::Prim>,
}

impl<'vir> TyPurifiedPrimData<'vir> {
    pub fn expect_native(&self) -> &TyPurifiedPrimDataNative<'vir> {
        match &self.kind {
            TyPurifiedPrimDataKind::Native(native) => native,
            _ => panic!(),
        }
    }
}

impl<'vir, D: TyDatas<'vir, PrimitiveData = TyPurifiedPrimData<'vir>>> TyData<'vir, D> {
    pub fn expect_purified_native(&self) -> &TyPurifiedPrimDataNative<'vir> {
        self.expect_primitive().expect_native()
    }

    pub fn expect_purified_float(&self) -> &FloatDomain<'vir> {
        match &self.expect_primitive().kind {
            TyPurifiedPrimDataKind::Float(fl) => fl,
            _ => panic!(),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct TyPurifiedImmRefData<'vir> {
    /// Construct domain from a parameter value.
    pub(super) value_to_snap: FunctionIdn<'vir, vir::PSnap, vir::CSnap>,
    /// Function to access the snapshot value.
    pub(super) value_access: AdtDestructor<'vir, vir::CSnap, vir::PSnap>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyPurifiedMutRefData<'vir> {
    /// Construct domain from a parameter value.
    pub(super) value_to_snap: FunctionIdn<'vir, vir::PSnap, vir::CSnap>,
    /// Function to access the snapshot value.
    pub(super) value_access: AdtDestructor<'vir, vir::CSnap, vir::PSnap>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyPurifiedStructData<'vir> {
    /// Construct domain from snapshots of fields or for primitive types
    /// from the single Viper primitive value.
    pub(super) field_snaps_to_snap: FunctionIdn<'vir, vir::ManySnap, vir::CSnap>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyPurifiedFieldData<'vir> {
    pub(super) read: AdtDestructor<'vir, vir::CSnap, vir::Snap>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyPurifiedEnumData<'vir> {
    #[allow(dead_code)]
    pub(super) discr_ty: vir::TypeSnap<'vir>,
    #[allow(dead_code)]
    pub(super) discr_prim: TyPurifiedPrimitive<'vir>,
    pub(super) snap_to_discr_snap: FunctionIdn<'vir, vir::CSnap, vir::CSnap>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyPurifiedVariantData<'vir> {
    pub discr: vir::ExprCSnap<'vir>,
}

/// You probably never want to use this, use `TyUsePurifiedEnc` instead.
pub(super) type TyPurifiedEnc = super::TyEnc<Purified>;

#[derive(Debug, Clone, Copy)]
pub struct TyPurifiedRef<'vir> {
    pub domain: vir::DomainIdnSnap<'vir>,
    pub unreachable_to_snap: FunctionIdn<'vir, vir::ManyTyVal, vir::Snap>,
}

impl<'vir> task_encoder::OutputRefAny for TyPurifiedRef<'vir> {}

#[derive(Debug, Clone)]
pub struct TyPurifiedEncLocal<'vir> {
    pub unreachable_to_snap: vir::Function<'vir>,
    pub kind: TyPurifiedEncLocalKind<'vir>,
}

#[derive(Debug, Clone, Copy)]
pub enum TyPurifiedEncLocalKind<'vir> {
    Domain {
        domain: vir::Domain<'vir>,
        // functions: Vec<vir::Function<'vir>>,
    },
    Adt {
        adt: vir::Adt<'vir>,
        domain: vir::Domain<'vir>,
        discr_fn: Option<vir::Function<'vir>>,
    },
}

#[derive(Clone, Debug)]
pub enum TyPurifiedEncError {}

impl TaskEncoder for TyPurifiedEnc {
    task_encoder::encoder_cache!(TyPurifiedEnc);
    type TaskDescription<'vir> = RustTy<'vir>;

    type OutputRef<'vir> = TyPurifiedRef<'vir>;
    type OutputFullDependency<'vir> = TyPurified<'vir>;

    /// A domain is not encoded here for Param types, the relevant domains are
    /// encoded in [`GenericEnc`]. The reason we do not encode the domain for
    /// `Param` types here is because we don't want [`GenericEnc`] to depend on
    /// this encoder: doing so would create a cyclic dependency.
    type OutputFullLocal<'vir> = TyPurifiedEncLocal<'vir>;

    type EncodingError = TyPurifiedEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let mut builder = TyBuilder::<Purified>::new(deps, vcx, task_key);
            let output_ref = builder.output_ref();
            deps.emit_output_ref(*task_key, output_ref)?;

            let specifics = match &task_key.specifics {
                TySpecifics::Param(param) => {
                    let builder = builder.set_domain_builder();
                    TySpecifics::Param(super::kinds::param::ty_purified(param, deps, builder)?)
                }
                TySpecifics::Opaque(opaque) => {
                    let builder = builder.set_domain_builder();
                    TySpecifics::Opaque(super::kinds::opaque::ty_purified(opaque, deps, builder)?)
                }
                TySpecifics::Primitive(prim) => {
                    let builder = builder.set_domain_builder();
                    TySpecifics::Primitive(super::kinds::primitive::ty_purified(
                        vcx, prim, deps, builder,
                    )?)
                }
                TySpecifics::ImmRef(immref) => {
                    let domain = builder.set_adt_builder();
                    TySpecifics::ImmRef(super::kinds::immref::ty_purified(
                        task_key, immref, deps, domain,
                    )?)
                }
                TySpecifics::MutRef(mutref) => {
                    let domain = builder.set_adt_builder();
                    TySpecifics::MutRef(super::kinds::mutref::ty_purified(
                        task_key, mutref, deps, domain,
                    )?)
                }
                TySpecifics::StructLike(structlike) => {
                    let domain = builder.set_adt_builder();
                    TySpecifics::StructLike(super::kinds::structlike::ty_purified(
                        task_key, structlike, deps, domain,
                    )?)
                }
                TySpecifics::EnumLike(enumlike) => {
                    let domain = builder.set_adt_builder();
                    TySpecifics::EnumLike(super::kinds::enumlike::ty_purified(
                        task_key, enumlike, deps, domain,
                    )?)
                }
            };
            let output = TyData::new(output_ref, task_key.inhabited, specifics).alloc();
            Ok((builder.build(), output))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in TyPurifiedEnc::all_outputs_local_no_errors() {
            program.add_function(output.unreachable_to_snap);
            match output.kind {
                TyPurifiedEncLocalKind::Domain { domain } => program.add_domain(domain),
                TyPurifiedEncLocalKind::Adt {
                    adt,
                    domain,
                    discr_fn,
                } => {
                    program.add_adt(adt);
                    program.add_domain(domain);
                    if let Some(discr_fn) = discr_fn {
                        program.add_function(discr_fn);
                    }
                }
            }
        }
    }
}

impl<'vir> TyPurifiedPrimData<'vir> {
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
