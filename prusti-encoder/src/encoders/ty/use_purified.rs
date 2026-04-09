use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, FunctionIdn};

use crate::encoders::{
    Pure, Purified,
    ty::{
        LazyRustTy, RustTyDatas,
        generics::{GArgs, GArgsCastEnc, GArgsTyEnc, GParams},
        purified::TyPurifiedRef,
    },
};

use super::{
    TyUseEnc, UseTyDatas,
    data::*,
    generics::{GArgCaster, GArgsTy},
    purified::{PurifiedTyDatas, TyPurifiedEnc},
};

pub(super) type UsePurifiedTyDatas = UseTyDatas<Purified>;

type FieldCaster<'vir> = GArgCaster<'vir, Purified>;

impl<'vir> TyDatas<'vir> for UsePurifiedTyDatas {
    type TyData = TyUsePurifiedRef<'vir>;
    type OpaqueData = <PurifiedTyDatas as TyDatas<'vir>>::OpaqueData;
    type ParamData = <PurifiedTyDatas as TyDatas<'vir>>::ParamData;
    type PrimitiveData = <PurifiedTyDatas as TyDatas<'vir>>::PrimitiveData;
    type ImmRefData = TyUsePurifiedImmRef<'vir>;
    type MutRefData = TyUsePurifiedMutRef<'vir>;
    type FieldData = TyUsePurifiedField<'vir>;
    type StructData = TyUsePurifiedStructData<'vir>;
    type VariantData = <PurifiedTyDatas as TyDatas<'vir>>::VariantData;
    type EnumData = <PurifiedTyDatas as TyDatas<'vir>>::EnumData;
}

pub type TyUsePurified<'vir> = Ty<'vir, UsePurifiedTyDatas>;
pub type TyUsePurifiedStruct<'vir> = StructData<'vir, UsePurifiedTyDatas>;
pub type TyUsePurifiedEnum<'vir> = EnumData<'vir, UsePurifiedTyDatas>;

#[derive(Debug, Clone, Copy)]
pub struct TyUsePurifiedData<'vir> {
    args: GArgsTy<'vir>,
    purified: <PurifiedTyDatas as TyDatas<'vir>>::TyData,
}

#[derive(Debug, Clone, Copy)]
pub struct TyUsePurifiedImmRef<'vir> {
    snap_ty: vir::ExprTyVal<'vir>,
    caster: FieldCaster<'vir>,
    args: GArgsTy<'vir>,
    purified: <PurifiedTyDatas as TyDatas<'vir>>::ImmRefData,
}

#[derive(Debug, Clone, Copy)]
pub struct TyUsePurifiedMutRef<'vir> {
    snap_ty: vir::ExprTyVal<'vir>,
    caster: FieldCaster<'vir>,
    args: GArgsTy<'vir>,
    purified: <PurifiedTyDatas as TyDatas<'vir>>::MutRefData,
}

#[derive(Debug, Clone, Copy)]
pub struct TyUsePurifiedField<'vir> {
    caster: FieldCaster<'vir>,
    purified: <PurifiedTyDatas as TyDatas<'vir>>::FieldData,
}

#[derive(Debug, Clone, Copy)]
pub struct TyUsePurifiedStructData<'vir> {
    #[allow(dead_code)]
    args: GArgsTy<'vir>,
    purified: <PurifiedTyDatas as TyDatas<'vir>>::StructData,
}

#[derive(Debug, Clone, Copy)]
pub struct TyUsePurifiedEnumData<'vir> {
    #[allow(dead_code)]
    args: GArgsTy<'vir>,
    purified: <PurifiedTyDatas as TyDatas<'vir>>::EnumData,
}

/// Encodes a type into the snapshot representation. Takes an arbitrary Rust
/// `Ty` and provides a wrapper around the results of the `DomainEnc` encoder.
/// This wrapper handles all the generic casts required.
pub type TyUsePurifiedEnc = TyUseEnc<Purified>;

#[derive(Debug, Clone, Copy)]
pub struct TyUsePurifiedRef<'vir> {
    pub snapshot: vir::TypeSnap<'vir>,
    args: GArgsTy<'vir>,
    ty_purified_ref: TyPurifiedRef<'vir>,
}

impl<'vir> task_encoder::OutputRefAny for TyUsePurifiedRef<'vir> {}

impl TaskEncoder for TyUsePurifiedEnc {
    task_encoder::encoder_cache!(TyUsePurifiedEnc);

    type TaskDescription<'vir> = super::RustTyDecomposition<'vir>;

    type OutputRef<'vir> = TyUsePurifiedRef<'vir>;
    type OutputFullDependency<'vir> = TyUsePurified<'vir>;

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type EncodingError = ();

    const ENCODER_NAME: &'static str = "purified type encoder";

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let ty_purified_ref = deps.require_ref::<TyPurifiedEnc>(task_key.ty)?;
        let args = deps.require_dep::<GArgsTyEnc>(task_key.args)?;
        let snapshot = (ty_purified_ref.domain)();
        let inner = TyUsePurifiedRef {
            args,
            snapshot,
            ty_purified_ref,
        };
        deps.emit_output_ref(*task_key, inner)?;

        let ty_purified = deps.require_dep::<TyPurifiedEnc>(task_key.ty)?;
        let ty = task_key.ty.zip(ty_purified);
        let inhabited = ty.inhabited;
        let mut walker = TyUsePurifiedWalker::new(deps, task_key.args);
        let specifics = walker.encode_ty(ty);
        let ty_use_purified = TyData::new(inner, inhabited, specifics);
        Ok(((), ty_use_purified.alloc()))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        TyPurifiedEnc::emit_outputs(program)
    }
}

struct TyUsePurifiedWalker<'a, 'vir> {
    deps: &'a mut task_encoder::TaskEncoderDependencies<'vir, TyUsePurifiedEnc>,
    args_t: GArgsTy<'vir>,
    args: GArgs<'vir>,
}

impl<'a, 'vir> TyUsePurifiedWalker<'a, 'vir> {
    fn new(
        deps: &'a mut task_encoder::TaskEncoderDependencies<'vir, TyUsePurifiedEnc>,
        args: GArgs<'vir>,
    ) -> Self {
        let args_t = deps.require_dep::<GArgsTyEnc>(args).unwrap();
        TyUsePurifiedWalker { deps, args_t, args }
    }

    fn encode_ty(
        &mut self,
        ty: TyData<'vir, (RustTyDatas, PurifiedTyDatas)>,
    ) -> TySpecifics<'vir, UsePurifiedTyDatas> {
        match &ty.specifics {
            TySpecifics::Param(..) => TySpecifics::mk_param(()),
            TySpecifics::Opaque(data) => TySpecifics::mk_opaque(*data.1),
            TySpecifics::Primitive(data) => TySpecifics::mk_primitive(*data.1),
            TySpecifics::ImmRef((data, ref_domain)) => {
                let caster = self.encode_normalized(**data, ty.0.params);
                TySpecifics::mk_immref(TyUsePurifiedImmRef {
                    snap_ty: self.args_t.get_ty()[0],
                    caster,
                    args: self.args_t,
                    purified: **ref_domain,
                })
            }
            TySpecifics::MutRef((data, ref_domain)) => {
                let caster = self.encode_normalized(**data, ty.0.params);
                TySpecifics::mk_mutref(TyUsePurifiedMutRef {
                    snap_ty: self.args_t.get_ty()[0],
                    caster,
                    args: self.args_t,
                    purified: **ref_domain,
                })
            }
            TySpecifics::StructLike(data) => {
                TySpecifics::StructLike(self.encode_structlike(data, ty.0.params))
            }
            TySpecifics::EnumLike(data) => {
                TySpecifics::EnumLike(self.encode_enumlike(data, ty.0.params))
            }
        }
    }

    fn encode_normalized(
        &mut self,
        inner: LazyRustTy<'vir>,
        params: GParams<'vir>,
    ) -> FieldCaster<'vir> {
        let normalized = inner.decompose_compare_normalize(params, self.args);
        self.deps
            .require_dep::<GArgsCastEnc<Purified>>(normalized)
            .unwrap()
    }

    fn encode_structlike(
        &mut self,
        data: &StructData<'vir, (RustTyDatas, PurifiedTyDatas)>,
        params: GParams<'vir>,
    ) -> StructData<'vir, UsePurifiedTyDatas> {
        let fields = data
            .fields
            .iter()
            .map(|field| {
                let caster = self.encode_normalized(field.0.ty(), params);
                TyUsePurifiedField {
                    caster,
                    purified: *field.1,
                }
            })
            .collect::<Vec<_>>();
        let inhabited = data.inhabited;
        let data = TyUsePurifiedStructData {
            args: self.args_t,
            purified: *data.1,
        };
        StructData::new(data, inhabited, fields)
    }

    fn encode_enumlike(
        &mut self,
        data: &EnumData<'vir, (RustTyDatas, PurifiedTyDatas)>,
        params: GParams<'vir>,
    ) -> EnumData<'vir, UsePurifiedTyDatas> {
        let variants = data
            .variants
            .iter()
            .map(|variant| {
                let structlike = self.encode_structlike(&variant.inner, params);
                VariantData::new(*variant.1, variant.inhabited, structlike)
            })
            .collect::<Vec<_>>();
        EnumData::new(*data.1, data.inhabited, variants)
    }
}

impl<'vir> TyUsePurifiedData<'vir> {}

impl<'vir> TyUsePurifiedRef<'vir> {
    pub fn unreachable_to_snap<Curr, Next>(&self) -> vir::ExprGenSnap<'vir, Curr, Next> {
        self.ty_purified_ref.unreachable_to_snap.call()(self.args.get_ty())
    }
}

impl<'vir> TyUsePurifiedImmRef<'vir> {
    pub fn value_to_snap<Curr, Next>(
        &self,
        inner: vir::ExprGenSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenCSnap<'vir, Curr, Next> {
        let inner = self.caster.cast_to_callee_ctx(inner);
        self.purified.value_to_snap.call()(inner.downcast_ty())
    }

    pub fn value_access<Curr, Next>(
        &self,
        snap: vir::ExprGenCSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        let value = self.purified.value_access.call()(snap);
        self.caster.cast_to_caller_ctx(value.upcast_ty())
    }
}

impl<'vir> TyUsePurifiedMutRef<'vir> {
    pub fn value_to_snap<Curr, Next>(
        &self,
        inner: vir::ExprGenSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenCSnap<'vir, Curr, Next> {
        let inner = self.caster.cast_to_callee_ctx(inner);
        self.purified.value_to_snap.call()(inner.downcast_ty())
    }

    pub fn value_access<Curr, Next>(
        &self,
        snap: vir::ExprGenCSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        let value = self.purified.value_access.call()(snap);
        self.caster.cast_to_caller_ctx(value.upcast_ty())
    }
}

impl<'vir> TyData<'vir, UsePurifiedTyDatas> {
    // pub fn pack(
    //     &self,
    //     variant: Option<abi::VariantIdx>,
    //     self_snap: vir::ExprSnap<'vir>,
    //     label: Option<vir::OldLabel<'vir>>,
    // ) -> Vec<vir::Stmt<'vir>> {
    //     if let Some(variant) = variant {
    //         return self.expect_variant(variant).inner.pack();
    //     }
    // }
}

impl<'vir> TyUsePurifiedStruct<'vir> {
    pub fn field_snaps_to_snap<Curr, Next>(
        &self,
        mut snaps: Vec<vir::ExprGenSnap<'vir, Curr, Next>>,
    ) -> vir::ExprGenCSnap<'vir, Curr, Next> {
        assert_eq!(snaps.len(), self.fields.len());
        for (snap, field) in snaps.iter_mut().zip(&self.fields) {
            *snap = field.caster.cast_to_callee_ctx(*snap);
        }
        self.purified.field_snaps_to_snap.call()(&snaps)
    }
}

impl<'vir> TyUsePurifiedField<'vir> {
    pub fn field_snap<Curr, Next>(
        &self,
        snap: vir::ExprGenCSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        let res = self.purified.read.call()(snap);
        self.caster.cast_to_caller_ctx(res)
    }
}

impl<'vir> TyUsePurifiedEnum<'vir> {
    pub fn snap_to_discr_snap<Curr, Next>(
        &self,
        snap: vir::ExprGenCSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenCSnap<'vir, Curr, Next> {
        self.snap_to_discr_snap.call()(snap)
    }
}
