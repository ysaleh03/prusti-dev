use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::PredicateIdn;

use crate::encoders::{
    Pure, Purified,
    ty::{
        LazyRustTy, RustTyDatas,
        generics::{GArgs, GArgsCastEnc, GArgsTyEnc, GParams},
    },
};

use super::{
    TyUseEnc, UseTyDatas,
    data::*,
    generics::{GArgCaster, GArgsTy},
    purified::{PurifiedTyDatas, TyPurifiedEnc},
};

pub(super) type UsePurifiedTyDatas = UseTyDatas<Purified>;

type FieldCaster<'vir> = GArgCaster<'vir, Pure>;

impl<'vir> TyDatas<'vir> for UsePurifiedTyDatas {
    type TyData = TyUsePurifiedData<'vir>;
    type PrimitiveData = ();
    type ImmRefData = TyUsePurifiedImmRef<'vir>;
    type MutRefData = TyUsePurifiedMutRef<'vir>;
    type FieldData = TyUsePurifiedField<'vir>;
    type StructData = TyUsePurifiedStructData<'vir>;
    type VariantData = ();
    type EnumData = TyUsePurifiedEnumData<'vir>;
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
    #[allow(dead_code)]
    caster: FieldCaster<'vir>,
    #[allow(dead_code)]
    args: GArgsTy<'vir>,
    #[allow(dead_code)]
    purified: <PurifiedTyDatas as TyDatas<'vir>>::ImmRefData,
}

#[derive(Debug, Clone, Copy)]
pub struct TyUsePurifiedMutRef<'vir> {
    #[allow(dead_code)]
    caster: FieldCaster<'vir>,
    args: GArgsTy<'vir>,
    purified: <PurifiedTyDatas as TyDatas<'vir>>::MutRefData,
}

#[derive(Debug, Clone, Copy)]
pub struct TyUsePurifiedStructData<'vir> {
    args: GArgsTy<'vir>,
    ref_to_pred: PredicateIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>,
    #[allow(dead_code)]
    purified: <PurifiedTyDatas as TyDatas<'vir>>::StructData,
}

#[derive(Debug, Clone, Copy)]
pub struct TyUsePurifiedField<'vir> {
    caster: FieldCaster<'vir>,
    args: GArgsTy<'vir>,
    purified: <PurifiedTyDatas as TyDatas<'vir>>::FieldData,
}

#[derive(Debug, Clone, Copy)]
pub struct TyUsePurifiedEnumData<'vir> {
    #[allow(dead_code)]
    args: GArgsTy<'vir>,
    purified: <PurifiedTyDatas as TyDatas<'vir>>::EnumData,
}

/// Encodes a type into the predicate representation. Takes an arbitrary Rust
/// `Ty` and provides a wrapper around the results of the `TyPurifiedEnc` encoder.
/// This wrapper handles all the generic casts required (e.g. when fold/unfolding).
pub type TyUsePurifiedEnc = TyUseEnc<Purified>;

impl TaskEncoder for TyUsePurifiedEnc {
    task_encoder::encoder_cache!(TyUsePurifiedEnc);

    type TaskDescription<'vir> = super::RustTyDecomposition<'vir>;

    type OutputFullDependency<'vir> = TyUsePurified<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;

        let ty_purified = deps.require_dep::<TyPurifiedEnc>(task_key.ty)?;
        let mut walker = TyUsePurifiedWalker::new(deps, task_key.args);
        let ty_use_purified = walker.encode_ty(task_key.ty.zip(ty_purified));
        Ok(((), ty_use_purified.alloc()))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        TyPurifiedEnc::emit_outputs(program)
    }
}

struct TyUsePurifiedWalker<'a, 'vir> {
    deps: &'a mut TaskEncoderDependencies<'vir, TyUsePurifiedEnc>,
    args_t: GArgsTy<'vir>,
    args: GArgs<'vir>,
}

impl<'a, 'vir> TyUsePurifiedWalker<'a, 'vir> {
    fn new(
        deps: &'a mut TaskEncoderDependencies<'vir, TyUsePurifiedEnc>,
        args: GArgs<'vir>,
    ) -> Self {
        let args_t = deps.require_dep::<GArgsTyEnc>(args).unwrap();
        Self { deps, args_t, args }
    }

    fn encode_ty(
        &mut self,
        ty: TyData<'vir, (RustTyDatas, PurifiedTyDatas)>,
    ) -> TyData<'vir, UsePurifiedTyDatas> {
        let specifics = match &ty.specifics {
            TySpecifics::Param(..) => TySpecifics::mk_param(()),
            TySpecifics::Opaque(..) => TySpecifics::mk_opaque(()),
            TySpecifics::Primitive(..) => TySpecifics::mk_primitive(()),
            TySpecifics::ImmRef(data) => {
                let caster = self.encode_normalized(*data.0, ty.0.params);
                TySpecifics::mk_immref(TyUsePurifiedImmRef {
                    caster,
                    args: self.args_t,
                    purified: *data.1,
                })
            }
            TySpecifics::MutRef(data) => {
                let caster = self.encode_normalized(*data.0, ty.0.params);
                TySpecifics::mk_mutref(TyUsePurifiedMutRef {
                    caster,
                    args: self.args_t,
                    purified: *data.1,
                })
            }
            TySpecifics::StructLike(data) => {
                TySpecifics::StructLike(self.encode_structlike(data, ty.1.ref_to_pred, ty.0.params))
            }
            TySpecifics::EnumLike(data) => {
                TySpecifics::EnumLike(self.encode_enumlike(data, ty.0.params))
            }
        };
        let data = TyUsePurifiedData {
            args: self.args_t,
            purified: *ty.1,
        };
        TyData::new(data, ty.inhabited, specifics)
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
        ref_to_pred: PredicateIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>,
        params: GParams<'vir>,
    ) -> StructData<'vir, UsePurifiedTyDatas> {
        let fields = data
            .fields
            .iter()
            .map(|field| {
                let caster = self.encode_normalized(field.0.ty(), params);
                TyUsePurifiedField {
                    caster,
                    args: self.args_t,
                    purified: *field.1,
                }
            })
            .collect::<Vec<_>>();
        let inhabited = data.inhabited;
        let data = TyUsePurifiedStructData {
            args: self.args_t,
            ref_to_pred,
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
                let structlike =
                    self.encode_structlike(&variant.inner, variant.1.predicate, params);
                VariantData::new((), variant.inhabited, structlike)
            })
            .collect::<Vec<_>>();
        let inhabited = data.inhabited;
        let data = TyUsePurifiedEnumData {
            args: self.args_t,
            purified: *data.1,
        };
        EnumData::new(data, inhabited, variants)
    }
}

impl<'vir> TyUsePurifiedData<'vir> {
    pub fn snapshot(&self) -> vir::TypeSnap<'vir> {
        self.purified
    }
}

impl<'vir> TyData<'vir, UsePurifiedTyDatas> {}

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

    fn cast_to_caller_ctx(
        &self,
        self_snap: vir::ExprSnap<'vir>,
    ) -> impl Iterator<Item = vir::Stmt<'vir>> {
        self.fields
            .iter()
            .filter_map(|f| f.cast_to_caller_ctx(self_snap))
    }

    fn cast_to_callee_ctx(
        &self,
        self_snap: vir::ExprSnap<'vir>,
    ) -> impl Iterator<Item = vir::Stmt<'vir>> {
        self.fields
            .iter()
            .filter_map(|f| f.cast_to_callee_ctx(self_snap))
    }
}

impl<'vir> TyUsePurifiedField<'vir> {
    pub fn field_snap<Curr, Next>(
        &self,
        self_snap: vir::ExprGenSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        (self.purified.read)(self_snap)
    }

    fn cast_to_caller_ctx(&self, self_snap: vir::ExprSnap<'vir>) -> Option<vir::Stmt<'vir>> {
        self.caster.cast_to_caller_ctx(self_snap)
    }

    fn cast_to_callee_ctx(&self, self_snap: vir::ExprSnap<'vir>) -> Option<vir::Stmt<'vir>> {
        self.caster.cast_to_callee_ctx(self_snap)
    }
}

impl<'vir> TyUsePurifiedEnum<'vir> {
    pub fn discr(&self, self_snap: vir::ExprSnap<'vir>) -> vir::ExprSnap<'vir> {
        (self.purified.snap_to_discr_snap)(self_snap)
    }

    pub fn discr_ty(&self) -> TyUsePurified<'vir> {
        self.purified.discr_ty
    }
}

impl<'vir> TyUsePurifiedImmRef<'vir> {
    pub fn value(&self, self_snap: vir::ExprSnap<'vir>) -> vir::ExprSnap<'vir> {
        (self.purified.value_access)(self_snap)
    }
}

impl<'vir> TyUsePurifiedMutRef<'vir> {
    pub fn value(&self, self_snap: vir::ExprSnap<'vir>) -> vir::ExprSnap<'vir> {
        (self.purified.value_access)(self_snap)
    }
}
