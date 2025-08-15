use prusti_rustc_interface::{
    middle::{mir, ty},
    span::def_id::DefId,
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::CastType;

/// Encodes a Rust function as a Viper method using the polymorphic encoding of generics.
pub struct MirPolyPurifiedEnc;

use crate::{
    encoder_traits::purified_function_enc::{
        PurifiedFunctionEnc, PurifiedFunctionEncError, PurifiedFunctionEncOutput,
        PurifiedFunctionEncOutputRef,
    },
    encoders::{
        lifted::{generic::LiftedGenericEnc, ty_constructor::TyConstructorEnc},
        most_generic_ty::{self},
    },
};

impl PurifiedFunctionEnc for MirPolyPurifiedEnc {
    fn mk_method_ident<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        def_id: &Self::TaskKey<'tcx>,
    ) -> vir::ViperIdent<'vir> {
        vir::vir_format_identifier!(vcx, "m_{}", vcx.tcx().def_path_str(*def_id))
    }

    fn mk_conditions<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        task_key: &Self::TaskKey<'vir>,
        arg: &super::PurifiedLocalDef<'vir>,
        ty: ty::Ty<'vir>,
        suffix: &str,
    ) -> Option<vir::ExprBool<'vir>> {
        if ty.is_primitive() {
            return None;
        }
        let most_generic_ty = most_generic_ty::extract_type_params(vcx.tcx(), ty).0;
        let name_s = vir::vir_format_identifier!(vcx, "{}{}", arg.local.name, suffix).to_str();
        let type_s = arg.ty.snapshot;
        let snap = vcx.mk_local_ex(name_s, type_s);
        let lhs = (deps
            .require_ref::<crate::encoders::domain::DomainEnc>(most_generic_ty)
            .unwrap()
            .typeof_function)(snap);
        let rhs = extract_type_expr(vcx, deps, ty, most_generic_ty.into());
        Some(vcx.mk_eq_expr(lhs, rhs))
    }
}

impl TaskEncoder for MirPolyPurifiedEnc {
    task_encoder::encoder_cache!(MirPolyPurifiedEnc);

    type TaskDescription<'tcx> = DefId;

    type TaskKey<'tcx> = DefId;

    type OutputRef<'vir> = PurifiedFunctionEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = PurifiedFunctionEncOutput<'vir>;

    type EncodingError = PurifiedFunctionEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        def_id: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        <Self as PurifiedFunctionEnc>::encode(*def_id, deps).map(|r| (r, ()))
    }
}

/// Recurisvely visits all types in `typ` and builds an
/// Expr that constructs the corresponding VIR type.
pub fn extract_type_expr<'vir: 'tcx, 'tcx, Curr, Next, E: TaskEncoder>(
    vcx: &'vir vir::VirCtxt<'tcx>,
    deps: &mut TaskEncoderDependencies<'vir, E>,
    typ: ty::Ty<'tcx>,
    gen: ty::Ty<'tcx>,
) -> vir::ExprGenTyVal<'vir, Curr, Next> {
    let most_generic_ty = most_generic_ty::extract_type_params(vcx.tcx(), typ).0;
    let ty_constructor = deps
        .require_ref::<TyConstructorEnc>(most_generic_ty)
        .unwrap();

    match (typ.kind(), gen.kind()) {
        // if typ is a param, then we're done
        (ty::TyKind::Param(param_ty), ty::Param(_)) => {
            let lifted = deps
                .require_ref::<LiftedGenericEnc>(*param_ty)
                .unwrap()
                .expr(vcx);
            lifted
        }
        // if typ is a primitive then we need to require/ensure
        // that lhs has the corresponding VIR type
        (ty::TyKind::Bool, _)
        | (ty::TyKind::Char, _)
        | (ty::TyKind::Int(..), _)
        | (ty::TyKind::Uint(..), _)
        | (ty::TyKind::Float(..), _)
        | (ty::TyKind::Foreign(..), _)
        | (ty::TyKind::Str, _)
        | (ty::TyKind::Never, _)
        | (ty::TyKind::Error(..), _)
        | (ty::TyKind::Ref(..), ty::TyKind::Param(_)) => ty_constructor.ty_constructor.gen()(&[]),
        (ty::TyKind::Adt(_, args), ty::TyKind::Param(_))
            if args.types().collect::<Vec<_>>().is_empty() =>
        {
            ty_constructor.ty_constructor.gen()(&[])
        }
        // if a param generic corresponds to a non-primitive typ
        // then we need to expand the param before proceeding
        (ty::TyKind::Adt(..), ty::TyKind::Param(_))
        | (ty::TyKind::Array(..), ty::TyKind::Param(_))
        | (ty::TyKind::Pat(..), ty::TyKind::Param(_))
        | (ty::TyKind::Slice(..), ty::TyKind::Param(_))
        | (ty::TyKind::RawPtr(..), ty::TyKind::Param(_))
        | (ty::Tuple(..), ty::TyKind::Param(_)) => {
            extract_type_expr(vcx, deps, typ, most_generic_ty.ty())
        }
        // otherwise we expand both types recursively and collect their conditions
        (ty::TyKind::Adt(_, typ_args), ty::TyKind::Adt(_, gen_args)) => {
            let rhss = typ_args
                .types()
                .zip(gen_args.types())
                .map(|(typ_arg, gen_arg)| extract_type_expr(vcx, deps, typ_arg, gen_arg))
                .collect::<Vec<_>>();
            ty_constructor.ty_constructor.gen()(&rhss)
        }
        (ty::TyKind::Ref(_, typ_ty, ..), ty::TyKind::Ref(_, gen_ty, ..)) => {
            let rhs = extract_type_expr(vcx, deps, *typ_ty, *gen_ty);
            ty_constructor.ty_constructor.gen()(&[rhs])
        }
        (ty::TyKind::Tuple(typ_tys), ty::TyKind::Tuple(gen_tys)) => {
            let rhss = typ_tys
                .iter()
                .zip(gen_tys.iter())
                .map(|(typ_ty, gen_ty)| extract_type_expr(vcx, deps, typ_ty, gen_ty))
                .collect::<Vec<_>>();
            ty_constructor.ty_constructor.gen()(&rhss)
        }
        (ty::TyKind::Array(typ_ty, ..), ty::TyKind::Array(gen_ty, ..))
        | (ty::TyKind::Pat(typ_ty, ..), ty::TyKind::Pat(gen_ty, ..))
        | (ty::TyKind::Slice(typ_ty), ty::TyKind::Slice(gen_ty))
        | (ty::TyKind::RawPtr(typ_ty, ..), ty::TyKind::RawPtr(gen_ty, ..)) => {
            let rhs = extract_type_expr(vcx, deps, *typ_ty, *gen_ty);
            ty_constructor.ty_constructor.gen()(&[rhs])
        }
        (typ_kind, gen_kind) => {
            unreachable!("typ: {typ_kind:#?} gen: {gen_kind:#?}")
        }
    }
}
