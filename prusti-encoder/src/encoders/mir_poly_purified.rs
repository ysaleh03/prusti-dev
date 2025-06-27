use prusti_rustc_interface::{
    middle::{mir, ty, ty::TypeVisitableExt},
    span::def_id::DefId,
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};

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
        idx: usize,
    ) -> Vec<vir::Expr<'vir>> {
        let mir_ty = vcx
            .tcx()
            .fn_sig(task_key)
            .map_bound(|bound| {
                if idx == mir::RETURN_PLACE.as_usize() {
                    bound.output()
                } else {
                    bound.input(idx - 1)
                }
            })
            .instantiate_identity()
            .skip_binder();
        let most_generic_ty = most_generic_ty::extract_type_params(vcx.tcx(), mir_ty).0;
        let lhs = if idx == mir::RETURN_PLACE.as_usize() {
            arg.local_ex
        } else {
            let name_s = vir::vir_format_identifier!(vcx, "{}_param", arg.local.name).to_str();
            let type_s = arg.ty.snapshot;
            vcx.mk_local_ex(name_s, type_s)
        };
        let lhs = deps
            .require_ref::<crate::encoders::domain::DomainEnc>(most_generic_ty)
            .unwrap()
            .typeof_function
            .apply(vcx, [lhs]);

        extract_type_conditions(vcx, deps, mir_ty, most_generic_ty.into(), lhs)
            .iter()
            .map(|(lhs, rhs)| vcx.mk_eq_expr(lhs, rhs))
            .collect::<Vec<_>>()
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

/// Recurisvely visits all types in `root` and builds a `Vec` of conditions
/// to allow for casting from `s_Param` to the corresponding VIR type.
/// <br>
/// Returns conditions in the format `(lhs, rhs)` such that `lhs == rhs`.
fn extract_type_conditions<'vir: 'tcx, 'tcx>(
    vcx: &'vir vir::VirCtxt<'tcx>,
    deps: &mut TaskEncoderDependencies<'vir, MirPolyPurifiedEnc>,
    root: ty::Ty<'tcx>,
    generic: ty::Ty<'tcx>,
    lhs: vir::Expr<'vir>,
) -> Vec<(vir::Expr<'vir>, vir::Expr<'vir>)> {
    if !root.has_param() && generic == root {
        return Vec::new();
    }

    let most_generic_ty = most_generic_ty::extract_type_params(vcx.tcx(), root).0;
    let ty_constructor = deps
        .require_ref::<TyConstructorEnc>(most_generic_ty)
        .unwrap();

    match (root.kind(), generic.kind()) {
        // if root is a param, then we're done
        (ty::TyKind::Param(param_ty), ty::Param(_)) => {
            let lifted = deps
                .require_ref::<LiftedGenericEnc>(*param_ty)
                .unwrap()
                .expr(vcx);
            vec![(lhs, lifted)]
        }
        // if root is a primitive then we need to require/ensure
        // that lhs has the corresponding VIR type
        (ty::TyKind::Bool, ty::TyKind::Param(param_ty))
        | (ty::TyKind::Char, ty::TyKind::Param(param_ty))
        | (ty::TyKind::Int(..), ty::TyKind::Param(param_ty))
        | (ty::TyKind::Uint(..), ty::TyKind::Param(param_ty))
        | (ty::TyKind::Float(..), ty::TyKind::Param(param_ty))
        | (ty::TyKind::Foreign(..), ty::TyKind::Param(param_ty))
        | (ty::TyKind::Str, ty::TyKind::Param(param_ty))
        | (ty::TyKind::Never, ty::TyKind::Param(param_ty))
        | (ty::TyKind::Error(..), ty::TyKind::Param(param_ty)) => {
            vec![(lhs, ty_constructor.ty_constructor.apply(vcx, &[]))]
        }
        // if a param generic corresponds to a non-primitive root
        // then we need to expand the param before proceeding
        // *and*
        // need to require/ensure that lhs is the corresponding VIR
        // data structure with fields of the corresponding VIR types
        (ty::TyKind::Array(..), ty::TyKind::Param(_))
        | (ty::TyKind::Pat(..), ty::TyKind::Param(_))
        | (ty::TyKind::Slice(..), ty::TyKind::Param(_))
        | (ty::TyKind::RawPtr(..), ty::TyKind::Param(_))
        | (ty::TyKind::Ref(..), ty::TyKind::Param(_))
        | (ty::Tuple(..), ty::TyKind::Param(_)) => {
            let mut inner_eq_exprs =
                extract_type_conditions(vcx, deps, root, most_generic_ty.into(), lhs);
            let rhss = inner_eq_exprs
                .iter()
                .map(|(_, rhs)| *rhs)
                .collect::<Vec<_>>();
            let expr = (lhs, ty_constructor.ty_constructor.apply(vcx, &rhss));
            inner_eq_exprs.push(expr);
            inner_eq_exprs
        }
        // else we expand both types recursively and collect their conditions
        (ty::TyKind::Adt(root_adt_def, root_args), ty::TyKind::Adt(gen_adt_def, gen_args)) => {
            root_adt_def
                .all_fields()
                .zip(gen_adt_def.all_fields())
                .zip(ty_constructor.ty_param_accessors)
                .flat_map(|((root_field, gen_field), accessor)| {
                    extract_type_conditions(
                        vcx,
                        deps,
                        root_field.ty(vcx.tcx(), root_args),
                        gen_field.ty(vcx.tcx(), gen_args),
                        accessor.apply(vcx, [lhs]),
                    )
                })
                .collect::<Vec<_>>()
        }
        (ty::TyKind::Tuple(root_tys), ty::TyKind::Tuple(gen_tys)) => root_tys
            .iter()
            .zip(gen_tys.iter())
            .zip(ty_constructor.ty_param_accessors)
            .flat_map(|((root_ty, gen_ty), accessor)| {
                extract_type_conditions(vcx, deps, root_ty, gen_ty, accessor.apply(vcx, [lhs]))
            })
            .collect::<Vec<_>>(),
        (ty::TyKind::Array(root_ty, ..), ty::TyKind::Array(gen_ty, ..))
        | (ty::TyKind::Pat(root_ty, ..), ty::TyKind::Pat(gen_ty, ..))
        | (ty::TyKind::Slice(root_ty), ty::TyKind::Slice(gen_ty))
        | (ty::TyKind::RawPtr(root_ty, ..), ty::TyKind::RawPtr(gen_ty, ..))
        | (ty::TyKind::Ref(_, root_ty, ..), ty::TyKind::Ref(_, gen_ty, ..)) => {
            extract_type_conditions(
                vcx,
                deps,
                *root_ty,
                *gen_ty,
                ty_constructor.ty_param_accessors[0].apply(vcx, [lhs]),
            )
        }
        (root_kind, generic_kind) => {
            unreachable!("root: {root_kind:#?} generic: {generic_kind:#?}")
        }
    }
}
