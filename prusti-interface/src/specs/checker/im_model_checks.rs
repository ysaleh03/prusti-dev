use super::common::*;
use crate::{
    environment::{EnvQuery, Environment},
    utils::{has_im_model_field_attr, has_im_model_impl_attr},
    PrustiError,
};
use log::debug;
use prusti_rustc_interface::{
    errors::MultiSpan,
    hir::{
        self as hir,
        def::{DefKind, Res},
        intravisit, HirId, QPath, TyKind,
    },
    middle::ty::TyCtxt,
    span::Span,
};
use rustc_hash::FxHashMap;

// pub enum ImModelSpecResolverError {}

// #[derive(Debug, Eq, PartialEq, Hash, Clone)]
// pub struct ImModelSpecDeclaration {
//     base_type: DefId,
//     method: DefId,
// }

// impl ImModelSpecDeclaration {
//     fn from_method_call<'tcx>(
//         caller_def_id: DefId,
//         def_id: DefId,
//         substs: GenericArgsRef<'tcx>,
//         env_query: EnvQuery<'tcx>,
//     ) -> Self {
//         todo!()
//     }
// }

/// Checks the usage of the abstract field methods (induced by the `#[im_model]` macro) in non-spec code
pub struct IllegalModelUsagesChecker;

impl<'tcx> SpecCheckerStrategy<'tcx> for IllegalModelUsagesChecker {
    #[tracing::instrument(
        name = "IllegalModelUsagesChecker::check",
        level = "debug",
        skip(self, env)
    )]
    fn check(&self, env: &Environment<'tcx>) -> Vec<PrustiError> {
        let mut visit = ModelUsageVisitor {
            env_query: env.query,
            model_usages_in_non_spec_code: Vec::default(),
        }
        .wrap_as_visitor();

        env.query.tcx().hir_walk_toplevel_module(&mut visit);

        let illegal_model_usages = visit.wrapped.model_usages_in_non_spec_code;
        illegal_model_usages
            .into_iter()
            .map(|model_span| {
                PrustiError::incorrect(
                    "using models in non-specification code is not allowed".to_string(),
                    MultiSpan::from_span(model_span),
                )
            })
            .collect()
    }
}

/// Checks for the usage of models in non-specification code
struct ModelUsageVisitor<'tcx> {
    env_query: EnvQuery<'tcx>,
    model_usages_in_non_spec_code: Vec<Span>,
}

impl<'tcx> ModelUsageVisitor<'tcx> {
    fn get_called_method(&self, expr: &'tcx hir::Expr<'tcx>) -> Option<hir::HirId> {
        let maybe_method_def_id = self
            .env_query
            .tcx()
            .typeck(expr.hir_id.owner.def_id)
            .type_dependent_def_id(expr.hir_id);
        if let Some(method_def_id) = maybe_method_def_id {
            let maybe_local_def_id = method_def_id.as_local();
            if let Some(local_def_id) = maybe_local_def_id {
                let decl_hir_id = self.env_query.as_hir_id(local_def_id);
                return Some(decl_hir_id);
            }
        }
        None
    }
}

impl<'tcx> NonSpecExprVisitor<'tcx> for ModelUsageVisitor<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.env_query.tcx()
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        if let hir::ExprKind::MethodCall(_, _, _, call_span) = expr.kind {
            let maybe_method_decl_hir_id: Option<hir::HirId> = self.get_called_method(expr);

            if let Some(method_decl_hir_id) = maybe_method_decl_hir_id {
                let attrs = self.env_query.get_local_attributes(method_decl_hir_id);

                if has_im_model_field_attr(attrs) {
                    self.model_usages_in_non_spec_code.push(call_span);
                }
            }
        }
    }
}

struct CollectModelledTypes<'tcx> {
    env_query: EnvQuery<'tcx>,
    modelled_types: FxHashMap<HirId, &'tcx hir::Ty<'tcx>>,
    abstract_fields: FxHashMap<HirId, Vec<(HirId, &'tcx hir::Ty<'tcx>)>>,
    capabilities: FxHashMap<HirId, Vec<(hir::Expr<'tcx>, hir::Expr<'tcx>, hir::HirId)>>,
}

impl<'tcx> intravisit::Visitor<'tcx> for CollectModelledTypes<'tcx> {
    type NestedFilter = prusti_rustc_interface::middle::hir::nested_filter::All;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.env_query.tcx()
    }

    fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) {
        if let hir::ItemKind::Impl(_impl) = &item.kind {
            let impl_id = _impl.self_ty.hir_id;
            let attrs = self.env_query.get_local_attributes(item.hir_id());
            if has_im_model_impl_attr(attrs) {
                // println!("{impl_id}");
                self.modelled_types.insert(impl_id, _impl.self_ty);
                let tyck_res = self.env_query.tcx().typeck(impl_id.owner.def_id);
                let substs = tyck_res.node_args(impl_id);
                for item_id in _impl.items {
                    let item_attrs = self.env_query.get_local_attributes(item_id.hir_id());
                    if has_im_model_field_attr(item_attrs) {
                        let item_hir_id = item_id.hir_id();
                        let field_ty = self
                            .env_query
                            .get_fn_sig(item_hir_id.owner.def_id, substs)
                            .output();
                        // println!("{item_hir_id}: {field_ty}");
                        // self.abstract_fields.entry(impl_id).and_modify(|v| v.push(, )).or_insert(default)
                    }
                }
            }
        }

        intravisit::walk_item(self, item);
    }

    // fn visit_(&mut self, ex: &'tcx hir::Expr<'tcx>) {

    // }
}
