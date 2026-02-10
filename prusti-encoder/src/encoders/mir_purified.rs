use pcg::{
    PcgOutput,
    action::{BorrowPcgAction, PcgAction, PcgActions},
    borrow_pcg::{
        action::BorrowPcgActionKind,
        borrow_pcg_edge::{BorrowPcgEdge, LocalNode},
        edge::{
            abstraction::{AbstractionEdge, FunctionCallOrLoop},
            kind::BorrowPcgEdgeKind,
        },
        state::BorrowsState,
        unblock_graph::BorrowPcgUnblockAction,
    },
    coupling::PcgCoupledEdgeKind,
    free_pcs::{RepackGuide, RepackOp},
    r#loop::{LoopAnalysis, LoopId, PlaceUsages},
    pcg::{EvalStmtPhase, Pcg, PcgNode, PcgSuccessor},
    results::PcgBasicBlock,
    utils::{
        CompilerCtxt, HasPlace, Place, SnapshotLocation, display::DisplayWithCtxt,
        maybe_old::MaybeLabelledPlace,
    },
};
use prusti_interface::{PrustiError, specs::specifications::SpecQuery};
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::{
        mir,
        ty::{self, TyKind},
    },
    span::{Span, def_id::DefId},
};
use prusti_utils::config;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, CompType, ExprSnap, LocalDeclData, OldLabel, macros::ExprQuote};

use crate::encoders::{
    self, FunctionCallEnc, PurifiedWandEnc, PurifiedWandEncTask,
    mir_fn::{CallTaskDescription, RustSignature},
    mir_shared::PureRvalueEnc,
    ty::{
        RustTyDecomposition,
        data::TySpecifics,
        use_pure::{TyUsePure, TyUsePureEnc},
        use_purified::{TyUsePurified, TyUsePurifiedEnc},
    },
};

use super::PurifiedWandEncOutput;

#[derive(Clone, Copy)]
struct FromToVar<'vir> {
    decl: vir::LocalDeclBool<'vir>,
    expr: vir::ExprBool<'vir>,
}

impl<'vir> FromToVar<'vir> {
    fn new(vcx: &'vir vir::VirCtxt<'vir>, from: mir::BasicBlock, to: mir::BasicBlock) -> Self {
        let decl = vcx.mk_local_decl(
            vir::vir_format!(vcx, "_from_bb{}_to_bb{}", from.index(), to.index()),
            vir::TYPE_BOOL,
        );
        let expr = vcx.mk_local_ex(decl);
        Self { decl, expr }
    }
}

#[derive(Default)]
pub(crate) struct FromToVars<'vir>(FxHashMap<(mir::BasicBlock, mir::BasicBlock), FromToVar<'vir>>);

impl<'vir> FromToVars<'vir> {
    pub(crate) fn decls(&self) -> impl Iterator<Item = &'vir LocalDeclData<'vir, vir::Bool>> {
        self.0.values().map(|v| v.decl)
    }

    fn set_from_to_flag_stmt(
        &mut self,
        vcx: &'vir vir::VirCtxt<'vir>,
        from: mir::BasicBlock,
        to: mir::BasicBlock,
    ) -> vir::Stmt<'vir> {
        let var = self.get_or_create(vcx, from, to);
        vcx.mk_pure_assign_stmt(var.expr, vcx.mk_bool::<true>())
    }

    fn get_or_create(
        &mut self,
        vcx: &'vir vir::VirCtxt<'vir>,
        from: mir::BasicBlock,
        to: mir::BasicBlock,
    ) -> FromToVar<'vir> {
        *self
            .0
            .entry((from, to))
            .or_insert_with(|| FromToVar::new(vcx, from, to))
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum EdgeAction {
    Add,
    Remove,
}

impl EdgeAction {
    pub(crate) fn is_add(self) -> bool {
        matches!(self, EdgeAction::Add)
    }
    pub(crate) fn is_remove(self) -> bool {
        matches!(self, EdgeAction::Remove)
    }
}

pub(crate) enum PackOrUnpack {
    Pack,
    Unpack,
}

impl PackOrUnpack {
    pub(crate) fn for_action(action: EdgeAction) -> Self {
        match action {
            EdgeAction::Add => PackOrUnpack::Unpack,
            EdgeAction::Remove => PackOrUnpack::Pack,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum LocationLabelPrefix {
    Before,
    After,
    BeforeRefReassignment,
}

impl LocationLabelPrefix {
    pub(crate) fn to_str(self) -> &'static str {
        match self {
            LocationLabelPrefix::Before => "before",
            LocationLabelPrefix::After => "after",
            LocationLabelPrefix::BeforeRefReassignment => "before_ref_reassignment",
        }
    }
}

pub struct PurifiedEncVisitor<'vir, 'enc, E: TaskEncoder>
where
    'vir: 'enc,
{
    pub vcx: &'vir vir::VirCtxt<'vir>,
    pub deps: &'enc mut TaskEncoderDependencies<'vir, E>,
    pub def_id: DefId,
    pub local_decls: &'enc mir::LocalDecls<'vir>,
    pub fpcs_analysis: PcgOutput<'enc, 'vir>,
    pub local_defs: crate::encoders::PurifiedMirLocalDefEncOutput<'vir>,
    pub body: &'enc mir::Body<'vir>,

    pub wands: PurifiedWandEncOutput<'vir>,

    // TODO: in theory only need return_to_remote here for reconstructing
    // mutrefs at the end of the method..
    // pub return_to_remote: FxHashMap<mir::Local, vir::ExprSnap<'vir>>,
    // pub declared_remotes: FxHashSet<(&'vir str, vir::TypeSnap<'vir>)>, // is this even necessary??
    // pub remote_to_local_decl: FxHashMap<Place<'vir>, vir::LocalDeclSnap<'vir>>,
    pub declared_vars: FxHashSet<(&'vir str, vir::TypeSnap<'vir>)>,
    pub place_to_local_decl: FxHashMap<Place<'vir>, vir::LocalDeclSnap<'vir>>,

    pub tmp_ctr: usize,
    pub label_ctr: usize,
    pub call_labels: FxHashMap<mir::BasicBlock, (&'vir str, &'vir str)>,
    pub from_to_vars: FromToVars<'vir>,

    // for the current basic block
    pub current_fpcs: Option<PcgBasicBlock<'enc, 'vir>>,

    pub current_block_label: Option<vir::CfgBlockLabel<'vir>>,
    pub current_stmts: Option<Vec<vir::Stmt<'vir>>>,
    pub current_terminator: Option<vir::TerminatorStmt<'vir>>,

    pub encoded_blocks: Vec<vir::CfgBlock<'vir>>, // TODO: use IndexVec ?
}

// /// Represents the translation of a MIR place. If the place crosses a shared
// /// reference, then we will no longer have a predicate for the `address` Ref,
// /// but we do also have the snapshot available.
// pub(crate) struct PlaceExpr<'vir> {
//     address: vir::ExprRef<'vir>,
//     snap: Option<vir::ExprSnap<'vir>>,
// }

// impl<'vir> PlaceExpr<'vir> {
//     /// Expects the encoded place to not be behind a shared ref
//     pub(crate) fn expect_predicate(&self) -> vir::ExprRef<'vir> {
//         assert!(self.snap.is_none());
//         self.address
//     }
// }

pub(crate) struct EncodePlaceResult<'vir> {
    pub(crate) snap: vir::ExprSnap<'vir>,
    pub(crate) ty: mir::PlaceTy<'vir>,
}

macro_rules! comment {
    ($self:tt, $($arg:tt)*) => { $self.comment(
        vir::vir_format!($self.vcx, $($arg)*),
    ) };
}

type EncodeResult<'vir, T, E> = Result<T, EncodeFullError<'vir, E>>;

type EncodedRvalue<'vir> = vir::ExprSnap<'vir>;

enum EncodeRvalueError<'vir, E: TaskEncoder> {
    UnsupportedRvalue,
    EncoderError(EncodeFullError<'vir, E>),
}

impl<'vir, E: TaskEncoder> From<EncodeFullError<'vir, E>> for EncodeRvalueError<'vir, E> {
    fn from(e: EncodeFullError<'vir, E>) -> Self {
        EncodeRvalueError::EncoderError(e)
    }
}

impl<'vir, 'enc, E: TaskEncoder> PurifiedEncVisitor<'vir, 'enc, E> {
    pub(crate) fn pcg_ctxt(&self) -> CompilerCtxt<'enc, 'vir> {
        self.fpcs_analysis.ctxt()
    }

    // TODO: make `pub(super)`
    pub(crate) fn stmt(&mut self, stmt: vir::Stmt<'vir>) {
        self.current_stmts.as_mut().unwrap().push(stmt);
    }

    fn stmts(&mut self, stmts: impl IntoIterator<Item = vir::Stmt<'vir>>) {
        for stmt in stmts {
            self.stmt(stmt);
        }
    }

    fn comment(&mut self, msg: &'vir str) {
        self.stmt(self.vcx.mk_comment_stmt(msg));
    }

    fn ty_use_purified(&mut self, ty: ty::Ty<'vir>) -> TyUsePurified<'vir> {
        let ty_task = RustTyDecomposition::from_ty(ty, self.vcx.tcx(), self.def_id);
        self.deps.require_dep::<TyUsePurifiedEnc>(ty_task).unwrap()
    }

    fn encode_rvalue(
        &mut self,
        rvalue: &mir::Rvalue<'vir>,
        span: Span,
    ) -> Result<ExprSnap<'vir>, EncodeRvalueError<'vir, E>> {
        let rvalue_ty = rvalue.ty(self.local_decls, self.vcx.tcx());
        match rvalue {
            mir::Rvalue::Use(op) => Ok(self
                .encode_operand_snap(op, &())
                .map_err(EncodeRvalueError::from)?),
            mir::Rvalue::Cast(cast_kind, operand, ty) => {
                let encoded_cast = self.encode_cast_snap(*cast_kind, operand, *ty, &())?;
                self.vcx.with_span(span, |_| {
                    self.vcx
                        .handle_error("exhale.failed:assertion.false", move |_| {
                            Some(vec![PrustiError::verification(
                                "cast may fail: value might not fit into the target type",
                                span.into(),
                            )])
                        });
                });
                Ok(encoded_cast.expr)
            }
            mir::Rvalue::Len(place) => Ok(self.encode_len_snap((*place).into(), &())),
            mir::Rvalue::BinaryOp(op, box (l, r)) => Ok(self
                .encode_binop_snap(rvalue_ty, *op, l, r, &())
                .map_err(EncodeRvalueError::from)?),
            mir::Rvalue::UnaryOp(op, operand) => Ok(self
                .encode_unary_op_snap(rvalue_ty, *op, operand, &())
                .map_err(EncodeRvalueError::from)?),
            mir::Rvalue::Aggregate(
                box kind @ (mir::AggregateKind::Adt(..) | mir::AggregateKind::Tuple),
                fields,
            ) => Ok(self
                .encode_aggregate_snap(rvalue_ty, kind, fields, &())
                .map_err(EncodeRvalueError::from)?),
            mir::Rvalue::Discriminant(place) => {
                let place_ty = place.ty(self.local_decls, self.vcx.tcx());
                let ty = self.ty_use_purified(place_ty.ty);
                let place_expr = self.encode_place(Place::from(*place)).snap;

                Ok(match ty
                    .get_enumlike()
                    .filter(|_| place_ty.variant_index.is_none())
                {
                    Some(el) => {
                        let ty = self.ty_use_pure(place_ty.ty).expect_enumlike();
                        ty.snap_to_discr_snap(place_expr.downcast_ty())
                    }
                    None => {
                        // mir::Rvalue::Discriminant documents "Returns zero for types without discriminant"
                        let zero = self.vcx.mk_uint::<0>();
                        (ty.expect_primitive().prim_to_snap)(zero.upcast_ty())
                    }
                }
                .upcast_ty()
                .into())
            }
            mir::Rvalue::Ref(_reg, _kind, place) => Ok(match rvalue_ty.kind() {
                TyKind::Ref(.., ty::Mutability::Not) => {
                    let (_, snap, _, _) = self.encode_place_with_snap((*place).into());
                    let inner = self.ty_use_purified(rvalue_ty).expect_immref();
                    inner.prim_to_snap(snap).upcast_ty()
                }
                TyKind::Ref(.., ty::Mutability::Mut) => {
                    let (_, snap, _, _) = self.encode_place_with_snap(Place::from(*place));
                    let inner = self.ty_use_purified(rvalue_ty).expect_mutref();
                    inner.prim_to_snap(snap).upcast_ty()
                }
                _ => unreachable!(),
            }),
            _ => Err(EncodeRvalueError::UnsupportedRvalue),
        }
    }

    /// Do the same as [self.pcs_succ] but instead of adding the statements to [self.current_stmts] return them instead.
    /// TODO: clean this up
    fn collect_pcs_succ<'a>(
        &mut self,
        state: &Pcg<'_, 'vir>,
        pcs: &'a PcgSuccessor<'_, 'vir>,
    ) -> Vec<vir::Stmt<'vir>> {
        let current_stmts = self.current_stmts.take();
        self.current_stmts = Some(Vec::new());
        self.pcs_succ(state, pcs);
        let new_stmts = self.current_stmts.take().unwrap();
        self.current_stmts = current_stmts;
        new_stmts
    }

    pub(crate) fn block<Err>(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<(), Err>,
    ) -> Result<Vec<vir::Stmt<'vir>>, Err> {
        let current_stmts = self.current_stmts.take();
        self.current_stmts = Some(Vec::new());
        f(self)?;
        let new_stmts = self.current_stmts.take().unwrap();
        self.current_stmts = current_stmts;
        Ok(new_stmts)
    }

    pub(crate) fn pack_or_unpack(
        &mut self,
        base: MaybeLabelledPlace<'vir>,
        expansion: Vec<LocalNode<'vir>>,
        guide: Option<RepackGuide>,
        pack_or_unpack: PackOrUnpack,
        label: Option<&'vir str>,
    ) {
        let place = base.place();
        let label = if let MaybeLabelledPlace::Labelled(snap) = base {
            Some(self.get_location_label(snap.at()))
        } else {
            label.map(vir::OldLabel::Label)
        };
        let target_places = expansion
            .iter()
            .filter_map(|mp| mp.as_current_place())
            .collect::<Vec<_>>();

        match pack_or_unpack {
            PackOrUnpack::Unpack => self.unpack(place, guide, &target_places, label),
            PackOrUnpack::Pack => self.pack(place, guide, &target_places, label),
        }
    }

    // pub(crate) fn pcs_borrow_expansion(
    //     &mut self,
    //     expansion: BorrowPcgExpansion<'vir>,
    //     unpack: bool,
    //     label: Option<&'vir str>,
    // ) {
    //     let base = expansion.base();
    //     let PcgNode::Place(base) = base else {
    //         // Ignore expansions of region projections
    //         return;
    //     };
    //     let (place, old) = match base {
    //         MaybeLabelledPlace::Current(place) => (place, None),
    //         MaybeLabelledPlace::Labelled(snap) => {
    //             // We shouldn't be unpacking old places?
    //             debug_assert!(!unpack);
    //             (
    //                 snap.place(),
    //                 Some(Self::get_location_label(self.vcx, snap.at())),
    //             )
    //         }
    //     };
    //     let mut place_enc = self.encode_place(place);
    //     if let Some(label) = old {
    //         place_enc.expr = self.vcx.mk_old(place_enc.expr, label);
    //     } else if let Some(label) = label {
    //         place_enc.expr = self.vcx.mk_local_labelled_old_expr(place_enc.expr, label);
    //     }
    //     if unpack {
    //         self.expand(
    //             place,
    //             None,
    //             &expansion
    //                 .expansion()
    //                 .iter()
    //                 .map(|maybe| maybe.place())
    //                 .collect::<Vec<_>>(),
    //         );
    //     } else {
    //         self.collapse(
    //             place,
    //             None,
    //             &expansion
    //                 .expansion()
    //                 .iter()
    //                 .map(|maybe| maybe.place())
    //                 .collect::<Vec<_>>(),
    //         );
    //     }
    // }

    fn pcs_handle_edge(
        &mut self,
        borrows_state: &BorrowsState<'_, 'vir>,
        edge: &BorrowPcgEdge<'vir>,
        edge_action: EdgeAction,
        label: Option<&'vir str>,
        edge_to_loop: bool,
        to_skip: &mut Vec<mir::BasicBlock>,
    ) -> EncodeResult<'vir, (), E> {
        let conditions = edge.conditions();

        // For each block `b` where the edge is only valid if control flow
        // continues from `b` to a specified subset of its successors, `cond`
        // contains the corresponding VIR expression.
        let cond = conditions
            .all_branch_choices()
            .map(|choices| {
                let successors = choices.successors(self.body);
                let from = choices.from();
                let disj = successors
                    .iter()
                    .map(|to| self.from_to_vars.get_or_create(self.vcx, from, *to).expr)
                    .collect::<Vec<_>>();
                // Control flow must continue from `choices.from()` to any one of the `successors`
                self.vcx.mk_disj(self.vcx.alloc_slice(&disj))
            })
            .collect::<Vec<_>>();
        // For each block `b` where the edge validity depends on the successor taken from `b`,
        // every successor must be valid.
        let cond = self.vcx.mk_conj(self.vcx.alloc_slice(&cond));
        let stmts = self.block(|self_| {
            self_.pcs_handle_edge_conditionless(
                borrows_state,
                edge,
                edge_action,
                label,
                edge_to_loop,
                to_skip,
            )
        })?;
        if stmts.is_empty()
            || stmts
                .iter()
                .all(|stmt| matches!(stmt.kind, vir::StmtKindData::Comment(_)))
        {
            self.stmts(stmts);
            return Ok(());
        }
        let stmts = self.vcx.alloc_slice(&stmts);
        self.stmt(self.vcx.mk_if_stmt(cond, stmts, &[]));
        Ok(())
    }

    fn pcs_handle_edge_conditionless(
        &mut self,
        borrows_state: &BorrowsState<'_, 'vir>,
        edge: &BorrowPcgEdge<'vir>,
        edge_action: EdgeAction,
        label: Option<&'vir str>,
        edge_to_loop: bool,
        to_skip: &mut Vec<mir::BasicBlock>,
    ) -> EncodeResult<'vir, (), E> {
        match edge.kind() {
            // BorrowPcgEdgeKind::Borrow(borrow) if borrow.is_mut() && edge_action.is_remove() => {
            //     self.unpack(borrow.assigned_ref(), label);
            // }
            // BorrowPcgEdgeKind::Borrow(borrow_edge) if borrow_edge.is_mut() => {
            //     if edge_action.is_add() {
            //         return Ok(());
            //     }
            //     let deref_place = borrow_edge.deref_place(self.pcg_ctxt()).place();
            //     let deref_ty = deref_place.ty(self.pcg_ctxt()).ty;
            //     let deref_enc = self.encode_place(deref_place);

            //     let remote_place = borrow_edge.blocked_place().place();
            //     let remote_local_data =
            //         if let Some(local_data) = self.remote_to_local_decl.get(&remote_place) {
            //             self.vcx.mk_local_decl(local_data.name, local_data.ty)
            //         } else {
            //             let remote_name = vir::vir_format_identifier!(
            //                 self.vcx,
            //                 "_{}s_remote",
            //                 remote_place.local.as_usize()
            //             )
            //             .to_str();
            //             let remote_ty = deref_enc.expr.snap.unwrap().ty();
            //             let local = self.vcx.mk_local_decl(remote_name, remote_ty);

            //             self.declared_remotes.insert((remote_name, remote_ty));
            //             self.remote_to_local_decl.insert(remote_place, local);

            //             local
            //         };
            // }
            BorrowPcgEdgeKind::BorrowPcgExpansion(expansion)
                if let PcgNode::Place(base) = expansion.base() =>
            {
                self.pack_or_unpack(
                    base,
                    expansion.expansion(),
                    expansion.guide(),
                    PackOrUnpack::for_action(edge_action),
                    label,
                );
            }
            BorrowPcgEdgeKind::Coupled(PcgCoupledEdgeKind(FunctionCallOrLoop::FunctionCall(
                call_edge,
            ))) => {
                if edge_action.is_add() {
                    // The wand will be introduced by the method call itself.
                    return Ok(());
                }
                let call = call_edge.metadata();
                // We may be encoding multiple edges as a single wand, skip
                // further edge removals. This is a hack to get around the fact
                // that Viper doesn't support hyperwands.
                if to_skip.contains(&call.location().block) {
                    return Ok(());
                }
                to_skip.push(call.location().block);
                // TODO: this applies *all* the wands for the referenced
                //   function call; instead we should figure out which
                //   wand it is based on the edge info.
                // TODO: closures
                let wands = self
                    .deps
                    .require_dep::<PurifiedWandEnc>(PurifiedWandEncTask {
                        data: call.function_data().unwrap(),
                    })
                    .unwrap();
                let bb = &self.body[call.location().block];
                let terminator = bb.terminator.as_ref().unwrap();
                match &terminator.kind {
                    mir::TerminatorKind::Call {
                        args, destination, ..
                    } => {
                        let (_, dest_snap, _, _) =
                            self.encode_place_with_snap((*destination).into());
                        let wand_args =
                            std::iter::once(Ok(dest_snap))
                                .chain(args.iter().map(|operand| {
                                    self.encode_operand_snap_immediate(&operand.node)
                                }))
                                .collect::<Result<Vec<_>, EncodeFullError<'vir, E>>>()?;
                        let (label_pre, label_post) = self.call_labels[&call.location().block];
                        wands.apply_proofs(&wand_args, label_pre, label_post, self);
                    }
                    _ => unreachable!(),
                }
            }
            BorrowPcgEdgeKind::Abstraction(at @ AbstractionEdge::Loop(_)) => {
                self.pcs_handle_wand(
                    borrows_state,
                    edge_action.is_add(),
                    &at.clone().into_singleton_coupled_edge(),
                    label,
                    edge_to_loop,
                );
            }
            other => comment!(self, "(ignoring) {edge_action:?} {other:?}"),
        }
        comment!(
            self,
            "(PCG) handled edge {edge_action:?}: {}",
            edge.to_short_string(self.pcg_ctxt())
        );
        Ok(())
    }

    // fn pcs_handle_edge_conditionless(
    //     &mut self,
    //     borrows_state: &BorrowsState<'_, 'vir>,
    //     edge: &BorrowPcgEdge<'vir>,
    //     add: bool,
    //     label: Option<&'vir str>,
    //     edge_to_loop: bool,
    //     to_skip: &mut Vec<mir::BasicBlock>,
    // ) {
    //     match edge.kind() {
    //         BorrowPcgEdgeKind::BorrowPcgExpansion(expansion) => {
    //             self.pcs_borrow_expansion(expansion.clone(), add, label);
    //         }
    //         BorrowPcgEdgeKind::Coupled(PcgCoupledEdgeKind(FunctionCallOrLoop::FunctionCall(
    //             call_edge,
    //         ))) => {
    //             if add {
    //                 // The wand will be introduced by the method call itself.
    //                 return;
    //             }
    //             let call = call_edge.metadata();
    //             // We may be encoding multiple edges as a single wand, skip
    //             // further edge removals. This is a hack to get around the fact
    //             // that Viper doesn't support hyperwands.
    //             if to_skip.contains(&call.location().block) {
    //                 return;
    //             }
    //             to_skip.push(call.location().block);
    //             // TODO: this applies *all* the wands for the referenced
    //             //   function call; instead we should figure out which
    //             //   wand it is based on the edge info.
    //             let wands = self
    //                 .deps
    //                 .require_local::<PurifiedWandEnc>(PurifiedWandEncTask {
    //                     def_id: call.def_id().unwrap(),
    //                 })
    //                 .unwrap();
    //             let bb = &self.body[call.location().block];
    //             let terminator = bb.terminator.as_ref().unwrap();
    //             match &terminator.kind {
    //                 mir::TerminatorKind::Call {
    //                     args, destination, ..
    //                 } => {
    //                     let (_, dest_snap, _) = self.encode_place_snap((*destination).into());
    //                     let wand_args =
    //                         std::iter::once(dest_snap)
    //                             .chain(args.iter().map(|operand| {
    //                                 self.encode_operand_snap_immediate(&operand.node)
    //                             }))
    //                             .collect::<Vec<_>>();
    //                     let (label_pre, label_post) = self.call_labels[&call.location().block];
    //                     wands.apply_proofs(&wand_args, label_pre, label_post, self);
    //                 }
    //                 _ => unreachable!(),
    //             }
    //         }
    //         BorrowPcgEdgeKind::Abstraction(at @ AbstractionEdge::Loop(_)) => {
    //             self.pcs_handle_wand(
    //                 borrows_state,
    //                 add,
    //                 &at.clone().into_singleton_coupled_edge(),
    //                 label,
    //                 edge_to_loop,
    //             );
    //         }
    //         // BorrowPcgEdgeKind::Borrow(BorrowEdge::Remote(remote_borrow))
    //         //     if remote_borrow.is_mut(self.pcg_ctxt()) =>
    //         // {
    //         //     if add {
    //         //         return;
    //         //     }

    //         //     let deref_place = remote_borrow.deref_place(self.pcg_ctxt()).place();
    //         //     let deref_ty = deref_place.ty(self.pcg_ctxt()).ty;
    //         //     let deref_enc = self.encode_place(deref_place);

    //         //     let remote_place = remote_borrow.blocked_place();
    //         //     let remote_local_data =
    //         //         if let Some(local_data) = self.remote_place_to_local_decl.get(&remote_place) {
    //         //             self.vcx.mk_local_decl(local_data.name, local_data.ty)
    //         //         } else {
    //         //             let remote_name = vir::vir_format_identifier!(
    //         //                 self.vcx,
    //         //                 "_{}s_remote",
    //         //                 remote_place.assigned_local().as_usize()
    //         //             )
    //         //             .to_str();
    //         //             let local = self.vcx.mk_local_decl(remote_name, deref_enc.expr.ty());

    //         //             self.declared_remotes
    //         //                 .insert((remote_name, deref_enc.expr.ty()));
    //         //             self.remote_place_to_local_decl.insert(remote_place, local);

    //         //             local
    //         //         };

    //         //     let lhs = self.vcx.mk_local_ex(remote_local_data);
    //         //     let (rhs_place, _rhs) = (deref_place, deref_enc.expr);
    //         //     let rhs = if let Some(&rhs) = self.place_to_local_data.get(&rhs_place) {
    //         //         self.vcx
    //         //             .mk_local_ex(self.vcx.mk_local_decl(rhs.name, rhs.ty))
    //         //     } else {
    //         //         // caster.cast_to_concrete_if_possible(self.vcx, self.encode_place(rhs_place).expr)
    //         //         self.encode_place(rhs_place).expr
    //         //     };

    //         //     self.stmt(self.vcx.mk_pure_assign_stmt(lhs, rhs));

    //         //     let assigned_local = remote_place.assigned_local();
    //         //     // let cons = self.local_defs.locals[assigned_local]
    //         //     //     .ty
    //         //     //     .expect_purified_mutref()
    //         //     //     .snap_data
    //         //     //     .prim_to_snap;
    //         //     // self.return_to_remote.insert(
    //         //     //     assigned_local,
    //         //     //     (cons(caster.cast_to_generic_if_necessary(self.vcx, lhs))).upcast_ty(),
    //         //     // );
    //         // }
    //         // BorrowPcgEdgeKind::Borrow(BorrowEdge::Local(local_borrow)) => {
    //         //     if add {
    //         //         return;
    //         //     }

    //         //     let blocked_place = local_borrow.blocked_place.place();
    //         //     let deref_place = local_borrow.deref_place(self.pcg_ctxt()).place();
    //         //     let deref_ty = deref_place.ty(self.pcg_ctxt()).ty;

    //         //     let lhs = self.encode_place(blocked_place).expr;
    //         //     let rhs = if let Some(&rhs) = self.place_to_local_data.get(&deref_place) {
    //         //         self.vcx
    //         //             .mk_local_ex(self.vcx.mk_local_decl(rhs.name, rhs.ty))
    //         //     } else {
    //         //         self.encode_place(deref_place).expr
    //         //     };

    //         //     self.stmt(self.vcx.mk_pure_assign_stmt(lhs, rhs));
    //         // }
    //         unsupported_op => comment!(self, "(ignoring {unsupported_op:?})"),
    //     }
    // }

    pub(crate) fn pcs_unblock_actions(
        &mut self,
        borrows_state: &BorrowsState<'_, 'vir>,
        actions: &[BorrowPcgUnblockAction<'vir>],
        label: Option<&'vir str>,
    ) -> EncodeResult<'vir, (), E> {
        let mut to_skip = Vec::new();
        for action in actions {
            self.pcs_handle_edge(
                borrows_state,
                action.edge(),
                EdgeAction::Remove,
                label,
                false,
                &mut to_skip,
            )?;
        }
        Ok(())
    }

    fn pcg_actions(
        &mut self,
        pcg: &Pcg<'_, 'vir>,
        actions: &PcgActions<'vir>,
        edge_to_loop: bool,
    ) -> EncodeResult<'vir, (), E> {
        for action in actions.iter() {
            match action {
                PcgAction::Borrow(action) => self.borrow_action(pcg, action, edge_to_loop)?,
                PcgAction::Owned(action) => self.pcg_repack(action.kind()),
            }
        }
        Ok(())
    }

    fn borrow_action(
        &mut self,
        pcg: &Pcg<'_, 'vir>,
        action: &BorrowPcgAction<'vir>,
        edge_to_loop: bool,
    ) -> EncodeResult<'vir, (), E> {
        let mut to_skip = Vec::new();
        match action.kind() {
            //Weaken(Weaken<'tcx>),
            //Restore(RestoreCapability<'tcx>),
            //MakePlaceOld(Place<'tcx>),
            //SetLatest(Place<'tcx>, Location),
            //AddRegionProjectionMember(RegionProjectionMember<'tcx>, PathConditions),
            BorrowPcgActionKind::RemoveEdge(edge) => self.pcs_handle_edge(
                pcg.borrow_pcg(),
                edge,
                EdgeAction::Remove,
                None,
                edge_to_loop,
                &mut to_skip,
            ),
            BorrowPcgActionKind::AddEdge { edge } => self.pcs_handle_edge(
                pcg.borrow_pcg(),
                edge,
                EdgeAction::Add,
                None,
                edge_to_loop,
                &mut to_skip,
            ),
            //RenamePlace {
            //    old: MaybeOldPlace<'tcx>,
            //    new: MaybeOldPlace<'tcx>,
            //},
            other => {
                comment!(self, "(ignoring) {other:?}");
                Ok(())
            }
        }
    }

    fn pcg_repack(&mut self, repack_op: &RepackOp<'vir>) {
        comment!(self, "[PCG] {repack_op:?}");

        fn should_ignore(repack_op: &RepackOp<'_>) -> bool {
            match repack_op {
                RepackOp::RegainLoanedCapability(..) => true,
                RepackOp::Weaken(weaken) => {
                    weaken.from_cap().is_exclusive() && weaken.to_cap().is_read()
                }
                _ => false,
            }
        }

        match repack_op {
            RepackOp::Expand(expand) => {
                self.unpack(
                    expand.from(),
                    expand.guide(),
                    &expand.target_places(self.pcg_ctxt()),
                    None,
                );
            }
            RepackOp::Collapse(collapse) => {
                let expansion = collapse.to().expansion(collapse.guide(), self.pcg_ctxt());
                self.pack(
                    collapse.to(),
                    collapse.guide(),
                    &collapse
                        .to()
                        .expansion_places(&expansion, self.pcg_ctxt())
                        .unwrap(),
                    None,
                );
            }
            // RepackOp::Weaken(weaken)
            //     if weaken.from_cap().is_exclusive() && weaken.to_cap().is_write() =>
            // {
            //     self.pcg_weaken(weaken.place())
            // }
            other => {
                if should_ignore(other) {
                    self.stmt(self.vcx.mk_comment_stmt(vir::vir_format!(
                        self.vcx,
                        "ignored repack op: {other:?}"
                    )));
                } else {
                    self.stmt(self.vcx.mk_comment_stmt(vir::vir_format!(
                        self.vcx,
                        "unsupported repack op: {other:?}"
                    )));
                    self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                }
            }
        }
    }

    fn unpack(
        &mut self,
        place: Place<'vir>,
        guide: Option<RepackGuide>,
        target_places: &[Place<'vir>],
        label: Option<OldLabel<'vir>>,
    ) {
        let place_enc = self.encode_place(place);
        let place_ty = place_enc.ty;
        let data = self.ty_use_purified(place_ty.ty);

        let self_decl = self.place_to_local_decl.get(&place).map_or_else(
            || self.local_defs.locals[place.local].local_snap,
            |local_data| self.vcx.mk_local_decl(local_data.name, local_data.ty),
        );
        let self_snap = self.vcx.mk_local_ex(self_decl);

        match &data.specifics {
            TySpecifics::Param(_) | TySpecifics::Primitive(_) => unreachable!(),
            TySpecifics::Opaque(_) => panic!("cannot unpack opaque type"),
            TySpecifics::EnumLike(data) => match guide {
                Some(RepackGuide::Downcast(sym, vid)) => {
                    let variant_name = vir::vir_format_identifier!(
                        self.vcx,
                        "{}_as_{}",
                        self_decl.name,
                        sym.map_or(String::from("variant_") + &vid.index().to_string(), |sym| {
                            sym.to_string()
                        })
                    )
                    .to_str();
                    let lhs = self.vcx.mk_local_decl(variant_name, self_decl.ty);
                    self.stmt(self.vcx.mk_pure_assign_stmt(lhs.expr(self.vcx), self_snap));
                    self.declared_vars.insert((variant_name, self_decl.ty));
                    self.place_to_local_decl.insert(target_places[0], lhs);
                }
                None if let Some(vid) = place_ty.variant_index => {
                    let data = &data.variants[vid.as_usize()].inner;
                    for (idx, field) in data.fields.iter().enumerate() {
                        let field_name = vir::vir_format_identifier!(
                            self.vcx,
                            "{}_field_{}",
                            self_decl.name,
                            idx
                        )
                        .to_str();
                        let rhs = field.field_snap(self_snap.downcast_ty());
                        let lhs = self.vcx.mk_local_decl(field_name, rhs.ty());
                        self.stmt(self.vcx.mk_pure_assign_stmt(lhs.expr(self.vcx), rhs));
                        self.declared_vars.insert((field_name, rhs.ty()));
                        self.place_to_local_decl.insert(target_places[idx], lhs);
                    }
                }
                _ => return,
            },
            TySpecifics::StructLike(data) => {
                for (idx, field) in data.fields.iter().enumerate() {
                    let field_name =
                        vir::vir_format_identifier!(self.vcx, "{}_field_{}", self_decl.name, idx)
                            .to_str();
                    let rhs = field.field_snap(self_snap.downcast_ty());
                    let lhs = self.vcx.mk_local_decl(field_name, rhs.ty());
                    self.stmt(self.vcx.mk_pure_assign_stmt(lhs.expr(self.vcx), rhs));
                    self.declared_vars.insert((field_name, rhs.ty()));
                    self.place_to_local_decl.insert(target_places[idx], lhs);
                }
            }
            TySpecifics::ImmRef(data) => {
                let value_name =
                    vir::vir_format_identifier!(self.vcx, "{}_value", self_decl.name).to_str();
                let rhs = data.value_access(self_snap.downcast_ty());
                let lhs = self.vcx.mk_local_decl(value_name, rhs.ty());
                self.stmt(self.vcx.mk_pure_assign_stmt(lhs.expr(self.vcx), rhs));
                self.declared_vars.insert((value_name, rhs.ty()));
                self.place_to_local_decl.insert(target_places[0], lhs);
            }
            TySpecifics::MutRef(data) => {
                let value_name =
                    vir::vir_format_identifier!(self.vcx, "{}_value", self_decl.name).to_str();
                let rhs = data.value_access(self_snap.downcast_ty());
                let lhs = self.vcx.mk_local_decl(value_name, rhs.ty());
                self.stmt(self.vcx.mk_pure_assign_stmt(lhs.expr(self.vcx), rhs));
                self.declared_vars.insert((value_name, rhs.ty()));
                self.place_to_local_decl.insert(target_places[0], lhs);
            }
        }
    }

    fn pack(
        &mut self,
        place: Place<'vir>,
        guide: Option<RepackGuide>,
        target_places: &[Place<'vir>],
        label: Option<OldLabel<'vir>>,
    ) {
        let place_enc = self.encode_place(place);
        let place_ty = place_enc.ty;
        let data = self.ty_use_purified(place_ty.ty);

        let self_decl = self.place_to_local_decl.get(&place).map_or_else(
            || self.local_defs.locals[place.local].local_snap,
            |local_data| self.vcx.mk_local_decl(local_data.name, local_data.ty),
        );
        let self_snap = self.vcx.mk_local_ex(self_decl);

        match &data.specifics {
            TySpecifics::Param(_) | TySpecifics::Primitive(_) => unreachable!(),
            TySpecifics::Opaque(_) => panic!("cannot pack opaque type"),
            TySpecifics::EnumLike(data) => match guide {
                Some(RepackGuide::Downcast(..)) => {
                    let rhs = self
                        .place_to_local_decl
                        .get(&target_places[0])
                        .unwrap()
                        .expr(self.vcx);
                    self.stmt(self.vcx.mk_pure_assign_stmt(self_snap, rhs));
                }
                None if let Some(vid) = place_ty.variant_index => {
                    let data = &data.variants[vid.as_usize()].inner;
                    for (idx, field) in data.fields.iter().enumerate() {
                        let lhs = field.field_snap(self_snap.downcast_ty());
                        let rhs = self
                            .place_to_local_decl
                            .get(&target_places[idx])
                            .unwrap()
                            .expr(self.vcx);
                        self.stmt(self.vcx.mk_pure_assign_stmt(lhs, rhs));
                    }
                }
                _ => return,
            },
            TySpecifics::StructLike(data) => {
                for (idx, field) in data.fields.iter().enumerate() {
                    let lhs = field.field_snap(self_snap.downcast_ty());
                    let rhs = self
                        .place_to_local_decl
                        .get(&target_places[idx])
                        .unwrap()
                        .expr(self.vcx);
                    self.stmt(self.vcx.mk_pure_assign_stmt(lhs, rhs));
                }
            }
            TySpecifics::ImmRef(data) => {
                let lhs = data.value_access(self_snap.downcast_ty());
                let rhs = self
                    .place_to_local_decl
                    .get(&target_places[0])
                    .unwrap()
                    .expr(self.vcx);
                self.stmt(self.vcx.mk_pure_assign_stmt(lhs, rhs));
            }
            TySpecifics::MutRef(data) => {
                let lhs = data.value_access(self_snap.downcast_ty());
                let rhs = self
                    .place_to_local_decl
                    .get(&target_places[0])
                    .unwrap()
                    .expr(self.vcx);
                self.stmt(self.vcx.mk_pure_assign_stmt(lhs, rhs));
            }
        }
    }

    fn loop_analysis(&mut self) -> &LoopAnalysis {
        self.fpcs_analysis.analysis().loop_analysis()
    }

    fn loop_place_usages(&mut self, block: mir::BasicBlock) -> Option<PlaceUsages<'vir>> {
        self.fpcs_analysis
            .analysis()
            .loop_place_usages(block)
            .cloned()
    }

    fn loop_head_of(&mut self, block: mir::BasicBlock) -> Option<LoopId> {
        self.loop_analysis().loop_head_of(block)
    }

    fn pcs_succ<'a>(&mut self, pcg_state: &Pcg<'_, 'vir>, succ: &'a PcgSuccessor<'_, 'vir>) {
        let edge_to_loop = self.loop_head_of(succ.block()).is_some();
        self.pcg_actions(pcg_state, succ.actions(), edge_to_loop);
    }

    fn encode_operand(
        &mut self,
        operand: &mir::Operand<'vir>,
    ) -> EncodeResult<'vir, vir::ExprSnap<'vir>, E> {
        let ty = operand.ty(self.local_decls, self.vcx.tcx());
        let (encode_place_result, ty_out) = match operand {
            &mir::Operand::Move(source) => {
                return Ok(self.encode_place(Place::from(source)).snap);
            }
            &mir::Operand::Copy(_source) => {
                let ty_out = self.ty_use_purified(ty);
                (self.encode_operand_snap(operand, &())?, ty_out)
            }
            mir::Operand::Constant(box constant) => {
                let ty_out = self.ty_use_purified(ty);
                let constant = self.encode_constant_snap(constant)?;
                (constant.upcast_ty(), ty_out)
            }
        };
        let tmp_exp = self.new_tmp(&ty_out.data.snapshot).expr(self.vcx);
        self.stmt(self.vcx.mk_pure_assign_stmt(tmp_exp, encode_place_result));
        Ok(tmp_exp)
    }

    /// Encodes the snapshot of an operand. This should not be used for encoding
    /// regular mir statements/terminators as it doesn't match the semantics.
    fn encode_operand_snap_immediate(
        &mut self,
        operand: &mir::Operand<'vir>,
    ) -> Result<vir::ExprSnap<'vir>, EncodeFullError<'vir, E>> {
        match operand {
            &mir::Operand::Move(source) | &mir::Operand::Copy(source) => {
                Ok(self.encode_place_with_snap(Place::from(source)).1)
            }
            mir::Operand::Constant(box constant) => {
                Ok(self.encode_constant_snap(constant)?.upcast_ty())
            }
        }
    }

    pub(crate) fn encode_place(&mut self, place: Place<'vir>) -> EncodePlaceResult<'vir> {
        if let Some(decl) = self.place_to_local_decl.get(&place) {
            return EncodePlaceResult {
                snap: decl.expr(self.vcx),
                ty: place.ty(self.pcg_ctxt()),
            };
        }
        let mut place_ty = mir::PlaceTy::from_ty(self.local_decls[place.local].ty);
        let mut result = self.local_defs[place.local].local_ex;
        for (place, elem) in place.iter_projections() {
            result = self.encode_place_element(place.into(), elem, result);
            place_ty = place_ty.projection_ty(self.vcx.tcx(), elem);
        }
        EncodePlaceResult {
            snap: result,
            ty: place_ty,
        }
    }

    pub(crate) fn encode_place_with_snap(
        &mut self,
        place: Place<'vir>,
    ) -> (
        EncodePlaceResult<'vir>,
        vir::ExprSnap<'vir>,
        mir::PlaceTy<'vir>,
        TyUsePurified<'vir>,
    ) {
        let ty = (*place).ty(self.local_decls, self.vcx.tcx());
        assert!(ty.variant_index.is_none());

        let ty_out = self.ty_use_purified(ty.ty);
        let result = self.encode_place(place);
        let snap = self
            .place_to_local_decl
            .get(&place)
            .map_or(result.snap, |local_data| {
                self.vcx
                    .mk_local_ex(self.vcx.mk_local_decl(local_data.name, local_data.ty))
            });
        (result, snap, ty, ty_out)
    }

    fn encode_place_element(
        &mut self,
        place: Place<'vir>,
        elem: mir::PlaceElem<'vir>,
        expr: vir::ExprSnap<'vir>,
    ) -> vir::ExprSnap<'vir> {
        if let Some(decl) = self.place_to_local_decl.get(&place) {
            return decl.expr(self.vcx);
        }
        let place_ty = place.ty(self.pcg_ctxt());
        match elem {
            mir::ProjectionElem::Field(field_idx, _) => self
                .ty_use_purified(place_ty.ty)
                .expect_variant_opt(place_ty.variant_index)
                .fields[field_idx.as_usize()]
            .field_snap(expr.downcast_ty()),
            mir::ProjectionElem::Downcast(..) => expr,
            mir::ProjectionElem::Deref => {
                assert!(place_ty.variant_index.is_none());
                let e_ty = self.ty_use_purified(place_ty.ty);
                match place_ty.ty.kind() {
                    ty::TyKind::Adt(adt, _) if adt.is_box() => {
                        e_ty.expect_variant_opt(place_ty.variant_index).fields[0]
                            .field_snap(expr.downcast_ty())
                    }
                    ty::TyKind::Ref(_, _, ty::Mutability::Not) => {
                        e_ty.expect_immref().value_access(expr.downcast_ty())
                    }
                    ty::TyKind::Ref(_, _, ty::Mutability::Mut) => {
                        e_ty.expect_mutref().value_access(expr.downcast_ty())
                    }
                    ty_kind => unreachable!("{ty_kind:?}"),
                }
            }
            _ => todo!("Unsupported ProjectionElem {:?}", elem),
        }
    }

    fn new_tmp<T: CompType>(&mut self, ty: vir::Type<'vir, T>) -> vir::LocalDecl<'vir, T> {
        let name = vir::vir_format!(self.vcx, "_tmp{}", self.tmp_ctr);
        let local = vir::vir_local_decl! { self.vcx; [name] : [ty] };
        self.tmp_ctr += 1;
        self.stmt(self.vcx.mk_local_decl_stmt(local, None));
        // self.vcx.mk_local_ex(local)
        local
    }

    pub(crate) fn new_label(&mut self, base: &str) -> &'vir str {
        let name = vir::vir_format!(self.vcx, "{base}{}", self.label_ctr);
        self.label_ctr += 1;
        self.stmt(self.vcx.mk_label_stmt(name));
        name
    }

    pub(crate) fn get_location_label(&self, at: SnapshotLocation) -> vir::OldLabel<'vir> {
        if let SnapshotLocation::BeforeJoin(bb) | SnapshotLocation::Loop(bb) = at {
            return vir::OldLabel::Block(vir::CfgBlockLabelData::BasicBlock(bb.as_usize()));
        }
        let prefix = match at {
            SnapshotLocation::Before(..) => LocationLabelPrefix::Before,
            SnapshotLocation::After(..) => LocationLabelPrefix::After,
            SnapshotLocation::BeforeRefReassignment(..) => {
                LocationLabelPrefix::BeforeRefReassignment
            }
            SnapshotLocation::Loop(_) | SnapshotLocation::BeforeJoin(_) => unreachable!(),
        };
        let location = at.location();
        let label = self.location_label(prefix, location);
        vir::OldLabel::Label(label)
    }

    pub(crate) fn location_label(
        &self,
        prefix: LocationLabelPrefix,
        location: mir::Location,
    ) -> &'vir str {
        vir::vir_format!(
            self.vcx,
            "_{}_{}_{}",
            prefix.to_str(),
            location.block.index(),
            location.statement_index
        )
    }

    fn new_before_label(&mut self, location: mir::Location) {
        let label = self.location_label(LocationLabelPrefix::Before, location);
        self.stmt(self.vcx.mk_label_stmt(label));
    }

    fn set_from_to_flag(&mut self, from: mir::BasicBlock, to: mir::BasicBlock) -> vir::Stmt<'vir> {
        self.from_to_vars.set_from_to_flag_stmt(self.vcx, from, to)
    }
}

impl<'vir, 'enc, E: TaskEncoder> PureRvalueEnc<'vir> for PurifiedEncVisitor<'vir, 'enc, E> {
    type Encoder = E;
    type EncodePlaceCtxt = ();
    type ExprCurr = ();
    type ExprNext = !;
    fn def_id(&self) -> DefId {
        self.def_id
    }

    fn deps(&mut self) -> &mut TaskEncoderDependencies<'vir, Self::Encoder> {
        self.deps
    }

    fn vcx(&self) -> &'vir vir::VirCtxt<'vir> {
        self.vcx
    }

    fn body(&self) -> &mir::Body<'vir> {
        self.body
    }

    fn ty_use_pure(&mut self, ty: ty::Ty<'vir>) -> TyUsePure<'vir> {
        let ty_task = RustTyDecomposition::from_ty(ty, self.vcx.tcx(), self.def_id);
        self.deps.require_dep::<TyUsePureEnc>(ty_task).unwrap()
    }

    fn encode_operand_snap(
        &mut self,
        operand: &mir::Operand<'vir>,
        _ctxt: &Self::EncodePlaceCtxt,
    ) -> Result<vir::ExprSnap<'vir>, EncodeFullError<'vir, E>> {
        match operand {
            &mir::Operand::Move(source) => {
                let (result, snap_val, _, ty_out) =
                    self.encode_place_with_snap(Place::from(source));

                let tmp_exp = self.new_tmp(ty_out.data.snapshot).expr(self.vcx);
                self.stmt(self.vcx.mk_pure_assign_stmt(tmp_exp, snap_val));
                Ok(tmp_exp)
            }
            &mir::Operand::Copy(place) => {
                Ok(self.encode_place_with_snap(place.into()).1)
                // let place_expr =
                //     if let Some(local_data) = self.place_to_local_decl.get(&place.into()) {
                //         return self
                //             .vcx
                //             .mk_local_ex(self.vcx.mk_local_decl(local_data.name, local_data.ty));
                //     } else {
                //         self.local_defs.locals[place.local].local_ex
                //     };

                // let mut place_ty = mir::PlaceTy::from_ty(self.local_decls[place.local].ty);
                // let mut encoded_place = mir::Place::from(place.local);

                // let mut crossed_ref =
                //     matches!(place_ty.ty.kind(), TyKind::Ref(_, _, ty::Mutability::Not));
                // let mut result = place_expr.as_dyn();
                // for elem in place.projection {
                //     if crossed_ref {
                //         use vir::Reify;
                //         let (expr, _) = crate::encoders::mir_pure::Enc::encode_place_element(
                //             self.deps,
                //             place_ty,
                //             elem,
                //             result.lift().downcast_ty(),
                //         );
                //         result = expr.reify(self.vcx, (self.def_id, &[])).as_dyn();
                //     } else {
                //         let maybe_local = self.place_to_local_decl.get(&encoded_place.into());
                //         result = if let Some(local) = maybe_local {
                //             self.vcx.mk_local_ex_local(local)
                //         } else {
                //             self.encode_place_element(place_ty, elem, result.downcast_ty())
                //         }
                //         .as_dyn();
                //     }
                //     place_ty = place_ty.projection_ty(self.vcx.tcx(), elem);
                //     encoded_place = encoded_place.project_deeper(&[elem], self.vcx.tcx());
                //     if !crossed_ref
                //         && matches!(place_ty.ty.kind(), TyKind::Ref(_, _, ty::Mutability::Not))
                //     {
                //         let ty_out = self.ty_use_purified(place_ty.ty);
                //         result = ty_out.expect_immref().value(result.downcast_ty()).as_dyn();
                //         crossed_ref = true;
                //     }
                // }
                // result.downcast_ty()
            }
            mir::Operand::Constant(box constant) => {
                Ok(self.encode_constant_snap(constant)?.upcast_ty())
            }
        }
    }

    fn encode_place_snap(
        &mut self,
        place: Place<'vir>,
        _ctxt: &Self::EncodePlaceCtxt,
    ) -> vir::ExprGenSnap<'vir, Self::ExprCurr, Self::ExprNext> {
        self.encode_place_with_snap(place).1
    }
}

impl<'vir, 'enc, E: TaskEncoder> mir::visit::Visitor<'vir> for PurifiedEncVisitor<'vir, 'enc, E> {
    fn visit_basic_block_data(&mut self, block: mir::BasicBlock, data: &mir::BasicBlockData<'vir>) {
        // We are verifying the absence of panics, so cleanup block should never
        // be reached, or even referenced.
        if data.is_cleanup {
            self.encoded_blocks.push(
                self.vcx.mk_cfg_block(
                    self.vcx
                        .alloc(vir::CfgBlockLabelData::BasicBlock(block.as_usize())),
                    &[],
                    &[],
                    self.vcx
                        .mk_dummy_stmt(vir::vir_format!(self.vcx, "cleanup block",)),
                ),
            );
            return;
        }
        if self.deps.check_cycle().is_err() {
            return;
        }

        self.current_stmts = Some(Vec::with_capacity(
            data.statements.len(), // TODO: not exact?
        ));
        self.current_block_label = Some(
            self.vcx
                .alloc(vir::CfgBlockLabelData::BasicBlock(block.as_usize())),
        );
        let cfpcs = self.fpcs_analysis.get_all_for_bb(block).unwrap().unwrap();

        // Calculate invariant at loop head
        let invariant = self
            .loop_place_usages(block)
            .map(|place_usages| self.get_loop_inv(&cfpcs, &place_usages, self.pcg_ctxt()))
            .unwrap_or_default();

        self.current_fpcs = Some(cfpcs);

        /*
        let mut phi_stmts = vec![];
        if let Some(phi_nodes) = self.ssa_analysis.phi.get(&block) {
            for phi_node in phi_nodes {
                assert!(!phi_node.sources.is_empty());
                let local_ty = &self.local_types[phi_node.local];
                let expr = phi_node.sources.iter()
                    .fold(self.vcx.mk_func_app(
                        local_ty.function_unreachable,
                        &[],
                    ), |prev, source| self.vcx.alloc(vir::ExprData::Ternary(self.vcx.alloc(vir::TernaryData {
                        cond: self.vcx.mk_local_ex(vir::vir_format_identifier!(self.vcx, "_reach_bb{}", source.0.as_usize())),
                        then: self.vcx.mk_local_ex(vir::vir_format_identifier!(self.vcx, "_{}s_{}", phi_node.local.as_usize(), source.1)),
                        else_: prev,
                    }))));
                phi_stmts.push(vir::StmtData::LocalDecl(self.vcx.alloc(vir::LocalDeclData {
                    name: vir::vir_format_identifier!(self.vcx, "_{}s_{}", phi_node.local.as_usize(), phi_node.new_version),
                    ty: self.local_types[phi_node.local].snapshot,
                    expr: Some(expr),
                })));
            }
        }
        for phi_stmt in phi_stmts {
            self.stmt(phi_stmt);
        }
        */
        assert!(self.current_terminator.is_none());
        self.super_basic_block_data(block, data);
        let stmts = self.current_stmts.take().unwrap();
        let terminator = self.current_terminator.take().unwrap();
        self.encoded_blocks.push(self.vcx.mk_cfg_block(
            self.current_block_label.take().unwrap(),
            invariant,
            self.vcx.alloc_slice(&stmts),
            terminator,
        ));
    }

    fn visit_statement(&mut self, statement: &mir::Statement<'vir>, location: mir::Location) {
        self.vcx.with_span(statement.source_info.span, |_vcx| {
            if self.deps.check_cycle().is_err() {
                return;
            }

            comment!(self, "[MIR] {location:?}: {statement:?}");

            let current_fpcs = self.current_fpcs.take().unwrap();
            let cfpcs = &current_fpcs.statements[location.statement_index];
            for phase in EvalStmtPhase::phases() {
                self.pcg_actions(&cfpcs.states[phase], &cfpcs.actions(phase), false);
            }
            self.current_fpcs = Some(current_fpcs);

            // TODO: these should not be ignored, but should havoc the local instead
            // This clears up the noise a bit, making sure StorageLive and other
            // kinds do not show up in the comments.
            // TODO: also make sure we don't ignore PCG annotations for these,
            //   *if* the pcs calls for mid-statement are moved later.
            const IGNORE_NOP_STMTS: bool = true;
            if IGNORE_NOP_STMTS {
                match &statement.kind {
                    mir::StatementKind::StorageLive(..) | mir::StatementKind::StorageDead(..) => {
                        return;
                    }
                    _ => {}
                }
            }

            let span = statement.source_info.span;

            match &statement.kind {
                mir::StatementKind::Assign(box (dest, rvalue)) => {
                    let proj_enc = self.encode_place(Place::from(*dest)).snap;
                    let rval_enc = self.encode_rvalue(rvalue, span);

                    match rval_enc {
                        Ok(rval_enc) => {
                            let dest_ty = dest.ty(self.local_decls, self.vcx.tcx());
                            assert!(dest_ty.variant_index.is_none());
                            let dest_ty_out = self.ty_use_purified(dest_ty.ty);
                            self.stmt(self.vcx.mk_pure_assign_stmt(proj_enc, rval_enc));
                        }
                        Err(_) => {
                            self.vcx.with_span(span, |vcx| {
                                let error_msg =
                                    format!("unsupported rvalue {rvalue:?} might be reached");
                                vcx.handle_error("exhale.failed:assertion.false", move |_| {
                                    Some(vec![PrustiError::verification(&error_msg, span.into())])
                                });
                                self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                            });
                        }
                    }
                }

                // no-ops
                    mir::StatementKind::StorageLive(..)
                    | mir::StatementKind::StorageDead(..)
                    | mir::StatementKind::FakeRead(_)
                    | mir::StatementKind::PlaceMention(_)
                    | mir::StatementKind::AscribeUserType(..)
                    | mir::StatementKind::Coverage(_)
                    | mir::StatementKind::ConstEvalCounter
                    | mir::StatementKind::Nop
                    | mir::StatementKind::BackwardIncompatibleDropHint { .. } => {}

                    mir::StatementKind::Intrinsic(intrinsic_kind) => {
                        let intrinsic_kind = intrinsic_kind.clone();
                        self.vcx.with_span(span, |vcx| {
                            vcx.handle_error("exhale.failed:assertion.false", move |_| {
                                Some(vec![PrustiError::verification(
                                    format!("unsupported intrinsic statement {intrinsic_kind:?} might be reached"),
                                    span.into(),
                                )])
                            });
                            self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                        });
                    }

                    mir::StatementKind::Retag(..)
                    | mir::StatementKind::SetDiscriminant { .. }
                    | mir::StatementKind::Deinit(..) => unreachable!(
                        "the statement kind {:?} is not allowed in the MIR analysis phase",
                        statement.kind
                    ),
            }
        });
    }

    fn visit_terminator(&mut self, terminator: &mir::Terminator<'vir>, location: mir::Location) {
        if self.deps.check_cycle().is_err() {
            return;
        }
        self.new_before_label(location);
        comment!(self, "[MIR] {location:?}: {:?}", terminator.kind);
        let span = terminator.source_info.span;

        let current_fpcs = self.current_fpcs.take().unwrap();
        let cfpcs = &current_fpcs.statements[location.statement_index];
        for phase in EvalStmtPhase::phases() {
            comment!(self, "PCG (T) {phase}");
            self.pcg_actions(&cfpcs.states[phase], &cfpcs.actions(phase), false)
                .unwrap();
        }
        self.current_fpcs = Some(current_fpcs);

        let terminator = match &terminator.kind {
            mir::TerminatorKind::Goto { target }
            | mir::TerminatorKind::FalseUnwind {
                real_target: target,
                ..
            }
            | mir::TerminatorKind::FalseEdge {
                real_target: target,
                ..
            } => {
                const REAL_TARGET_SUCC_IDX: usize = 0;
                // Ensure that the terminator succ that we use for the repacks is the correct one
                assert_eq!(
                    &self.current_fpcs.as_ref().unwrap().terminator.succs[REAL_TARGET_SUCC_IDX]
                        .block(),
                    target
                );
                let current_fpcs = self.current_fpcs.take().unwrap();
                let borrows =
                    current_fpcs.statements.last().unwrap().states[EvalStmtPhase::PostMain].clone();
                self.pcs_succ(
                    &borrows,
                    &current_fpcs.terminator.succs[REAL_TARGET_SUCC_IDX],
                );
                self.current_fpcs = Some(current_fpcs);
                let set_flag = self.set_from_to_flag(location.block, *target);
                self.stmt(set_flag);
                self.vcx.mk_goto_stmt(
                    self.vcx
                        .alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize())),
                )
            }
            mir::TerminatorKind::SwitchInt { discr, targets } => {
                let discr_ty_rs = discr.ty(self.local_decls, self.vcx.tcx());
                let discr_ty = self.ty_use_purified(discr_ty_rs).expect_primitive();

                let goto_targets = self.vcx.alloc_slice(
                    &targets
                        .iter()
                        .enumerate()
                        .map(|(idx, (value, target))| {
                            assert_eq!(
                                self.current_fpcs.as_ref().unwrap().terminator.succs[idx].block(),
                                target
                            );

                            let current_fpcs = self.current_fpcs.take().unwrap();
                            let borrows = &current_fpcs.statements.last().unwrap().states
                                [EvalStmtPhase::PostMain];
                            let mut extra_stmts =
                                self.collect_pcs_succ(borrows, &current_fpcs.terminator.succs[idx]);
                            self.current_fpcs = Some(current_fpcs);
                            extra_stmts.push(self.set_from_to_flag(location.block, target));

                            self.vcx.mk_goto_if_target(
                                discr_ty.expr_from_bits(discr_ty_rs, value).as_dyn(),
                                self.vcx
                                    .alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize())),
                                self.vcx.alloc_slice(&extra_stmts),
                            )
                        })
                        .collect::<Vec<_>>(),
                );
                let goto_otherwise = self.vcx.alloc(vir::CfgBlockLabelData::BasicBlock(
                    targets.otherwise().as_usize(),
                ));

                let otherwise_succ_idx = goto_targets.len();
                assert_eq!(
                    self.current_fpcs.as_ref().unwrap().terminator.succs[otherwise_succ_idx]
                        .block(),
                    targets.otherwise()
                );

                let current_fpcs = self.current_fpcs.take().unwrap();
                let borrows =
                    &current_fpcs.statements.last().unwrap().states[EvalStmtPhase::PostMain];
                let mut otherwise_stmts = self
                    .collect_pcs_succ(borrows, &current_fpcs.terminator.succs[otherwise_succ_idx]);
                self.current_fpcs = Some(current_fpcs);
                otherwise_stmts.push(self.set_from_to_flag(location.block, targets.otherwise()));

                let discr_ex = (discr_ty.expect_native().snap_to_prim)(
                    self.encode_operand_snap(discr, &()).unwrap().downcast_ty(),
                );
                self.vcx.mk_goto_if_stmt(
                    discr_ex.as_dyn(), // self.vcx.mk_local_ex(discr_name),
                    goto_targets,
                    goto_otherwise,
                    self.vcx.alloc_slice(&otherwise_stmts),
                )
            }
            mir::TerminatorKind::Return => {
                let current_fpcs = self.current_fpcs.take().unwrap();
                let borrows = current_fpcs.statements.last().unwrap().states
                    [EvalStmtPhase::PostMain]
                    .borrow_pcg();
                let proof_packages = self.package_proofs(borrows).unwrap();
                self.current_fpcs = Some(current_fpcs);
                self.stmts(proof_packages);

                self.vcx
                    .mk_goto_stmt(self.vcx.alloc(vir::CfgBlockLabelData::End))
            }
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
                // emit the current block, create a new label for the terminator
                // TODO: should we do this for any other terminators?
                let current_block = match self.current_block_label {
                    Some(vir::CfgBlockLabelData::BasicBlock(block)) => *block,
                    _ => unreachable!(),
                };
                self.encoded_blocks.push(
                    self.vcx.mk_cfg_block(
                        self.current_block_label
                            .replace(
                                self.vcx.alloc(vir::CfgBlockLabelData::BasicBlockTerminator(
                                    current_block,
                                )),
                            )
                            .unwrap(),
                        &[],
                        self.vcx
                            .alloc_slice(&self.current_stmts.replace(Vec::new()).unwrap()),
                        self.vcx
                            .mk_goto_stmt(self.vcx.alloc(
                                vir::CfgBlockLabelData::BasicBlockTerminator(current_block),
                            )),
                    ),
                );

                let func_ty = func.ty(self.body, self.vcx.tcx());
                let (func_def_id, caller_substs) =
                    RustSignature::get_def_id_and_caller_substs(func_ty);
                let is_pure = crate::encoders::with_proc_spec(
                    SpecQuery::GetProcKind(
                        func_def_id,
                        ty::List::identity_for_item(self.vcx.tcx(), func_def_id),
                    ),
                    |spec| spec.kind.is_pure().unwrap_or_default(),
                )
                .unwrap_or_default();

                let dest = self.encode_place(Place::from(*destination)).snap;
                if is_pure {
                    let pure_func = self
                        .deps
                        .require_dep::<FunctionCallEnc>(CallTaskDescription::new(
                            self.def_id,
                            caller_substs,
                            func_def_id,
                        ))
                        .unwrap();
                    let snap_args = args
                        .iter()
                        .map(|arg| {
                            self.vcx.with_span(arg.span, |_| {
                                self.encode_operand_snap(&arg.node, &()).unwrap()
                            })
                        })
                        .collect::<Vec<_>>();
                    let pure_func_app = pure_func.call(snap_args);
                    let assign_stmt = self.vcx.mk_pure_assign_stmt(dest, pure_func_app);
                    self.stmt(assign_stmt);
                } else {
                    vir::with_vcx(|vcx| {
                        vcx.with_span(terminator.source_info.span, |vcx| {
                            let Ok(func_out) =
                                self.deps.require_dep::<encoders::PurifiedMethodCallEnc>(
                                    CallTaskDescription::new(
                                        self.def_id,
                                        caller_substs,
                                        func_def_id,
                                    ),
                                )
                            else {
                                self.current_terminator = Some(
                                    self.vcx
                                        .mk_dummy_stmt(vir::vir_format!(self.vcx, "recursion",)),
                                );
                                return;
                            };

                            /// Recursively checks for mutable types
                            fn has_mut(typ: ty::Ty) -> bool {
                                match typ.kind() {
                                    TyKind::Ref(.., ty::Mutability::Mut)
                                    | TyKind::RawPtr(.., ty::Mutability::Mut) => true,
                                    // TyKind::Adt(_, args) => args
                                    //     .iter()
                                    //     .any(|arg| arg.as_type().map_or(false, |typ| has_mut(typ))),
                                    // TyKind::Tuple(typs) => typs.iter().any(|typ| has_mut(typ)),
                                    _ => false,
                                }
                            }

                            let method_in = args
                                .iter()
                                .map(|arg| self.encode_operand(&arg.node).unwrap())
                                .collect::<Vec<_>>();

                            let method_out = std::iter::once(dest)
                                .chain(
                                    args.iter()
                                        .filter(|arg| {
                                            has_mut(arg.node.ty(self.local_decls, self.vcx.tcx()))
                                        })
                                        .map(|arg| self.encode_operand(&arg.node).unwrap()),
                                )
                                .collect::<Vec<_>>();

                            let tmps = method_out
                                .iter()
                                .map(|out| self.new_tmp(out.ty()))
                                .collect::<Vec<_>>();

                            let call = func_out.call(
                                method_in,
                                self.vcx.alloc_slice(
                                    &tmps.iter().map(|tmp| tmp.as_dyn()).collect::<Vec<_>>(),
                                ),
                            );

                            let label_pre = self.new_label("pre");
                            vcx.handle_error(
                                "call.precondition:assertion.false",
                                move |reason_span_opt| {
                                    let mut error = PrustiError::verification(
                                        "precondition might not hold",
                                        span.into(),
                                    );
                                    if let Some(reason_span) = reason_span_opt {
                                        error.add_note_mut(
                                            "the failing precondition is here",
                                            Some(reason_span.into()),
                                        );
                                    }
                                    Some(vec![error])
                                },
                            );
                            self.stmts(call);
                            let label_post = self.new_label("post");
                            self.stmts(
                                method_out
                                    .iter()
                                    .zip(tmps.iter())
                                    .map(|(out, tmp)| vcx.mk_pure_assign_stmt(out, tmp.expr(vcx)))
                                    .collect::<Vec<_>>(),
                            );

                            // for ((_, tmp_expr), (arg_expr, arg, fn_arg_ty)) in
                            //     tmps.iter().zip(ref_muts.iter())
                            // {
                            //     let local_decls = self.local_decls_src();
                            //     let arg_ty = arg.node.ty(local_decls, self.vcx.tcx());
                            //     let caster = self
                            //         .deps()
                            //         .require_ref::<CastToEnc<CastTypePure>>(CastArgs {
                            //             expected: arg_ty,
                            //             actual: **fn_arg_ty,
                            //         })
                            //         .unwrap();
                            //     let tmp_expr = if arg_expr.ty() == tmp_expr.ty() {
                            //         tmp_expr
                            //     } else {
                            //         caster.apply_cast_if_necessary(self.vcx, tmp_expr)
                            //     };
                            //     self.stmt(self.vcx.mk_pure_assign_stmt(arg_expr, tmp_expr));
                            // }

                            self.call_labels
                                .insert(location.block, (label_pre, label_post));
                        })
                    });
                }

                target
                    .map(|target| {
                        const REAL_TARGET_SUCC_IDX: usize = 0;
                        // Ensure that the terminator succ that we use for the repacks is the correct one
                        assert_eq!(
                            self.current_fpcs.as_ref().unwrap().terminator.succs
                                [REAL_TARGET_SUCC_IDX]
                                .block(),
                            target
                        );
                        let current_fpcs = self.current_fpcs.take().unwrap();
                        let borrows = current_fpcs.statements.last().unwrap().states
                            [EvalStmtPhase::PostMain]
                            .clone();
                        self.pcs_succ(
                            &borrows,
                            &current_fpcs.terminator.succs[REAL_TARGET_SUCC_IDX],
                        );
                        self.current_fpcs = Some(current_fpcs);
                        let set_flag = self.set_from_to_flag(location.block, target);
                        self.stmt(set_flag);

                        self.vcx.mk_goto_stmt(
                            self.vcx
                                .alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize())),
                        )
                    })
                    .unwrap_or_else(|| {
                        // TODO: detect panic causes, adjust message accordingly
                        self.vcx.with_span(span, |vcx| {
                            vcx.handle_error("exhale.failed:assertion.false", move |_| {
                                Some(vec![PrustiError::verification(
                                    "unreachable statement might be reached",
                                    span.into(),
                                )])
                            });
                            self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                            self.vcx.mk_assume_false_stmt()
                        })
                    })
            }
            // If we are not checking for overflows, encode an overflow-checking
            // assertion as a goto.
            mir::TerminatorKind::Assert { msg, target, .. }
                if !config::check_overflows()
                    && matches!(
                        **msg,
                        mir::AssertMessage::Overflow(..) | mir::AssertMessage::OverflowNeg(..)
                    ) =>
            {
                const REAL_TARGET_SUCC_IDX: usize = 0;
                // Ensure that the terminator succ that we use for the repacks is the correct one
                assert_eq!(
                    &self.current_fpcs.as_ref().unwrap().terminator.succs[REAL_TARGET_SUCC_IDX]
                        .block(),
                    target
                );
                let current_fpcs = self.current_fpcs.take().unwrap();
                let borrows =
                    current_fpcs.statements.last().unwrap().states[EvalStmtPhase::PostMain].clone();
                self.pcs_succ(
                    &borrows,
                    &current_fpcs.terminator.succs[REAL_TARGET_SUCC_IDX],
                );
                self.current_fpcs = Some(current_fpcs);
                let set_flag = self.set_from_to_flag(location.block, *target);
                self.stmt(set_flag);
                self.vcx.mk_goto_stmt(
                    self.vcx
                        .alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize())),
                )
            }
            mir::TerminatorKind::Assert {
                cond,
                expected,
                msg,
                target,
                ..
            } => {
                const REAL_TARGET_SUCC_IDX: usize = 0;
                // Ensure that the terminator succ that we use for the repacks is the correct one
                assert_eq!(
                    &self.current_fpcs.as_ref().unwrap().terminator.succs[REAL_TARGET_SUCC_IDX]
                        .block(),
                    target,
                );
                let current_fpcs = self.current_fpcs.take().unwrap();
                let borrows =
                    current_fpcs.statements.last().unwrap().states[EvalStmtPhase::PostMain].clone();
                self.pcs_succ(
                    &borrows,
                    &current_fpcs.terminator.succs[REAL_TARGET_SUCC_IDX],
                );
                self.current_fpcs = Some(current_fpcs);

                let e_bool = self.ty_use_purified(self.vcx.tcx().types.bool);
                let enc = self.encode_operand_snap(cond, &()).unwrap().downcast_ty();
                let enc = (e_bool.expect_purified_native().snap_to_prim)(enc);
                let expected = self.vcx.mk_const_expr(vir::ConstData::Bool(*expected));
                let assert = self.vcx.mk_eq_expr(enc, expected);
                let error_msg = match **msg {
                    mir::AssertMessage::BoundsCheck { .. } => "bounds check may fail",
                    mir::AssertMessage::Overflow(..) | mir::AssertMessage::OverflowNeg(..) => {
                        "operation may overflow"
                    }
                    mir::AssertMessage::DivisionByZero(..)
                    | mir::AssertMessage::RemainderByZero(..) => "division by zero may occur",
                    mir::AssertMessage::ResumedAfterReturn(..) => {
                        "execution may continue after return"
                    }
                    mir::AssertMessage::ResumedAfterPanic(..) => {
                        "execution may continue after panic"
                    }
                    mir::AssertMessage::MisalignedPointerDereference { .. } => {
                        "misaligned pointer may be dereferenced"
                    }
                    mir::AssertKind::ResumedAfterDrop(..) => "execution may continue after drop",
                    mir::AssertKind::NullPointerDereference => "null pointer may be dereferenced",
                    mir::AssertKind::InvalidEnumConstruction(..) => {
                        "invalid enum construction may occur"
                    }
                };
                self.vcx.with_span(span, |vcx| {
                    vcx.handle_error("exhale.failed:assertion.false", move |_| {
                        Some(vec![PrustiError::verification(error_msg, span.into())])
                    });
                    self.stmt(self.vcx.mk_exhale_stmt(assert));
                });
                let set_flag = self.set_from_to_flag(location.block, *target);
                self.stmt(set_flag);
                let target_bb = self
                    .vcx
                    .alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize()));
                self.vcx.mk_goto_stmt(target_bb)
            }
            mir::TerminatorKind::Unreachable => self.vcx.with_span(span, |vcx| {
                vcx.handle_error("exhale.failed:assertion.false", move |_| {
                    Some(vec![PrustiError::verification(
                        "unreachable statement might be reached",
                        span.into(),
                    )])
                });
                self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                self.vcx.mk_assume_false_stmt()
            }),

            mir::TerminatorKind::Drop { target, .. } => {
                let set_flag = self.set_from_to_flag(location.block, *target);
                self.stmt(set_flag);
                self.vcx.mk_goto_stmt(
                    self.vcx
                        .alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize())),
                )
            }

            mir::TerminatorKind::UnwindResume | mir::TerminatorKind::UnwindTerminate(..) => {
                self.vcx.with_span(span, |vcx| {
                    vcx.handle_error("exhale.failed:assertion.false", move |_| {
                        Some(vec![PrustiError::unsupported(
                            "unwind paths are not supported",
                            span.into(),
                        )])
                    });
                    self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                    self.vcx.mk_assume_false_stmt()
                })
            }

            mir::TerminatorKind::TailCall { .. } => self.vcx.with_span(span, |vcx| {
                vcx.handle_error("exhale.failed:assertion.false", move |_| {
                    Some(vec![PrustiError::unsupported(
                        "tail calls are not supported",
                        span.into(),
                    )])
                });
                self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                self.vcx.mk_assume_false_stmt()
            }),
            mir::TerminatorKind::Yield { .. } => self.vcx.with_span(span, |vcx| {
                vcx.handle_error("exhale.failed:assertion.false", move |_| {
                    Some(vec![PrustiError::unsupported(
                        "yield statements are not supported",
                        span.into(),
                    )])
                });
                self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                self.vcx.mk_assume_false_stmt()
            }),
            mir::TerminatorKind::CoroutineDrop => self.vcx.with_span(span, |vcx| {
                vcx.handle_error("exhale.failed:assertion.false", move |_| {
                    Some(vec![PrustiError::unsupported(
                        "coroutines are not supported",
                        span.into(),
                    )])
                });
                self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                self.vcx.mk_assume_false_stmt()
            }),
            mir::TerminatorKind::InlineAsm { .. } => self.vcx.with_span(span, |vcx| {
                vcx.handle_error("exhale.failed:assertion.false", move |_| {
                    Some(vec![PrustiError::unsupported(
                        "inline assembly is not supported",
                        span.into(),
                    )])
                });
                self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                self.vcx.mk_assume_false_stmt()
            }),
        };
        assert!(self.current_terminator.replace(terminator).is_none());
    }
}
