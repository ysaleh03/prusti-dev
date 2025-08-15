use std::alloc::Global;

use pcg::{
    action::{BorrowPcgAction, PcgAction, PcgActions},
    borrow_pcg::{
        action::BorrowPcgActionKind,
        borrow_pcg_edge::BorrowPcgEdge,
        borrow_pcg_expansion::BorrowPcgExpansion,
        edge::{abstraction::AbstractionType, borrow::BorrowEdge, kind::BorrowPcgEdgeKind},
        state::BorrowsState,
        unblock_graph::BorrowPcgUnblockAction,
    },
    free_pcs::{CapabilityKind, PcgBasicBlock, RepackGuide, RepackOp},
    pcg::{EvalStmtPhase, PCGNode, Pcg, PcgSuccessor},
    r#loop::LoopAnalysis,
    utils::{maybe_old::MaybeOldPlace, remote::RemotePlace, CompilerCtxt, HasPlace, Place},
    PcgOutput,
};
use prusti_interface::{specs::specifications::SpecQuery, PrustiError};
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::{
        mir,
        ty::{self, TyKind},
    },
    span::def_id::DefId,
    target::abi,
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CSnap, CallableIdn, CastType, CompType, LocalData, LocalDecl, LocalDeclRef, PSnap};

use crate::{
    encoder_traits::{
        pure_func_app_enc::PureFuncAppEnc,
        purified_function_enc::{PurifiedFunctionEncOutput, PurifiedFunctionEncOutputRef},
    },
    encoders::{
        self,
        domain::DomainEnc,
        lifted::{
            aggregate_cast::{AggregateSnapArgsCastEnc, AggregateSnapArgsCastEncTask},
            casters::{CastersEncOutputRef, MakeConcreteCastFunction, MakeGenericCastFunction},
            func_app_ty_params::LiftedFuncAppTyParamsEnc,
            rust_ty_cast::RustTyGenericCastEncOutput,
        },
        mir_poly_purified::extract_type_expr,
        most_generic_ty::{self, extract_type_params},
        FunctionCallTaskDescription, MirBuiltinEnc, PurifiedWandEnc, PurifiedWandEncTask,
        SnapshotEnc,
    },
};

use super::{
    lifted::{
        cast::{CastArgs, CastToEnc},
        casters::CastTypePure,
        rust_ty_cast::RustTyCastersEnc,
        ty::{EncodeGenericsAsLifted, LiftedTyEnc},
    },
    rust_ty_predicates::{RustTyPredicatesEnc, RustTyPredicatesEncOutputRef},
    ConstEnc, MirMonoPurifiedEnc, MirPolyPurifiedEnc, PurifiedWandEncOutput,
};

pub struct MirPurifiedEnc;

#[derive(Clone, Debug)]
pub enum MirPurifiedEncError {
    // Unsupported,
}

const ENCODE_REACH_BB: bool = false;

impl MirPurifiedEnc {
    pub fn monomorphize() -> bool {
        cfg!(feature = "mono_function_encoding")
    }
}

impl TaskEncoder for MirPurifiedEnc {
    task_encoder::encoder_cache!(MirPurifiedEnc);

    type TaskDescription<'vir> = FunctionCallTaskDescription<'vir>;

    type OutputRef<'vir> = PurifiedFunctionEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = PurifiedFunctionEncOutput<'vir>;

    type EncodingError = MirPurifiedEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let monomorphize = Self::monomorphize();
        let output_ref = if monomorphize {
            deps.require_ref::<MirMonoPurifiedEnc>(*task_key)?
        } else {
            deps.require_ref::<MirPolyPurifiedEnc>(task_key.def_id)?
        };
        deps.emit_output_ref(*task_key, output_ref)?;
        let output: PurifiedFunctionEncOutput<'_> = if monomorphize {
            deps.require_local::<MirMonoPurifiedEnc>(*task_key)?
        } else {
            deps.require_local::<MirPolyPurifiedEnc>(task_key.def_id)?
        };
        Ok((output, ()))
    }
}

pub struct PurifiedEncVisitor<'vir, 'enc, E: TaskEncoder>
where
    'vir: 'enc,
{
    pub vcx: &'vir vir::VirCtxt<'vir>,
    // Are we monomorphizing functions?
    pub monomorphize: bool,
    pub deps: &'enc mut TaskEncoderDependencies<'vir, E>,
    pub def_id: DefId,
    pub local_decls: &'enc mir::LocalDecls<'vir>,
    pub fpcs_analysis: PcgOutput<'enc, 'vir, Global>,
    pub local_defs: crate::encoders::PurifiedLocalDefEncOutput<'vir>,
    pub body: &'enc mir::Body<'vir>,

    pub loop_analysis: LoopAnalysis,
    pub wands: PurifiedWandEncOutput<'vir>,

    pub declared_remotes: FxHashSet<(&'vir str, vir::TypeSnap<'vir>)>,
    pub remote_place_to_local_data: FxHashMap<RemotePlace, vir::LocalSnap<'vir>>,
    pub return_to_remote: FxHashMap<mir::Local, vir::ExprSnap<'vir>>,

    pub declared_vars: FxHashSet<(&'vir str, vir::TypeSnap<'vir>)>,
    pub place_to_local_data: FxHashMap<Place<'vir>, vir::LocalSnap<'vir>>,

    pub tmp_ctr: usize,
    pub label_ctr: usize,
    pub call_labels: FxHashMap<mir::BasicBlock, (&'vir str, &'vir str)>,
    pub from_to_vars: FxHashMap<mir::BasicBlock, Vec<(mir::BasicBlock, &'vir str)>>,

    // for the current basic block
    pub current_fpcs: Option<PcgBasicBlock<'vir>>,

    pub current_block_label: Option<vir::CfgBlockLabel<'vir>>,
    pub current_stmts: Option<Vec<vir::Stmt<'vir>>>,
    pub current_terminator: Option<vir::TerminatorStmt<'vir>>,

    pub encoded_blocks: Vec<vir::CfgBlock<'vir>>, // TODO: use IndexVec ?
}

impl<'vir, E: TaskEncoder> PureFuncAppEnc<'vir, E> for PurifiedEncVisitor<'vir, '_, E> {
    type EncodeOperandArgs = ();
    type Curr = !;
    type Next = !;
    type LocalDeclsSrc = mir::LocalDecls<'vir>;
    fn vcx(&self) -> &'vir vir::VirCtxt<'vir> {
        self.vcx
    }

    fn deps(&mut self) -> &mut TaskEncoderDependencies<'vir, E> {
        self.deps
    }

    fn local_decls_src(&self) -> &Self::LocalDeclsSrc {
        self.local_decls
    }

    fn encode_operand(
        &mut self,
        _args: &Self::EncodeOperandArgs,
        operand: &mir::Operand<'vir>,
    ) -> vir::ExprGenSnap<'vir, Self::Curr, Self::Next> {
        self.encode_operand_snap(operand)
    }

    fn monomorphize(&self) -> bool {
        self.monomorphize
    }
}

pub(crate) struct EncodePlaceResult<'vir> {
    pub(crate) expr: vir::ExprSnap<'vir>,
    pub(crate) ty: mir::tcx::PlaceTy<'vir>,
}

macro_rules! comment {
    ($self:tt, $($arg:tt)*) => { $self.comment(
        vir::vir_format!($self.vcx, $($arg)*),
    ) };
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

    /// Do the same as [self.pcs_succ] but instead of adding the statements to [self.current_stmts] return them instead.
    /// TODO: clean this up
    fn collect_pcs_succ<'a>(
        &mut self,
        state: &Pcg<'vir>,
        pcs: &'a PcgSuccessor<'vir>,
    ) -> Vec<vir::Stmt<'vir>> {
        let current_stmts = self.current_stmts.take();
        self.current_stmts = Some(Vec::new());
        self.pcs_succ(state, pcs);
        let new_stmts = self.current_stmts.take().unwrap();
        self.current_stmts = current_stmts;
        new_stmts
    }

    pub(crate) fn block(&mut self, f: impl FnOnce(&mut Self)) -> Vec<vir::Stmt<'vir>> {
        let current_stmts = self.current_stmts.take();
        self.current_stmts = Some(Vec::new());
        f(self);
        let new_stmts = self.current_stmts.take().unwrap();
        self.current_stmts = current_stmts;
        new_stmts
    }

    pub(crate) fn pcs_borrow_expansion(
        &mut self,
        expansion: BorrowPcgExpansion<'vir>,
        unpack: bool,
        label: Option<&'vir str>,
    ) {
        let base = expansion.base();
        let PCGNode::Place(base) = base else {
            // Ignore expansions of region projections
            return;
        };
        let (place, old) = match base {
            MaybeOldPlace::Current { place } => (place, None),
            MaybeOldPlace::OldPlace(snap) => {
                // We shouldn't be unpacking old places?
                debug_assert!(!unpack);
                (
                    snap.place(),
                    Some(Self::get_location_label(self.vcx, snap.at())),
                )
            }
        };
        let mut place_enc = self.encode_place(place);
        if let Some(label) = old {
            place_enc.expr = self.vcx.mk_old(place_enc.expr, label);
        } else if let Some(label) = label {
            place_enc.expr = self.vcx.mk_local_labelled_old_expr(place_enc.expr, label);
        }
        if unpack {
            self.expand(
                place,
                None,
                &expansion
                    .expansion()
                    .iter()
                    .map(|maybe| maybe.place())
                    .collect::<Vec<_>>(),
            );
        } else {
            self.collapse(
                place,
                None,
                &expansion
                    .expansion()
                    .iter()
                    .map(|maybe| maybe.place())
                    .collect::<Vec<_>>(),
            );
        }
    }

    fn pcs_handle_edge(
        &mut self,
        borrows_state: &BorrowsState<'vir>,
        edge: &BorrowPcgEdge<'vir>,
        add: bool,
        label: Option<&'vir str>,
        edge_to_loop: bool,
        to_skip: &mut Vec<mir::BasicBlock>,
    ) {
        let conditions = edge.conditions();
        let cond = conditions
            .all_branch_choices()
            .map(|choices| {
                let successors = choices.successors(self.body);
                let tos = &self.from_to_vars[&choices.from()];
                let candidates = tos.iter().filter(|(to, _)| successors.contains(to));
                let disj = candidates
                    .map(|(_, var)| self.vcx.mk_local_ex(var, &vir::TYPE_BOOL))
                    .collect::<Vec<_>>();
                self.vcx.mk_disj(self.vcx.alloc_slice(&disj))
            })
            .collect::<Vec<_>>();
        let cond = self.vcx.mk_conj(self.vcx.alloc_slice(&cond));
        let stmts = self.block(|self_| {
            self_.pcs_handle_edge_conditionless(
                borrows_state,
                edge,
                add,
                label,
                edge_to_loop,
                to_skip,
            )
        });
        if stmts
            .iter()
            .all(|stmt| matches!(stmt.kind, vir::StmtKindData::Comment(_)))
        {
            self.stmts(stmts);
            return;
        }
        let stmts = self.vcx.alloc_slice(&stmts);
        self.stmt(self.vcx.mk_if_stmt(cond, stmts, &[]));
    }

    fn pcs_handle_edge_conditionless(
        &mut self,
        borrows_state: &BorrowsState<'vir>,
        edge: &BorrowPcgEdge<'vir>,
        add: bool,
        label: Option<&'vir str>,
        edge_to_loop: bool,
        to_skip: &mut Vec<mir::BasicBlock>,
    ) {
        match edge.kind() {
            BorrowPcgEdgeKind::BorrowPcgExpansion(expansion) => {
                self.pcs_borrow_expansion(expansion.clone(), add, label);
            }
            BorrowPcgEdgeKind::Abstraction(AbstractionType::FunctionCall(call)) => {
                if add {
                    // The wand will be introduced by the method call itself.
                    return;
                }
                // We may be encoding multiple edges as a single wand, skip
                // further edge removals. This is a hack to get around the fact
                // that Viper doesn't support hyperwands.
                if to_skip.contains(&call.location().block) {
                    return;
                }
                to_skip.push(call.location().block);
                // TODO: this applies *all* the wands for the referenced
                //   function call; instead we should figure out which
                //   wand it is based on the edge info.
                let wands = self
                    .deps
                    .require_local::<PurifiedWandEnc>(PurifiedWandEncTask {
                        def_id: call.def_id().unwrap(),
                    })
                    .unwrap();
                let bb = &self.body[call.location().block];
                let terminator = bb.terminator.as_ref().unwrap();
                match &terminator.kind {
                    mir::TerminatorKind::Call {
                        args, destination, ..
                    } => {
                        let (_, dest_snap, _, _) = self.encode_place_snap((*destination).into());
                        let wand_args =
                            std::iter::once(dest_snap)
                                .chain(args.iter().map(|operand| {
                                    self.encode_operand_snap_immediate(&operand.node)
                                }))
                                .collect::<Vec<_>>();
                        let (label_pre, label_post) = self.call_labels[&call.location().block];
                        wands.apply_wands(&wand_args, label_pre, label_post, self);
                    }
                    _ => unreachable!(),
                }
            }
            BorrowPcgEdgeKind::Abstraction(at @ AbstractionType::Loop(_)) => {
                self.pcs_handle_wand(borrows_state, add, at, label, edge_to_loop);
            }
            BorrowPcgEdgeKind::Borrow(BorrowEdge::Remote(remote_borrow))
                if remote_borrow.is_mut(self.pcg_ctxt()) =>
            {
                if add {
                    return;
                }

                let deref_place = remote_borrow.deref_place(self.pcg_ctxt()).place();
                let deref_ty = deref_place.ty(self.pcg_ctxt()).ty;
                let deref_enc = self.encode_place(deref_place);

                let caster = self
                    .deps
                    .require_local::<RustTyCastersEnc<CastTypePure>>(deref_ty)
                    .unwrap();

                let remote_place = remote_borrow.blocked_place();
                let remote_local_data =
                    if let Some(local_data) = self.remote_place_to_local_data.get(&remote_place) {
                        *local_data
                    } else {
                        let remote_name = vir::vir_format_identifier!(
                            self.vcx,
                            "_{}s_remote",
                            remote_place.assigned_local().as_usize()
                        )
                        .to_str();
                        let local = self.vcx.mk_local(remote_name, deref_enc.expr.ty());

                        self.declared_remotes
                            .insert((remote_name, deref_enc.expr.ty()));
                        self.remote_place_to_local_data.insert(remote_place, local);

                        local
                    };

                let lhs = self.vcx.mk_local_ex_local(remote_local_data);
                let (rhs_place, _rhs) = (deref_place, deref_enc.expr);
                let rhs = if let Some(&rhs) = self.place_to_local_data.get(&rhs_place) {
                    self.vcx.mk_local_ex_local(rhs)
                } else {
                    caster.cast_to_concrete_if_possible(self.vcx, self.encode_place(rhs_place).expr)
                };

                self.stmt(self.vcx.mk_pure_assign_stmt(lhs, rhs));

                let assigned_local = remote_place.assigned_local();
                let cons = self.local_defs.locals[assigned_local]
                    .ty
                    .expect_purified_mutref()
                    .snap_data
                    .prim_to_snap;
                self.return_to_remote.insert(
                    assigned_local,
                    (cons.gen()(caster.cast_to_generic_if_necessary(self.vcx, lhs))).upcast_ty(),
                );
            }
            BorrowPcgEdgeKind::Borrow(BorrowEdge::Local(local_borrow)) => {
                if add {
                    return;
                }

                let blocked_place = local_borrow.blocked_place.place();
                let deref_place = local_borrow.deref_place(self.pcg_ctxt()).place();
                let deref_ty = deref_place.ty(self.pcg_ctxt()).ty;

                let caster = self
                    .deps
                    .require_local::<RustTyCastersEnc<CastTypePure>>(deref_ty)
                    .unwrap();

                let lhs = self.encode_place(blocked_place).expr;
                let (rhs_place, _rhs) = (deref_place, self.encode_place(deref_place).expr);
                let rhs = if let Some(&rhs) = self.place_to_local_data.get(&rhs_place) {
                    self.vcx.mk_local_ex_local(rhs)
                } else {
                    caster.cast_to_concrete_if_possible(self.vcx, self.encode_place(rhs_place).expr)
                };

                self.stmt(self.vcx.mk_pure_assign_stmt(lhs, rhs));
            }
            unsupported_op => comment!(self, "(ignoring {unsupported_op:?})"),
        }
    }

    pub(crate) fn pcs_unblock_actions(
        &mut self,
        borrows_state: &BorrowsState<'vir>,
        actions: &[BorrowPcgUnblockAction<'vir>],
        label: Option<&'vir str>,
    ) {
        let mut to_skip = Vec::new();
        for action in actions {
            self.pcs_handle_edge(
                borrows_state,
                action.edge(),
                false,
                label,
                false,
                &mut to_skip,
            );
        }
    }

    fn pcg_actions(&mut self, pcg: &Pcg<'vir>, actions: &PcgActions<'vir>, edge_to_loop: bool) {
        for action in actions.iter() {
            match action {
                PcgAction::Borrow(action) => self.borrow_action(pcg, action, edge_to_loop),
                PcgAction::Owned(action) => self.pcg_repack(action.kind()),
            }
        }
    }

    fn borrow_action(
        &mut self,
        pcg: &Pcg<'vir>,
        action: &BorrowPcgAction<'vir>,
        edge_to_loop: bool,
    ) {
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
                false,
                None,
                edge_to_loop,
                &mut to_skip,
            ),
            BorrowPcgActionKind::AddEdge { edge } => self.pcs_handle_edge(
                pcg.borrow_pcg(),
                edge,
                true,
                None,
                edge_to_loop,
                &mut to_skip,
            ),
            //RenamePlace {
            //    old: MaybeOldPlace<'tcx>,
            //    new: MaybeOldPlace<'tcx>,
            //},
            kind => comment!(self, "(ignoring {kind:?})"),
        }
    }

    fn pcg_repack(&mut self, repack_op: &RepackOp<'vir>) {
        match repack_op {
            RepackOp::Expand(expand) => {
                self.expand(
                    expand.from(),
                    expand.guide(),
                    &expand.target_places(self.pcg_ctxt()),
                );
            }
            RepackOp::Collapse(collapse) => {
                self.collapse(
                    collapse.to(),
                    collapse.guide(),
                    &collapse.expansion_places(self.pcg_ctxt()),
                );
            }
            ignored_op @ (RepackOp::RegainLoanedCapability(..)
            | RepackOp::Weaken(_, CapabilityKind::Exclusive, CapabilityKind::Read)
            | RepackOp::Weaken(_, CapabilityKind::Exclusive, CapabilityKind::Write)) => {
                self.stmt(self.vcx.mk_comment_stmt(vir::vir_format!(
                    self.vcx,
                    "ignored repack op: {ignored_op:?}"
                )));
            }
            unsupported_op => {
                self.stmt(self.vcx.mk_comment_stmt(vir::vir_format!(
                    self.vcx,
                    "unsupported repack op: {unsupported_op:?}"
                )));
                self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
            }
        }
    }

    fn extract_inner_tys(
        &mut self,
        ty: ty::Ty<'vir>,
        variant_index: Option<abi::VariantIdx>,
    ) -> Vec<ty::Ty<'vir>> {
        match ty.kind() {
            ty::TyKind::Adt(adt_def, args) if adt_def.is_box() => {
                vec![ty.expect_boxed_ty(), args.type_at(1)]
            }
            ty::TyKind::Adt(adt_def, args) if adt_def.is_enum() => adt_def
                .variant(variant_index.unwrap())
                .fields
                .iter()
                .map(|f| f.ty(self.vcx.tcx(), args))
                .collect::<Vec<_>>(),
            ty::TyKind::Adt(adt_def, args) => adt_def
                .all_fields()
                .map(|f| f.ty(self.vcx.tcx(), args))
                .collect::<Vec<_>>(),
            ty::TyKind::Tuple(tys) => tys.iter().collect::<Vec<_>>(),
            ty::TyKind::Array(ty, ..)
            | ty::TyKind::Pat(ty, ..)
            | ty::TyKind::Slice(ty)
            | ty::TyKind::RawPtr(ty, ..)
            | ty::TyKind::Ref(_, ty, ..) => vec![*ty],
            _ => unreachable!(),
        }
    }

    fn expand(
        &mut self,
        place: Place<'vir>,
        guide: Option<pcg::free_pcs::RepackGuide>,
        target_places: &[Place<'vir>],
    ) {
        let place_local_data = self.place_to_local_data.get(&place).map_or_else(
            || self.local_defs.locals[place.local].local,
            |local_data| *local_data,
        );

        let place_ty = place.ty(self.pcg_ctxt()).ty;
        let place_vid = place.ty(self.pcg_ctxt()).variant_index;
        let place_ty_out = self
            .deps
            .require_ref::<RustTyPredicatesEnc>(place_ty)
            .unwrap();

        let (most_generic_ty, _) =
            encoders::most_generic_ty::extract_type_params(self.vcx.tcx(), place_ty);
        let place_enc = self.encode_place(place);
        let casts = self.place_casts(&place_enc);

        match place_ty_out.generic_predicate.specifics {
            encoders::predicate::PredicateEncData::StructLike(predicate_enc_data_struct) => {
                let most_generic_inner_tys =
                    self.extract_inner_tys(most_generic_ty.ty(), place_vid);
                for (idx, field_fn) in predicate_enc_data_struct
                    .snap_data
                    .field_access
                    .iter()
                    .enumerate()
                {
                    let field_name = vir::vir_format_identifier!(
                        self.vcx,
                        "{}_field_{}",
                        place_local_data.name,
                        idx
                    )
                    .to_str();
                    let field_place = target_places[idx];
                    let read_fn = field_fn.read;
                    let field_ty = field_place.ty(self.pcg_ctxt()).ty;
                    let most_generic_ty = most_generic_inner_tys[idx];
                    let rhs = if let TyKind::Param(p) = most_generic_ty.kind()
                        && !field_ty.is_param(p.index)
                    {
                        &casts[idx].cast_to_concrete_if_possible(
                            self.vcx,
                            (read_fn)(self.vcx.mk_local_ex_local(place_local_data.downcast_ty())),
                        )
                    } else {
                        (read_fn)(self.vcx.mk_local_ex_local(place_local_data.downcast_ty()))
                    };
                    self.declared_vars.insert((field_name, rhs.ty()));
                    let field_local_data = self.vcx.mk_local(field_name, rhs.ty());
                    self.place_to_local_data
                        .insert(field_place.into(), &field_local_data);
                    self.stmt(
                        self.vcx
                            .mk_pure_assign_stmt(self.vcx.mk_local_ex_local(field_local_data), rhs),
                    );
                }
            }
            encoders::predicate::PredicateEncData::EnumLike(Some(predicate_enc_data_enum)) => {
                match guide {
                    Some(RepackGuide::Downcast(sym, vid)) => {
                        let variant_name = vir::vir_format_identifier!(
                            self.vcx,
                            "{}_as_{}",
                            place_local_data.name,
                            sym.map_or(
                                String::from("variant_") + &vid.index().to_string(),
                                |sym| { sym.to_string() }
                            )
                        )
                        .to_str();

                        self.declared_vars
                            .insert((variant_name, place_local_data.ty));
                        let variant_local_data =
                            self.vcx.mk_local(variant_name, place_local_data.ty);
                        self.place_to_local_data
                            .insert(target_places[0], &variant_local_data);
                        self.stmt(self.vcx.mk_pure_assign_stmt(
                            self.vcx.mk_local_ex_local(variant_local_data),
                            self.vcx.mk_local_ex_local(place_local_data),
                        ));
                    }
                    None if place_vid.is_some() => {
                        let most_generic_inner_tys =
                            self.extract_inner_tys(most_generic_ty.ty(), place_vid);
                        for (idx, field_fn) in predicate_enc_data_enum.variants
                            [place_vid.unwrap().index()]
                        .fields
                        .snap_data
                        .field_access
                        .iter()
                        .enumerate()
                        {
                            let field_name = vir::vir_format_identifier!(
                                self.vcx,
                                "{}_field_{}",
                                place_local_data.name,
                                idx
                            )
                            .to_str();
                            let field_place = target_places[idx];
                            let read_fn = field_fn.read;
                            let field_ty = field_place.ty(self.pcg_ctxt()).ty;
                            let most_generic_ty = most_generic_inner_tys[idx];
                            let rhs = if let TyKind::Param(p) = most_generic_ty.kind()
                                && !field_ty.is_param(p.index)
                            {
                                &casts[idx].cast_to_concrete_if_possible(
                                    self.vcx,
                                    (read_fn)(
                                        self.vcx.mk_local_ex_local(place_local_data.downcast_ty()),
                                    ),
                                )
                            } else {
                                (read_fn)(
                                    self.vcx.mk_local_ex_local(place_local_data.downcast_ty()),
                                )
                            };
                            self.declared_vars.insert((field_name, rhs.ty()));
                            let field_local_data = self.vcx.mk_local(field_name, rhs.ty());
                            self.place_to_local_data
                                .insert(field_place.into(), &field_local_data);
                            self.stmt(self.vcx.mk_pure_assign_stmt(
                                self.vcx.mk_local_ex_local(field_local_data),
                                rhs,
                            ));
                        }
                    }
                    _ => return,
                }
            }
            encoders::predicate::PredicateEncData::PurifiedImmRef(
                predicate_enc_data_purified_imm_ref,
            ) => {
                let most_generic_inner_tys = self.extract_inner_tys(most_generic_ty.ty(), None);
                let value_name =
                    vir::vir_format_identifier!(self.vcx, "{}_value", place_local_data.name)
                        .to_str();
                let value_place = target_places[0].place();
                let value_fn = predicate_enc_data_purified_imm_ref.snap_data.value_access;
                let value_ty = value_place.ty(self.pcg_ctxt()).ty;
                let most_generic_ty = most_generic_inner_tys[0];
                let rhs = if let TyKind::Param(p) = most_generic_ty.kind()
                    && !value_ty.is_param(p.index)
                {
                    let snap = value_fn(self.vcx.mk_local_ex_local(place_local_data.downcast_ty()))
                        .upcast_ty();
                    casts[0].cast_to_concrete_if_possible(self.vcx, snap)
                } else {
                    value_fn(self.vcx.mk_local_ex_local(place_local_data.downcast_ty())).upcast_ty()
                };
                self.declared_vars.insert((value_name, rhs.ty()));
                let value_local_data = self.vcx.mk_local(value_name, rhs.ty());
                self.place_to_local_data
                    .insert(value_place.into(), &value_local_data);
                self.stmt(
                    self.vcx
                        .mk_pure_assign_stmt(self.vcx.mk_local_ex_local(value_local_data), rhs),
                );
            }
            encoders::predicate::PredicateEncData::PurifiedMutRef(
                predicate_enc_data_purified_mut_ref,
            ) => {
                let most_generic_inner_tys = self.extract_inner_tys(most_generic_ty.ty(), None);
                let value_name =
                    vir::vir_format_identifier!(self.vcx, "{}_value", place_local_data.name)
                        .to_str();
                let value_place = target_places[0].place();
                let value_fn = predicate_enc_data_purified_mut_ref.snap_data.value_access;
                let value_ty = value_place.ty(self.pcg_ctxt()).ty;
                let most_generic_ty = most_generic_inner_tys[0];
                let rhs = if let TyKind::Param(p) = most_generic_ty.kind()
                    && !value_ty.is_param(p.index)
                {
                    let snap = self.vcx.mk_local_ex_local(place_local_data.downcast_ty());
                    let snap = value_fn(snap).upcast_ty();
                    casts[0].cast_to_concrete_if_possible(self.vcx, snap)
                } else {
                    value_fn(self.vcx.mk_local_ex_local(place_local_data.downcast_ty())).upcast_ty()
                };
                self.declared_vars.insert((value_name, rhs.ty()));
                let value_local_data = self.vcx.mk_local(value_name, rhs.ty());
                self.place_to_local_data
                    .insert(value_place.into(), &value_local_data);
                self.stmt(
                    self.vcx
                        .mk_pure_assign_stmt(self.vcx.mk_local_ex_local(value_local_data), rhs),
                );
            }
            encoders::predicate::PredicateEncData::ImmRef(..)
            | encoders::predicate::PredicateEncData::MutRef(..)
            | encoders::predicate::PredicateEncData::Param
            | encoders::predicate::PredicateEncData::Never
            | encoders::predicate::PredicateEncData::Primitive(..)
            | encoders::predicate::PredicateEncData::EnumLike(None)
            | encoders::predicate::PredicateEncData::Trusted => return,
        }
    }

    fn collapse(
        &mut self,
        place: Place<'vir>,
        guide: Option<RepackGuide>,
        target_places: &[Place<'vir>],
    ) {
        let place_local_data = self.place_to_local_data.get(&place).map_or_else(
            || self.local_defs.locals[place.local].local,
            |local_data| *local_data,
        );

        let place_vid = place.ty(self.pcg_ctxt()).variant_index;
        let place_ty = place.ty(self.pcg_ctxt()).ty;
        let place_ty_out = self
            .deps
            .require_ref::<RustTyPredicatesEnc>(place_ty)
            .unwrap();

        let (most_generic_ty, substs) =
            encoders::most_generic_ty::extract_type_params(self.vcx.tcx(), place_ty);
        let place_enc = self.encode_place(place);
        let casts = self.place_casts(&place_enc);

        match place_ty_out.generic_predicate.specifics {
            encoders::predicate::PredicateEncData::StructLike(predicate_enc_data_struct) => {
                let most_generic_inner_tys = self.extract_inner_tys(most_generic_ty.ty(), None);
                let snap_cons = predicate_enc_data_struct.snap_data.field_snaps_to_snap;
                let mut field_exprs = Vec::new();
                for idx in 0..target_places.len() {
                    let field_place = target_places[idx];
                    let field_expr = self
                        .vcx
                        .mk_local_ex_local(self.place_to_local_data.get(&field_place).unwrap());
                    if let TyKind::Param(p) = most_generic_inner_tys[idx].kind()
                        && !field_place.ty(self.pcg_ctxt()).ty.is_param(p.index)
                    {
                        field_exprs.push(
                            *&casts[idx]
                                .cast_to_generic_if_necessary(self.vcx, field_expr)
                                .upcast_ty(),
                        );
                    } else {
                        field_exprs.push(field_expr);
                    }
                }

                // this isn't a great way to check, but
                // ensures only non-box, non-tuple ADTs get typarams
                let type_exprs = if snap_cons.arity().0.is_empty() {
                    vec![]
                } else {
                    substs
                        .into_iter()
                        .map(|typ| {
                            extract_type_expr(
                                self.vcx,
                                self.deps,
                                typ,
                                extract_type_params(self.vcx.tcx(), typ).0.ty(),
                            )
                        })
                        .collect::<Vec<_>>()
                };

                let stmt = self.vcx.mk_pure_assign_stmt(
                    self.vcx.mk_local_ex_local(place_local_data),
                    (snap_cons)(type_exprs.as_slice(), field_exprs.as_slice()).upcast_ty(),
                );
                self.stmt(stmt);
            }
            encoders::predicate::PredicateEncData::EnumLike(Some(predicate_enc_data_enum)) => {
                match guide {
                    Some(RepackGuide::Downcast(..)) => {
                        let variant_local_data =
                            self.place_to_local_data.get(&target_places[0]).unwrap();
                        self.stmt(self.vcx.mk_pure_assign_stmt(
                            self.vcx.mk_local_ex_local(place_local_data),
                            self.vcx.mk_local_ex_local(variant_local_data),
                        ));
                    }
                    None if place_vid.is_some() => {
                        let most_generic_inner_tys =
                            self.extract_inner_tys(most_generic_ty.ty(), place_vid);
                        let snap_cons = predicate_enc_data_enum.variants
                            [place_vid.unwrap().index()]
                        .fields
                        .snap_data
                        .field_snaps_to_snap;
                        let mut field_exprs = Vec::new();
                        for idx in 0..target_places.len() {
                            let field_place = target_places[idx];
                            let field_expr = self.vcx.mk_local_ex_local(
                                self.place_to_local_data.get(&field_place).unwrap(),
                            );
                            if let TyKind::Param(p) = most_generic_inner_tys[idx].kind()
                                && !field_place.ty(self.pcg_ctxt()).ty.is_param(p.index)
                            {
                                field_exprs.push(
                                    *&casts[idx]
                                        .cast_to_generic_if_necessary(self.vcx, field_expr)
                                        .upcast_ty(),
                                );
                            } else {
                                field_exprs.push(field_expr);
                            }
                        }
                        let type_exprs = substs
                            .into_iter()
                            .map(|typ| {
                                extract_type_expr(
                                    self.vcx,
                                    self.deps,
                                    typ,
                                    extract_type_params(self.vcx.tcx(), typ).0.ty(),
                                )
                            })
                            .collect::<Vec<_>>();
                        let stmt = self.vcx.mk_pure_assign_stmt(
                            self.vcx.mk_local_ex_local(place_local_data),
                            (snap_cons)(&type_exprs.as_slice(), &field_exprs.as_slice())
                                .upcast_ty(),
                        );
                        self.stmt(stmt);
                    }
                    _ => return,
                }
            }
            encoders::predicate::PredicateEncData::PurifiedImmRef(
                predicate_enc_data_purified_imm_ref,
            ) => {
                let most_generic_inner_tys = self.extract_inner_tys(most_generic_ty.ty(), None);
                let snap_cons = predicate_enc_data_purified_imm_ref.snap_data.prim_to_snap;
                let value_place = target_places[0].place();
                let value_expr = self
                    .vcx
                    .mk_local_ex_local(self.place_to_local_data.get(&value_place).unwrap());
                let value_expr = if let TyKind::Param(p) = most_generic_inner_tys[0].kind()
                    && !value_place.ty(self.pcg_ctxt()).ty.is_param(p.index)
                {
                    casts[0].cast_to_generic_if_necessary(self.vcx, value_expr)
                } else {
                    value_expr.downcast_ty()
                };
                let stmt = self.vcx.mk_pure_assign_stmt(
                    self.vcx.mk_local_ex_local(place_local_data),
                    (snap_cons)(value_expr).upcast_ty(),
                );
                self.stmt(stmt);
            }
            encoders::predicate::PredicateEncData::PurifiedMutRef(
                predicate_enc_data_purified_mut_ref,
            ) => {
                let most_generic_inner_tys = self.extract_inner_tys(most_generic_ty.ty(), None);
                let snap_cons = predicate_enc_data_purified_mut_ref.snap_data.prim_to_snap;
                let value_place = target_places[0].place();
                let value_expr = self
                    .vcx
                    .mk_local_ex_local(self.place_to_local_data.get(&value_place).unwrap());
                let value_expr = if let TyKind::Param(p) = most_generic_inner_tys[0].kind()
                    && !value_place.ty(self.pcg_ctxt()).ty.is_param(p.index)
                {
                    casts[0].cast_to_generic_if_necessary(self.vcx, value_expr)
                } else {
                    value_expr.downcast_ty()
                };
                let stmt = self.vcx.mk_pure_assign_stmt(
                    self.vcx.mk_local_ex_local(place_local_data),
                    (snap_cons)(value_expr).upcast_ty(),
                );
                self.stmt(stmt);
            }
            encoders::predicate::PredicateEncData::ImmRef(..)
            | encoders::predicate::PredicateEncData::MutRef(..)
            | encoders::predicate::PredicateEncData::Param
            | encoders::predicate::PredicateEncData::Never
            | encoders::predicate::PredicateEncData::Primitive(..)
            | encoders::predicate::PredicateEncData::EnumLike(None)
            | encoders::predicate::PredicateEncData::Trusted => {}
        }
    }

    fn pcs_succ<'a>(&mut self, pcg_state: &Pcg<'vir>, succ: &'a PcgSuccessor<'vir>) {
        let edge_to_loop = self.loop_analysis.loop_head_of(succ.block()).is_some();
        self.pcg_actions(pcg_state, succ.actions(), edge_to_loop);
    }

    fn encode_operand_snap(&mut self, operand: &mir::Operand<'vir>) -> vir::ExprSnap<'vir> {
        match operand {
            &mir::Operand::Move(source) => {
                let (result, snap_val, _, ty_out) = self.encode_place_snap(Place::from(source));

                let tmp_exp = self.new_tmp(ty_out.snapshot()).1;
                self.stmt(self.vcx.mk_pure_assign_stmt(tmp_exp, snap_val));
                tmp_exp
            }
            &mir::Operand::Copy(place) => {
                let place_expr =
                    if let Some(local_data) = self.place_to_local_data.get(&place.into()) {
                        return self.vcx.mk_local_ex_local(local_data);
                    } else {
                        self.local_defs.locals[place.local].local_ex
                    };

                let mut place_ty = mir::tcx::PlaceTy::from_ty(self.local_decls[place.local].ty);
                let mut encoded_place = mir::Place::from(place.local);

                let mut crossed_ref =
                    matches!(place_ty.ty.kind(), TyKind::Ref(_, _, ty::Mutability::Not));
                let mut result = place_expr.as_dyn();
                for elem in place.projection {
                    if crossed_ref {
                        use vir::Reify;
                        let (expr, _) = crate::encoders::mir_pure::encode_place_element(
                            self.vcx,
                            self.deps,
                            place_ty,
                            elem,
                            result.lift().downcast_ty(),
                            None,
                        );
                        result = expr.reify(self.vcx, (self.def_id, &[])).as_dyn();
                    } else {
                        let maybe_local = self.place_to_local_data.get(&encoded_place.into());
                        result = if let Some(local) = maybe_local {
                            self.vcx.mk_local_ex_local(local)
                        } else {
                            self.encode_place_element(place_ty, elem, result.downcast_ty())
                        }
                        .as_dyn();
                    }
                    place_ty = place_ty.projection_ty(self.vcx.tcx(), elem);
                    encoded_place = encoded_place.project_deeper(&[elem], self.vcx.tcx());
                    if !crossed_ref
                        && matches!(place_ty.ty.kind(), TyKind::Ref(_, _, ty::Mutability::Not))
                    {
                        let ty_out = self
                            .deps
                            .require_ref::<RustTyPredicatesEnc>(place_ty.ty)
                            .unwrap();
                        result = (ty_out
                            .generic_predicate
                            .expect_purified_immref()
                            .snap_data
                            .prim_to_snap)(result.downcast_ty())
                        .as_dyn();
                        crossed_ref = true;
                    }
                }
                result.downcast_ty()
            }
            mir::Operand::Constant(box constant) => self.encode_constant(constant).upcast_ty(),
        }
    }

    fn encode_operand(&mut self, operand: &mir::Operand<'vir>) -> vir::ExprSnap<'vir> {
        let ty = operand.ty(self.local_decls, self.vcx.tcx());
        let (encode_place_result, ty_out) = match operand {
            &mir::Operand::Move(source) => return self.encode_place(Place::from(source)).expr,
            &mir::Operand::Copy(_source) => {
                let ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(ty).unwrap();
                (self.encode_operand_snap(operand), ty_out)
            }
            mir::Operand::Constant(box constant) => {
                let ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(ty).unwrap();
                let constant = self.encode_constant(constant);
                (constant.upcast_ty(), ty_out)
            }
        };
        let tmp = self.new_tmp(&ty_out.generic_predicate.snapshot);
        let stmt = self.vcx.mk_pure_assign_stmt(tmp.1, encode_place_result);
        self.stmt(stmt);
        tmp.1
    }

    /// Encodes the snapshot of an operand. This should not be used for encoding
    /// regular mir statements/terminators as it doesn't match the semantics.
    fn encode_operand_snap_immediate(
        &mut self,
        operand: &mir::Operand<'vir>,
    ) -> vir::ExprSnap<'vir> {
        match operand {
            &mir::Operand::Move(source) => self.encode_place_snap(Place::from(source)).1,
            &mir::Operand::Copy(source) => self.encode_place_snap(Place::from(source)).1,
            mir::Operand::Constant(box constant) => self.encode_constant(constant).upcast_ty(),
        }
    }

    fn encode_constant(&mut self, constant: &mir::ConstOperand<'vir>) -> vir::ExprCSnap<'vir> {
        self.deps
            .require_local::<ConstEnc>((constant.const_, 0, self.def_id))
            .unwrap()
    }

    pub(crate) fn encode_place(&mut self, place: Place<'vir>) -> EncodePlaceResult<'vir> {
        if let Some(local) = self.place_to_local_data.get(&place) {
            return EncodePlaceResult {
                expr: self.vcx.mk_local_ex_local(local),
                ty: place.ty(self.pcg_ctxt()),
            };
        }
        let mut place_ty = mir::tcx::PlaceTy::from_ty(self.local_decls[place.local].ty);
        let mut encoded_place = mir::Place::from(place.local);
        let mut result = self
            .place_to_local_data
            .get(&encoded_place.into())
            .map_or(self.local_defs.locals[place.local].local_ex, |local| {
                self.vcx.mk_local_ex_local(local)
            });
        // TODO: factor this out (duplication with pure encoder)?
        for &elem in place.projection {
            encoded_place = encoded_place.project_deeper(&[elem], self.vcx.tcx());
            result = if let Some(local) = self.place_to_local_data.get(&encoded_place.into()) {
                self.vcx.mk_local_ex_local(local)
            } else {
                self.encode_place_element(place_ty, elem, result.downcast_ty())
            };
            place_ty = place_ty.projection_ty(self.vcx.tcx(), elem);
        }
        EncodePlaceResult {
            expr: result,
            ty: place_ty,
        }
    }

    fn place_casts(
        &mut self,
        place_enc: &EncodePlaceResult<'vir>,
    ) -> Vec<
        RustTyGenericCastEncOutput<
            'vir,
            CastersEncOutputRef<
                vir::FunctionIdn<'vir, (vir::CSnap, vir::ManyTyVal), vir::PSnap>,
                vir::FunctionIdn<'vir, (vir::PSnap, vir::ManyTyVal), vir::CSnap>,
            >,
        >,
    > {
        match place_enc.ty.ty.kind() {
            TyKind::Adt(def, generics) if def.is_box() => {
                let to_concrete = self
                    .deps
                    .require_local::<RustTyCastersEnc<CastTypePure>>(
                        place_enc.ty.ty.expect_boxed_ty(),
                    )
                    .unwrap();
                let to_generic = self
                    .deps
                    .require_local::<RustTyCastersEnc<CastTypePure>>(generics.type_at(1))
                    .unwrap();
                vec![to_concrete, to_generic]
            }
            TyKind::Adt(def, generics) => {
                let variant = match (def.adt_kind(), place_enc.ty.variant_index) {
                    (ty::AdtKind::Enum, Some(idx)) => def.variant(idx),
                    (ty::AdtKind::Enum, None) => return Default::default(),
                    (_, Some(_)) => unreachable!(),
                    _ => def.non_enum_variant(),
                };
                variant
                    .fields
                    .iter()
                    .map(|field| {
                        let field_ty = field.ty(self.vcx.tcx(), &generics);
                        self.deps
                            .require_local::<RustTyCastersEnc<CastTypePure>>(field_ty)
                            .unwrap()
                    })
                    .collect::<Vec<_>>()
            }
            TyKind::Tuple(tys) => tys
                .iter()
                .map(|ty| {
                    self.deps
                        .require_local::<RustTyCastersEnc<CastTypePure>>(ty)
                        .unwrap()
                })
                .collect::<Vec<_>>(),
            TyKind::Ref(_, ty, _) => vec![self
                .deps
                .require_local::<RustTyCastersEnc<CastTypePure>>(*ty)
                .unwrap()],
            _ => vec![],
        }
    }

    pub(crate) fn encode_place_snap(
        &mut self,
        place: Place<'vir>,
    ) -> (
        EncodePlaceResult<'vir>,
        vir::ExprSnap<'vir>,
        mir::tcx::PlaceTy<'vir>,
        RustTyPredicatesEncOutputRef<'vir>,
    ) {
        let ty = (*place).ty(self.local_decls, self.vcx.tcx());
        assert!(ty.variant_index.is_none());

        let ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(ty.ty).unwrap();
        let result = self.encode_place(place);
        let snap = self
            .place_to_local_data
            .get(&place)
            .map_or(result.expr, |local_data| {
                self.vcx.mk_local_ex_local(local_data)
            });
        (result, snap, ty, ty_out)
    }

    fn encode_place_element(
        &mut self,
        place_ty: mir::tcx::PlaceTy<'vir>,
        elem: mir::PlaceElem<'vir>,
        expr: vir::ExprCSnap<'vir>,
    ) -> vir::ExprSnap<'vir> {
        match elem {
            mir::ProjectionElem::Field(field_idx, _) => {
                let e_ty = self
                    .deps
                    .require_ref::<RustTyPredicatesEnc>(place_ty.ty)
                    .unwrap();
                let field_access = e_ty
                    .generic_predicate
                    .expect_variant_opt(place_ty.variant_index)
                    .snap_data
                    .field_access;
                (field_access[field_idx.as_usize()].read)(expr)
            }
            // TODO: should all variants start at the same `Ref`?
            mir::ProjectionElem::Downcast(..) => expr.upcast_ty(),
            mir::ProjectionElem::Deref => {
                assert!(place_ty.variant_index.is_none());
                let e_ty = self
                    .deps
                    .require_ref::<RustTyPredicatesEnc>(place_ty.ty)
                    .unwrap();
                match place_ty.ty.kind() {
                    ty::TyKind::Adt(adt, _) if adt.is_box() => {
                        let field_access = e_ty
                            .generic_predicate
                            .expect_variant_opt(place_ty.variant_index)
                            .snap_data
                            .field_access;
                        (field_access[0].read)(expr)
                    }
                    ty::TyKind::Ref(_, _, ty::Mutability::Not) => {
                        // TODO: unfold? function? use snapshot?
                        let value_access = e_ty
                            .generic_predicate
                            .expect_purified_immref()
                            .snap_data
                            .value_access;
                        (value_access)(expr).upcast_ty()
                    }
                    ty::TyKind::Ref(_, _, ty::Mutability::Mut) => {
                        // TODO: unfold? function? use snapshot?
                        let value_access = e_ty
                            .generic_predicate
                            .expect_purified_mutref()
                            .snap_data
                            .value_access;
                        (value_access)(expr).upcast_ty()
                    }
                    ty_kind => unreachable!("{ty_kind:?}"),
                }
            }
            _ => todo!("Unsupported ProjectionElem {:?}", elem),
        }
    }

    fn new_tmp<T: CompType>(
        &mut self,
        ty: vir::Type<'vir, T>,
    ) -> (vir::Local<'vir, T>, vir::Expr<'vir, T>) {
        let name = vir::vir_format!(self.vcx, "_tmp{}", self.tmp_ctr);
        self.tmp_ctr += 1;
        self.stmt(
            self.vcx
                .mk_local_decl_stmt(vir::vir_local_decl! { self.vcx; [name] : [ty] }, None),
        );
        let tmp = self.vcx.mk_local(name, ty);
        (tmp, self.vcx.mk_local_ex_local(tmp))
    }

    pub(crate) fn new_label(&mut self, base: &str) -> &'vir str {
        let name = vir::vir_format!(self.vcx, "{base}{}", self.label_ctr);
        self.label_ctr += 1;
        self.stmt(self.vcx.mk_label_stmt(name));
        name
    }

    fn new_after_label(&mut self, location: mir::Location) {
        let name = vir::vir_format!(
            self.vcx,
            "_after_{}_{}",
            location.block.index(),
            location.statement_index
        );
        self.stmt(self.vcx.mk_label_stmt(name));
    }

    fn set_from_to_flag(&mut self, from: mir::BasicBlock, to: mir::BasicBlock) -> vir::Stmt<'vir> {
        let name = vir::vir_format!(self.vcx, "_from_bb{}_to_bb{}", from.index(), to.index());
        let tos = self.from_to_vars.entry(from).or_default();
        debug_assert!(!tos.contains(&(to, name)));
        tos.push((to, name));
        let local = self.vcx.mk_local_ex(name, &vir::TYPE_BOOL);
        self.vcx
            .mk_pure_assign_stmt(local, self.vcx.mk_bool::<true>())
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
            .loop_analysis
            .loop_head_of(block)
            .map(|lh| self.get_loop_inv(lh, &cfpcs))
            .unwrap_or_default();

        self.current_fpcs = Some(cfpcs);

        if ENCODE_REACH_BB {
            self.stmt(self.vcx.mk_pure_assign_stmt(
                self.vcx.mk_local_ex(
                    vir::vir_format!(self.vcx, "_reach_bb{}", block.as_usize()),
                    &vir::TYPE_BOOL,
                ),
                self.vcx.mk_bool::<true>(),
            ));
        }

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
        if self.deps.check_cycle().is_err() {
            return;
        }

        comment!(self, "[MIR] {location:?}: {statement:?}");

        let current_fpcs = self.current_fpcs.take().unwrap();
        let cfpcs = &current_fpcs.statements[location.statement_index];
        for phase in EvalStmtPhase::phases() {
            self.pcg_actions(&cfpcs.states[phase], cfpcs.actions(phase), false);
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

        match &statement.kind {
            mir::StatementKind::Assign(box (dest, rvalue)) => {
                // What are we assigning to?
                let proj_enc = self.encode_place(Place::from(*dest)).expr;
                let rvalue_ty = rvalue.ty(self.local_decls, self.vcx.tcx());

                // The snapshot of the value that we are assigning.
                let rval_enc = match rvalue {
                    mir::Rvalue::Use(op) => {
                        self.encode_operand_snap(op)
                    },

                    //mir::Rvalue::Repeat(Operand<'vir>, Const<'vir>) => {}
                    //mir::Rvalue::ThreadLocalRef(DefId) => {}
                    //mir::Rvalue::AddressOf(Mutability, Place<'vir>) => {}
                    //mir::Rvalue::Len(Place<'vir>) => {}
                    //mir::Rvalue::Cast(CastKind, Operand<'vir>, Ty<'vir>) => {}

                    mir::Rvalue::BinaryOp(op, box (l, r)) => {
                        let l_ty = l.ty(self.local_decls, self.vcx.tcx());
                        let r_ty = r.ty(self.local_decls, self.vcx.tcx());
                        use crate::encoders::MirBuiltinEncTask::{BinOp, CheckedBinOp};
                        let task = if op.is_overflowing() {
                            CheckedBinOp(rvalue_ty, *op, l_ty, r_ty)
                        } else {
                            BinOp(rvalue_ty, *op, l_ty, r_ty)
                        };
                        let binop_function = self.deps.require_ref::<MirBuiltinEnc>(
                            task
                        ).unwrap().bin_op().unwrap();
                        binop_function(
                            self.encode_operand_snap(l).downcast_ty(),
                            self.encode_operand_snap(r).downcast_ty(),
                        ).upcast_ty()
                    }

                    //mir::Rvalue::NullaryOp(NullOp, Ty<'vir>) => {}

                    mir::Rvalue::UnaryOp(unop, operand) => {
                        let operand_ty = operand.ty(self.local_decls, self.vcx.tcx());
                        let unop_function = self.deps.require_ref::<MirBuiltinEnc>(
                            crate::encoders::MirBuiltinEncTask::UnOp(
                                rvalue_ty,
                                *unop,
                                operand_ty,
                            ),
                        ).unwrap().un_op().unwrap();
                        unop_function(self.encode_operand_snap(operand).downcast_ty()).upcast_ty()
                    }

                    mir::Rvalue::Aggregate(
                        box kind @ mir::AggregateKind::Adt(..),
                        fields,
                    ) => {
                        let e_rvalue_ty = self.deps.require_ref::<RustTyPredicatesEnc>(rvalue_ty).unwrap();
                        let mir::AggregateKind::Adt(def_id, vidx, generic_args, _, _) = kind else {
                            unreachable!()
                        };
                        let sl = e_rvalue_ty.generic_predicate.get_variant_any(*vidx);
                        let field_tys = fields.iter()
                            .map(|field| field.ty(self.local_decls, self.vcx.tcx()))
                            .collect::<Vec<_>>();
                        let ty_caster = self.deps.require_local::<AggregateSnapArgsCastEnc>(
                            AggregateSnapArgsCastEncTask {
                                tys: field_tys,
                                aggregate_type: kind.into()
                            }
                        ).unwrap();
                        let field_snaps = fields.iter().map(|field| self.encode_operand_snap(field)).collect::<Vec<_>>();
                        let casted_args = ty_caster.apply_casts(self.vcx, field_snaps.into_iter());
                        let type_args = generic_args
                            .types()
                            .map(|typ| {
                                extract_type_expr(self.vcx, self.deps, typ, extract_type_params(self.vcx.tcx(), typ).0.ty())
                            })
                            .collect::<Vec<_>>();
                        (sl.snap_data.field_snaps_to_snap)(&type_args, &casted_args).upcast_ty()
                    },
                    mir::Rvalue::Aggregate(
                        box kind @ mir::AggregateKind::Tuple,
                        fields,
                    ) => {
                        let e_rvalue_ty = self.deps.require_ref::<RustTyPredicatesEnc>(rvalue_ty).unwrap();
                        let sl = match kind {
                            mir::AggregateKind::Adt(_, vidx, _, _, _) =>
                                e_rvalue_ty.generic_predicate.get_variant_any(*vidx),
                            _ => e_rvalue_ty.generic_predicate.expect_structlike()
                        };
                        let field_tys = fields.iter()
                            .map(|field| field.ty(self.local_decls, self.vcx.tcx()))
                            .collect::<Vec<_>>();
                        let ty_caster = self.deps.require_local::<AggregateSnapArgsCastEnc>(
                            AggregateSnapArgsCastEncTask {
                                tys: field_tys,
                                aggregate_type: kind.into()
                            }
                        ).unwrap();
                        let field_snaps = fields.iter().map(|field| self.encode_operand_snap(field)).collect::<Vec<_>>();
                        let casted_args = ty_caster.apply_casts(self.vcx, field_snaps.into_iter());
                        (sl.snap_data.field_snaps_to_snap)(&[], &casted_args).upcast_ty()
                    }
                    mir::Rvalue::Discriminant(place) => {
                        let place_ty = place.ty(self.local_decls, self.vcx.tcx());
                        let ty = self
                            .deps
                            .require_local::<encoders::rust_ty_snapshots::RustTySnapshotsEnc>(place_ty.ty)
                            .unwrap()
                            .generic_snapshot
                            .specifics;
                        let place_expr = self.encode_place(Place::from(*place)).expr;

                        match ty.get_enumlike().filter(|_| place_ty.variant_index.is_none()) {
                            Some(ty) => (ty.unwrap().snap_to_discr_snap)(place_expr.downcast_ty()).upcast_ty(),
                            None => {
                                let e_rvalue_ty = self
                                    .deps
                                    .require_local::<encoders::rust_ty_snapshots::RustTySnapshotsEnc>(rvalue_ty)
                                    .unwrap()
                                    .generic_snapshot
                                    .specifics
                                    .expect_primitive();
                                // mir::Rvalue::Discriminant documents "Returns zero for types without discriminant"
                                let zero = self.vcx.mk_uint::<0>();
                                (e_rvalue_ty.prim_to_snap)(zero.upcast_ty()).upcast_ty()
                            }
                        }
                    }
                    mir::Rvalue::Ref(_reg, _kind, place) => {
                        match rvalue_ty.kind() {
                            TyKind::Ref(_, inner_ty, ty::Mutability::Not) => {
                                let e_rvalue_ty = self.deps.require_ref::<RustTyPredicatesEnc>(rvalue_ty).unwrap();
                                let cast = self
                                    .deps
                                    .require_local::<RustTyCastersEnc<CastTypePure>>(*inner_ty)
                                    .unwrap();
                                let snap = self.encode_operand_snap(&mir::Operand::Copy(*place));
                                let snap = cast.cast_to_generic_if_necessary(self.vcx, snap);
                                let inner = e_rvalue_ty.generic_predicate.expect_purified_immref();
                                (inner.snap_data.prim_to_snap)(snap).upcast_ty()
                            }
                            TyKind::Ref(_, inner_ty, ty::Mutability::Mut) => {
                                let e_rvalue_ty = self.deps.require_ref::<RustTyPredicatesEnc>(rvalue_ty).unwrap();
                                let (_, snap, _, _) = self.encode_place_snap(Place::from(*place));
                                let cast = self
                                    .deps
                                    .require_local::<RustTyCastersEnc<CastTypePure>>(*inner_ty)
                                    .unwrap();

                                // The snapshot of the referenced value should be encoded as a generic `Param`
                                let snap = cast.cast_to_generic_if_necessary(self.vcx, snap);
                                let inner = e_rvalue_ty.generic_predicate.expect_purified_mutref();
                                (inner.snap_data.prim_to_snap)(snap).upcast_ty()
                            }
                            _ => unreachable!(),
                        }
                    }

                    //mir::Rvalue::Discriminant(Place<'vir>) => {}
                    //mir::Rvalue::ShallowInitBox(Operand<'vir>, Ty<'vir>) => {}
                    //mir::Rvalue::CopyForDeref(Place<'vir>) => {}
                    other => {
                        let e_rvalue_ty = self.deps.require_ref::<RustTyPredicatesEnc>(rvalue_ty).unwrap();
                        tracing::error!("unsupported rvalue {other:?}");
                        self.vcx.mk_todo_expr(vir::vir_format!(self.vcx, "rvalue {rvalue:?}"), e_rvalue_ty.snapshot())
                    }
                };

                // TODO: this is to do FPCS repacks after accessing the rvalue
                //let e_rvalue_ty = self.deps.require_ref::<RustTyPredicatesEnc>(rvalue_ty).unwrap();
                //let (rval_var, rval_expr) = self.new_tmp(e_rvalue_ty.snapshot());
                //self.stmt(self.vcx.mk_pure_assign_stmt(rval_expr, expr));

                //self.fpcs_repacks_location(location, |loc| &loc.repacks_middle);

                let dest_ty = dest.ty(self.local_decls, self.vcx.tcx());
                assert!(dest_ty.variant_index.is_none());
                let assign = self.vcx.mk_pure_assign_stmt(proj_enc, rval_enc);
                self.stmt(assign);
            }

            // no-ops ?
            mir::StatementKind::StorageLive(..)
            | mir::StatementKind::StorageDead(..) => {}

            // no-ops
            mir::StatementKind::FakeRead(_)
            | mir::StatementKind::Retag(..)
            | mir::StatementKind::PlaceMention(_)
            | mir::StatementKind::AscribeUserType(..)
            | mir::StatementKind::Coverage(_)
            //| mir::StatementKind::ConstEvalCounter
            | mir::StatementKind::Nop => {}

            k => todo!("statement {k:?}"),
        }
        self.new_after_label(location);
    }

    fn visit_terminator(&mut self, terminator: &mir::Terminator<'vir>, location: mir::Location) {
        if self.deps.check_cycle().is_err() {
            return;
        }

        comment!(self, "[MIR] {location:?}: {:?}", terminator.kind);
        let span = terminator.source_info.span;

        let current_fpcs = self.current_fpcs.take().unwrap();
        let cfpcs = &current_fpcs.statements[location.statement_index];
        for phase in EvalStmtPhase::phases() {
            comment!(self, "PCG (T) {phase}");
            self.pcg_actions(&cfpcs.states[phase], cfpcs.actions(phase), false);
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
                let discr_ty = self
                    .deps
                    .require_ref::<RustTyPredicatesEnc>(discr_ty_rs)
                    .unwrap()
                    .generic_predicate
                    .expect_prim();

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

                let discr_ex =
                    (discr_ty.snap_to_prim)(self.encode_operand_snap(discr).downcast_ty());
                self.vcx.mk_goto_if_stmt(
                    discr_ex.as_dyn(), // self.vcx.mk_local_ex(discr_name),
                    goto_targets,
                    goto_otherwise,
                    self.vcx.alloc_slice(&otherwise_stmts),
                )
            }
            mir::TerminatorKind::Return => {
                let current_fpcs = self.current_fpcs.take().unwrap();
                let wands = core::mem::take(&mut self.wands);
                let borrows = current_fpcs.statements.last().unwrap().states
                    [EvalStmtPhase::PostMain]
                    .borrow_pcg();
                let wand_packages = wands.package_wands(borrows, self);
                self.wands = wands;
                self.current_fpcs = Some(current_fpcs);
                self.stmts(wand_packages);

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
                        std::mem::replace(
                            &mut self.current_block_label,
                            Some(self.vcx.alloc(vir::CfgBlockLabelData::BasicBlockTerminator(
                                current_block,
                            ))),
                        )
                        .unwrap(),
                        &[],
                        self.vcx.alloc_slice(
                            &std::mem::replace(&mut self.current_stmts, Some(Vec::new())).unwrap(),
                        ),
                        self.vcx
                            .mk_goto_stmt(self.vcx.alloc(
                                vir::CfgBlockLabelData::BasicBlockTerminator(current_block),
                            )),
                    ),
                );

                let (func_def_id, caller_substs) = self.get_def_id_and_caller_substs(func);
                let is_pure = crate::encoders::with_proc_spec(
                    SpecQuery::GetProcKind(
                        func_def_id,
                        ty::List::identity_for_item(self.vcx().tcx(), func_def_id),
                    ),
                    |spec| spec.kind.is_pure().unwrap_or_default(),
                )
                .unwrap_or_default();

                let dest_local_def = self.local_defs.locals[destination.local];
                let dest = dest_local_def.local_ex;

                let task = (func_def_id, self.def_id);
                let sig = self.vcx().tcx().fn_sig(func_def_id);
                let sig = if self.monomorphize {
                    let typing_env = ty::TypingEnv::post_analysis(self.vcx().tcx(), self.def_id);
                    self.vcx().tcx().instantiate_and_normalize_erasing_regions(
                        caller_substs,
                        typing_env,
                        sig,
                    )
                } else {
                    sig.instantiate_identity()
                };
                let fn_arg_tys = sig
                    .inputs()
                    .iter()
                    .map(|i| i.skip_binder())
                    .copied()
                    .collect::<Vec<_>>();
                if is_pure {
                    let pure_func_app = self.encode_pure_func_app(
                        func_def_id,
                        sig,
                        caller_substs,
                        args,
                        destination,
                        self.def_id,
                        &(),
                    );

                    let assign_stmt = self
                        .vcx
                        .mk_pure_assign_stmt(dest_local_def.local_ex, pure_func_app);

                    self.stmt(assign_stmt);
                } else {
                    let Ok(func_out) = self.deps.require_ref::<encoders::MirPurifiedEnc>(
                        FunctionCallTaskDescription::new(task.0, caller_substs, task.1),
                    ) else {
                        self.current_terminator = Some(
                            self.vcx
                                .mk_dummy_stmt(vir::vir_format!(self.vcx, "recursion",)),
                        );
                        return;
                    };

                    let arg_exprs = args
                        .iter()
                        .map(|arg| self.encode_operand(&arg.node))
                        .collect::<Vec<_>>();

                    let method_args = fn_arg_tys
                        .iter()
                        .zip(args.iter())
                        .zip(arg_exprs.iter())
                        .map(|((fn_arg_ty, arg), arg_ex)| {
                            let local_decls = self.local_decls_src();
                            let arg_ty = arg.node.ty(local_decls, self.vcx().tcx());
                            let caster = self
                                .deps()
                                .require_ref::<CastToEnc<CastTypePure>>(CastArgs {
                                    expected: *fn_arg_ty,
                                    actual: arg_ty,
                                })
                                .unwrap();
                            // In this context, `apply_cast_if_necessary` returns
                            // the impure operation to perform the cast
                            if *fn_arg_ty == arg_ty {
                                arg_ex
                            } else {
                                caster.apply_cast_if_necessary(self.vcx, arg_ex)
                            }
                        })
                        .collect::<Vec<_>>();

                    let mono = self.monomorphize;
                    let ty_args = self
                        .deps()
                        .require_local::<LiftedFuncAppTyParamsEnc>((mono, caller_substs))
                        .unwrap()
                        .iter()
                        .map(|ty| ty.expr(self.vcx()))
                        .collect::<Vec<_>>();

                    let label_pre = self.new_label("pre");

                    let mut tmps = Vec::new();
                    let mut ref_muts = Vec::new();

                    self.vcx().with_span(span, |vcx| {
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

                        for ((fn_arg_ty, arg), method_arg) in
                            fn_arg_tys.iter().zip(args.iter()).zip(method_args.iter())
                        {
                            if let ty::TyKind::Ref(_, _, mir::Mutability::Mut) = fn_arg_ty.kind() {
                                ref_muts.push((method_arg, arg, fn_arg_ty));
                                tmps.push(self.new_tmp(method_arg.ty()));
                            }
                        }

                        let method_out = std::iter::once(dest_local_def.local)
                            .chain(tmps.iter().map(|(local, _)| *local))
                            .collect::<Vec<_>>();

                        self.stmt(self.vcx.alloc(vir::StmtGenData::new(self.vcx.alloc(
                            (func_out.method_ref)(
                                (&method_args, &ty_args),
                                self.vcx.alloc_slice(&method_out.as_dyn()),
                            ),
                        ))));
                    });

                    for ((_, tmp_expr), (arg_expr, arg, fn_arg_ty)) in
                        tmps.iter().zip(ref_muts.iter())
                    {
                        let local_decls = self.local_decls_src();
                        let arg_ty = arg.node.ty(local_decls, self.vcx().tcx());
                        let caster = self
                            .deps()
                            .require_ref::<CastToEnc<CastTypePure>>(CastArgs {
                                expected: arg_ty,
                                actual: **fn_arg_ty,
                            })
                            .unwrap();
                        let tmp_expr = if arg_expr.ty() == tmp_expr.ty() {
                            tmp_expr
                        } else {
                            caster.apply_cast_if_necessary(self.vcx, tmp_expr)
                        };
                        self.stmt(self.vcx.mk_pure_assign_stmt(arg_expr, tmp_expr));
                    }

                    let label_post = self.new_label("post");
                    self.call_labels
                        .insert(location.block, (label_pre, label_post));
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
                        self.vcx().with_span(span, |vcx| {
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
            mir::TerminatorKind::Assert {
                cond,
                expected,
                msg,
                target,
                unwind,
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

                let e_bool = self
                    .deps
                    .require_ref::<RustTyPredicatesEnc>(self.vcx.tcx().types.bool)
                    .unwrap();
                let enc = self.encode_operand_snap(cond).downcast_ty();
                let enc = (e_bool.generic_predicate.expect_prim().snap_to_prim)(enc);
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
                    } // mir::AssertMessage::NullPointerDereference => "",
                };
                self.vcx().with_span(span, |vcx| {
                    vcx.handle_error("exhale.failed:assertion.false", move |_| {
                        Some(vec![PrustiError::verification(error_msg, span.into())])
                    });
                    self.stmt(self.vcx.mk_exhale_stmt(assert));
                });

                let target_bb = self
                    .vcx
                    .alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize()));
                let otherwise = match unwind {
                    mir::UnwindAction::Cleanup(bb) => self
                        .vcx
                        .alloc(vir::CfgBlockLabelData::BasicBlock(bb.as_usize())),
                    _ => todo!(),
                };

                let statements = self.set_from_to_flag(location.block, *target);
                let statements = self.vcx.alloc_slice(&[statements]);

                self.vcx.mk_goto_if_stmt(
                    enc.as_dyn(),
                    self.vcx.alloc_slice(&[self.vcx.mk_goto_if_target(
                        expected.as_dyn(),
                        target_bb,
                        statements,
                    )]),
                    otherwise,
                    &[],
                )
            }
            mir::TerminatorKind::Unreachable => self.vcx().with_span(span, |vcx| {
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

            unsupported_kind => self.vcx.mk_dummy_stmt(vir::vir_format!(
                self.vcx,
                "terminator {unsupported_kind:?}"
            )),
        };
        self.new_after_label(location);
        assert!(self.current_terminator.replace(terminator).is_none());
    }
}
