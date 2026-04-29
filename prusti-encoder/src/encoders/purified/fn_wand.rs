use crate::encoders::{
    MirLocalDefEnc, MirLocalDefEncOutput, MirLocalDefEncTask, Purified, PurifiedEncVisitor,
    TyUsePurifiedEnc,
    mir_fn::RustSignature,
    mir_purified::ProofScript,
    pure::spec::{EncodedPledge, MirSpecEnc},
    ty::{
        RustTyDecomposition,
        generics::{
            GArgCaster, GArgs, GArgsCastEnc, GArgsTy, GArgsTyEnc, GParams, GenericParamsEnc,
        },
    },
};
use pcg::{
    borrow_pcg::{
        FunctionData, FunctionShape, FunctionShapeInput, FunctionShapeNode, FunctionShapeOutput,
        MakeFunctionShapeError, state::BorrowsState, unblock_graph::UnblockGraph,
    },
    utils::Place,
};
use prusti_interface::PrustiError;
use prusti_rustc_interface::{
    data_structures::fx::FxHashSet,
    middle::{mir, ty},
    span::def_id::DefId,
};
use task_encoder::{
    EncodeFullError, EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies,
};
use vir::{CastType, HasType, MethodIdn, macros::ExprQuote};

/// Encodes the magic wands given a function signature.
pub struct PurifiedWandEnc;

#[derive(Clone, Debug)]
pub enum PurifiedWandEncError {
    Unsupported(#[allow(dead_code)] String),
}

impl<'vir, E: TaskEncoder> PurifiedEncVisitor<'vir, '_, E> {
    pub fn prove_wands(
        &mut self,
        final_borrow_state: &BorrowsState<'_, 'vir>,
    ) -> Result<Vec<ProofScript<'vir>>, EncodeFullError<'vir, E>> {
        let mut proof_scripts = Vec::new();
        let label = self.new_label("proof_post");

        let wand_datas = self.wands.viper_wands();

        for wand_data in wand_datas {
            if wand_data.lhs.is_empty() {
                continue;
            }

            for &lhs_node in wand_data.lhs.iter() {
                let local = lhs_node.mir_local();
                let decl = self.local_defs[local].local_snap;
                let pf_name = vir::vir_format!(self.vcx, "_pf{}", decl.name);
                let pf_decl = self.vcx.mk_local_decl(pf_name, decl.ty());
                self.pf_declared_vars.insert(pf_decl);
                self.pf_place_to_local_decl
                    .insert(Place::from(local), pf_decl);
            }

            let proof_bool = self.new_proof_bool();
            let mut pres = Vec::new();
            let mut body = Vec::new();
            let mut posts = Vec::new();

            for &lhs_node in wand_data.lhs.iter() {
                let type_cond = self.wands.encode_type_for_function_shape_node(
                    self.vcx,
                    self.deps,
                    lhs_node,
                    |l| {
                        self.pf_place_to_local_decl
                            .get(&Place::from(l))
                            .map(|d| d.expr(self.vcx))
                            .unwrap_or(self.local_defs[l].local_snap_ex)
                    },
                );
                pres.push(self.vcx.mk_inhale_stmt(type_cond));
            }

            for rhs in wand_data.rhs.iter() {
                let ug = UnblockGraph::for_node(
                    mir::Place::from(rhs.mir_local()),
                    final_borrow_state,
                    self.pcg_ctxt(),
                );
                let actions = ug.actions(self.pcg_ctxt()).unwrap();
                let unblock = self.block(|visitor| {
                    visitor.pcs_unblock_actions(final_borrow_state, &actions, None)
                })?;
                body.extend(unblock);
            }

            let spec = self
                .deps
                .require_dep::<MirSpecEnc<Purified>>((wand_data.def_id, false))?;

            for EncodedPledge {
                expiry_obligation,
                spec,
                span,
            } in spec.pledges.iter().copied()
            {
                self.vcx.with_span(span, |vcx| {
                    vcx.handle_error("exhale.failed:assertion.false", move |_| {
                        Some(vec![PrustiError::verification(
                            "pledge postcondition might not hold",
                            span.into(),
                        )])
                    });

                    expiry_obligation.map(|ob| pres.push(vcx.mk_inhale_stmt(ob.expr)));
                    posts.push(vcx.mk_exhale_stmt(spec));
                });
            }
            let proof_script = pres
                .iter()
                .chain(body.iter())
                .chain(posts.iter())
                .copied()
                .collect::<Vec<_>>();
            proof_scripts.push(ProofScript::new(proof_bool, proof_script));
        }
        Ok(proof_scripts)
    }
}

type EncodedPledges<'vir> = Vec<EncodedPledge<'vir>>;

#[derive(Clone)]
pub struct PurifiedWandEncOutput<'vir> {
    /// Information about the corresponding function.
    function_data: FunctionData<'vir>,

    /// The lifetime projections of all arguments to the function.
    inputs: Vec<FunctionShapeInput>,

    /// The lifetime projections of all function outputs (according to the
    /// corresponding [`FunctionShape`]). This *includes* lifetime projections
    /// of nested lifetimes in the function arguments.
    outputs: Vec<FunctionShapeOutput>,

    /// Encoded VIR expressions for the magic wands.
    wands: Vec<PurifiedWandData>,
}

impl<'vir> PurifiedWandEncOutput<'vir> {
    pub(crate) fn fn_sig(&self, vcx: &'vir vir::VirCtxt<'vir>) -> ty::FnSig<'vir> {
        self.function_data.instantiated_fn_sig(vcx.tcx())
    }

    pub(crate) fn g_params(&self, vcx: &'vir vir::VirCtxt<'vir>) -> GParams<'vir> {
        GParams::new(
            self.function_data.substs(),
            self.function_data.param_env(vcx.tcx()),
            false,
        )
    }

    fn encode_type_for_function_shape_node(
        &self,
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, impl TaskEncoder>,
        g: impl Into<FunctionShapeNode>,
        mut snap: impl FnMut(mir::Local) -> vir::ExprSnap<'vir>,
    ) -> vir::ExprBool<'vir> {
        use vir::Reify;
        let g = g.into();
        let fn_sig = self.fn_sig(vcx);
        let ty = RustTyDecomposition::from_ty(g.ty(fn_sig), vcx.tcx(), self.g_params(vcx));
        let self_ty_enc = deps
            .require_dep::<TyUsePurifiedEnc>(g.with_base(ty).base())
            .unwrap();
        let type_condition = vcx.mk_lazy_expr(
            "type_condition",
            vir::TYPE_BOOL,
            Box::new(move |vcx, self_expr: vir::ExprSnap<'vir>| {
                self_ty_enc
                    .data
                    .snap_to_ty_assertion(
                        vcx,
                        self_expr)}
                        .kind),
            None);

        let local = g.mir_local();
        let local_snap = snap(local);
        type_condition.reify(vcx, local_snap)
    }

    pub fn indirect_pres<'a, E: TaskEncoder>(
        &'a self,
        vcx: &'vir vir::VirCtxt<'vir>,
        local_defs: &'a MirLocalDefEncOutput<'vir>,
        deps: &'a mut TaskEncoderDependencies<'vir, E>,
    ) -> impl Iterator<Item = vir::ExprBool<'vir>> + 'a {
        let mk_pf_snap = |i: mir::Local| {
            let decl = local_defs[i].local_snap;
            let pf_name = vir::vir_format!(vcx, "_pf{}", decl.name);
            vcx.mk_local_decl(pf_name, decl.ty()).expr(vcx)
        };
        self.inputs()
            .map(move |g| self.encode_type_for_function_shape_node(vcx, deps, g, mk_pf_snap))
    }

    pub fn indirect_posts<'a, E: TaskEncoder>(
        &'a self,
        vcx: &'vir vir::VirCtxt<'vir>,
        local_defs: &'a MirLocalDefEncOutput<'vir>,
        deps: &'a mut TaskEncoderDependencies<'vir, E>,
    ) -> impl Iterator<Item = vir::ExprBool<'vir>> + 'a {
        // The encoded predicates for the input lifetime projections that are
        // not blocked by any of the result lifetime projections. These will be
        // encoded as part of the postcondition of the function (in contrast,
        // the predicates for the blocked inputs will appear on the right-hand
        // side of a magic wand in the postcondition).
        let unblocked_input_posts = self
            .inputs()
            .filter(|i| !self.blocked_inputs().contains(i))
            .map(|g| {
                self.encode_type_for_function_shape_node(vcx, deps, g, |i| {
                    local_defs[i].local_snap_ex
                })
            })
            .collect::<Vec<_>>()
            .into_iter();

        let output_posts = self.outputs().map(|g| {
            self.encode_type_for_function_shape_node(vcx, deps, g, |i| local_defs[i].local_snap_ex)
        });
        unblocked_input_posts.chain(output_posts)
    }

    pub fn apply_reconstructors<E: TaskEncoder>(
        &self,
        lhs: &[vir::ExprSnap<'vir>],
        rhs: &'vir [vir::ExprDyn<'vir>],
        label_pre: &'vir str,
        label_post: &'vir str,
        visitor: &mut PurifiedEncVisitor<'vir, '_, E>,
    ) {
        for wand_data in self.viper_wands() {
            let reconstructor_idn = visitor
                .deps
                .require_dep::<ReconstructorCallEnc>(ReconstructorCallEncTask::new(
                    self.function_data,
                    wand_data,
                ))
                .unwrap();
            let call = reconstructor_idn.call(lhs, rhs);
            // let call = vir::with_vcx(|vcx| vcx.alloc(vir::StmtGenData::new(vcx.alloc(call))));
            visitor.stmts(call);
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PurifiedWandEncTask<'tcx> {
    pub data: FunctionData<'tcx>,
}

impl<'tcx> PurifiedWandEncTask<'tcx> {
    pub fn def_id(&self) -> DefId {
        self.data.def_id()
    }

    pub fn function_shape(
        &self,
        vcx: &vir::VirCtxt<'tcx>,
    ) -> Result<FunctionShape, MakeFunctionShapeError> {
        self.data.shape(vcx.tcx())
    }
}

pub type PurifiedWandRhsKey = FunctionShapeInput;
pub type PurifiedWandLhsKey = FunctionShapeNode;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PurifiedWandData {
    def_id: DefId,
    /// Lifetime projections on the right-hand side of the wand. Guaranteed to be
    /// non-empty.
    rhs: Vec<PurifiedWandRhsKey>,
    /// Lifetime projections on the left-hand side of the wand. Guaranteed to be
    /// non-empty.
    lhs: Vec<PurifiedWandLhsKey>,
}

impl PurifiedWandData {
    pub fn new(def_id: DefId, lhs: Vec<PurifiedWandLhsKey>, rhs: Vec<PurifiedWandRhsKey>) -> Self {
        debug_assert!(!lhs.is_empty());
        debug_assert!(!rhs.is_empty());
        Self { def_id, rhs, lhs }
    }
}

impl TaskEncoder for PurifiedWandEnc {
    task_encoder::encoder_cache!(PurifiedWandEnc);

    type TaskDescription<'vir> = PurifiedWandEncTask<'vir>;

    type OutputFullDependency<'vir> = PurifiedWandEncOutput<'vir>;

    type EncodingError = PurifiedWandEncError;

    const ENCODER_NAME: &'static str = "purified wand encoder";

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        task.clone()
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(task_key.clone(), ())?;
        vir::with_vcx(|vcx| {
            let def_id = task_key.def_id();

            let shape = task_key.function_shape(vcx).map_err(|e| {
                EncodeFullError::EncodingError(
                    PurifiedWandEncError::Unsupported(format!("function shape: {e:?}")),
                    None,
                )
            })?;

            let coupled_edges = shape.coupled_edges().map_err(|e| {
                EncodeFullError::EncodingError(
                    PurifiedWandEncError::Unsupported(format!("coupled edges: {e:?}")),
                    None,
                )
            })?;

            let (inputs, outputs) = shape.take_inputs_and_outputs();
            let spec = deps.require_dep::<MirSpecEnc<Purified>>((def_id, false))?;
            if coupled_edges.is_empty() {
                assert!(spec.pledges.is_empty());
                return Ok((
                    (),
                    PurifiedWandEncOutput {
                        function_data: task_key.data,
                        inputs,
                        outputs,
                        wands: vec![],
                    },
                ));
            }
            let pledges = spec.pledges;
            if pledges.len() > 1 && coupled_edges.len() > 1 {
                return Err(EncodeFullError::EncodingError(
                    PurifiedWandEncError::Unsupported(format!(
                        "multiple pledges: {pledges:?}, coupled edges: {coupled_edges:?}"
                    )),
                    None,
                ));
            }
            let wands: Vec<PurifiedWandData> = coupled_edges
                .into_iter()
                .map(|hyper_edge| {
                    let (sources, targets) = hyper_edge.into_tuple();
                    PurifiedWandData::new(def_id, targets, sources)
                })
                .collect();

            Ok((
                (),
                PurifiedWandEncOutput {
                    function_data: task_key.data,
                    inputs,
                    outputs,
                    wands,
                },
            ))
        })
    }
}

impl<'vir> PurifiedWandEncOutput<'vir> {
    pub fn viper_wands(&self) -> Vec<PurifiedWandData> {
        self.wands.clone()
    }

    /// All lifetime projections in the arguments that are blocked by any of the
    /// lifetime projections in the function's result.
    pub fn blocked_inputs(&self) -> FxHashSet<FunctionShapeInput> {
        self.wands
            .iter()
            .flat_map(|wand| wand.rhs.iter().copied())
            .collect()
    }

    pub fn inputs(&self) -> impl Iterator<Item = FunctionShapeInput> + '_ {
        self.inputs.iter().copied()
    }

    pub fn outputs(&self) -> impl Iterator<Item = FunctionShapeOutput> + '_ {
        self.outputs.iter().copied()
    }
}

pub struct ReconstructorCallEnc;

#[derive(Debug, Clone)]
pub struct ReconstructorCallEncOutput<'vir> {
    method: ReconstructorEncOutputRef<'vir>,
    ty_args: GArgsTy<'vir>,
    inputs: Vec<GArgCaster<'vir, Purified>>,
    outputs: Vec<GArgCaster<'vir, Purified>>,
}

impl<'vir> ReconstructorCallEncOutput<'vir> {
    pub fn call(
        &self,
        args: &[vir::ExprSnap<'vir>],
        dests: &'vir [vir::ExprDyn<'vir>],
    ) -> Vec<vir::Stmt<'vir>> {
        assert_eq!(self.inputs.len(), args.len());
        assert_eq!(self.outputs.len(), dests.len());
        let inputs: Vec<_> = args
            .iter()
            .zip(self.inputs.iter())
            .map(|(arg, caster)| caster.cast_to_callee_ctx(arg))
            .collect();
        let call = self.method.method_ref.call()(
            (&inputs, self.ty_args.get_ty(), self.ty_args.get_const()),
            &dests,
        );
        vir::with_vcx(|vcx| {
            let call = vcx.alloc(vir::StmtGenData::new(vcx.alloc(call)));
            vec![call]
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ReconstructorCallEncTask<'tcx> {
    pub fn_data: FunctionData<'tcx>,
    pub wand_data: PurifiedWandData,
}

impl<'tcx> ReconstructorCallEncTask<'tcx> {
    pub fn new(fn_data: FunctionData<'tcx>, wand_data: PurifiedWandData) -> Self {
        ReconstructorCallEncTask { fn_data, wand_data }
    }

    pub fn def_id(&self) -> DefId {
        self.fn_data.def_id()
    }
}

impl TaskEncoder for ReconstructorCallEnc {
    task_encoder::encoder_cache!(ReconstructorCallEnc);
    type TaskDescription<'tcx> = ReconstructorCallEncTask<'tcx>;
    type OutputFullDependency<'vir> = ReconstructorCallEncOutput<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        task.clone()
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(task_key.clone(), ())?;
        let method_ref = deps.require_ref::<ReconstructorEnc>(task_key.wand_data.clone())?;
        let signature = RustSignature::new(task_key.def_id());

        let gargs = GArgs::new(task_key.def_id(), task_key.fn_data.substs());
        let ty_args = deps.require_dep::<GArgsTyEnc>(gargs)?;
        let inputs = signature
            .inputs
            .iter()
            .map(|ty| {
                let normalized = ty.decompose_compare_normalize(signature.gparams, gargs);
                deps.require_dep::<GArgsCastEnc<Purified>>(normalized)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let normalized = signature
            .output
            .decompose_compare_normalize(signature.gparams, gargs);
        let output = deps.require_dep::<GArgsCastEnc<Purified>>(normalized)?;
        Ok((
            (),
            ReconstructorCallEncOutput {
                method: method_ref,
                ty_args,
                inputs,
                outputs: vec![output],
            },
        ))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        ReconstructorEnc::emit_outputs(program);
    }
}

/// Encodes the magic wands given a function signature.
pub struct ReconstructorEnc;

// pub struct ReconstructorEncTask<'vir> {}

#[derive(Debug, Clone)]
pub struct ReconstructorEncOutputRef<'vir> {
    pub(crate) method_ref: MethodIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap)>,
}

impl<'vir> OutputRefAny for ReconstructorEncOutputRef<'vir> {}

#[derive(Debug, Clone, Copy)]
pub struct ReconstructorEncOutput<'vir> {
    method: vir::Method<'vir>,
}

#[derive(Clone, Debug)]
pub struct ReconstructorEncError;

impl TaskEncoder for ReconstructorEnc {
    task_encoder::encoder_cache!(ReconstructorEnc);

    type TaskDescription<'tcx> = PurifiedWandData;

    type OutputRef<'vir> = ReconstructorEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = ReconstructorEncOutput<'vir>;

    type EncodingError = ReconstructorEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        task.clone()
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let def_id = task_key.def_id;
        let signature = RustSignature::new(def_id);
        vir::with_vcx(|vcx| {
            let span = vcx.tcx().def_span(def_id);
            let local_defs = deps.require_dep_spanned::<MirLocalDefEnc<Purified>>(
                MirLocalDefEncTask::Local {
                    def_id,
                    all_locals: false,
                },
                span,
            )?;

            let gparams = GParams::from(def_id);
            let generics = deps
                .require_dep_spanned::<GenericParamsEnc>(gparams, span)
                .unwrap();

            let name = vir::vir_format_identifier!(vcx, "r_{}", vcx.tcx().def_path_str(def_id));

            let mut args = Vec::new();
            let mut arg_tys = Vec::new();
            let mut pres = Vec::new();
            for &g in &task_key.lhs {
                let local = g.mir_local();
                let ty = if local.as_usize() == 0 {
                    signature.output
                } else {
                    signature.inputs[local.as_usize()]
                };
                let decl = local_defs[g.mir_local()].local_snap;
                let pf_decl =
                    vcx.mk_local_decl(vir::vir_format!(vcx, "_pf{}", decl.name), decl.ty());
                args.push(pf_decl);
                arg_tys.push(pf_decl.ty());
                pres.push(generics.ty_assertion(deps, pf_decl.expr(vcx), ty.decompose(gparams)));
            }

            let mut rets = Vec::new();
            let mut posts = Vec::new();
            for &g in &task_key.rhs {
                let local_def = local_defs[g.mir_local()];
                rets.push(local_def.local_snap);
                posts.push(local_def.impure_pred);
            }

            let method_ref = MethodIdn::new(
                name,
                (
                    vcx.alloc_slice(&arg_tys),
                    generics.ty_args(),
                    generics.const_args(),
                ),
            );

            deps.emit_output_ref(task_key.clone(), ReconstructorEncOutputRef { method_ref })?;

            let pledges = deps
                .require_dep_spanned::<MirSpecEnc<Purified>>((def_id, false), span)?
                .pledges;

            for p in pledges {
                p.expiry_obligation_expr().map(|b| pres.push(b));
                posts.push(p.spec);
            }

            let method = vcx.mk_method(
                method_ref,
                (&args, generics.ty_decls(), generics.const_decls()),
                vcx.alloc_slice(&rets.as_dyn()),
                vcx.alloc_slice(&pres),
                vcx.alloc_slice(&posts),
                None,
            );

            Ok((ReconstructorEncOutput { method }, ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors() {
            program.add_method(output.method);
        }
    }
}
