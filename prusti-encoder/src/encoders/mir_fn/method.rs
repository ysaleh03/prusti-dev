use pcg::{borrow_checker::r#impl::NllBorrowCheckerImpl, borrow_pcg::FunctionData};
use prusti_rustc_interface::{middle::mir, span::def_id::DefId};
use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, MethodIdn, macros::ExprQuote};

use crate::{
    encoders::{
        Impure, ImpureEncVisitor, MirLocalDefEnc, MirLocalDefEncTask, MirSpecEnc, Purified,
        PurifiedEncVisitor, PurifiedMirLocalDefEnc, PurifiedMirLocalDefEncTask, PurifiedWandEnc,
        Purity, WandEnc, WandEncTask,
        mir_fn::{CallTaskDescription, RustSignature},
        purified::{fn_wand::PurifiedWandEncTask, spec::PurifiedMirSpecEnc},
        ty::{
            data::TySpecifics,
            generics::{
                GArgCaster, GArgsCastEnc, GArgsTy, GArgsTyEnc, GParams, GenericParamsEnc,
                PurityCasters,
            },
        },
    },
    trait_support::is_function_with_body,
};

// Method wrapper

pub struct ImpureMethodCallEnc;
pub struct PurifiedMethodCallEnc;

#[derive(Debug, Clone)]
pub struct MethodCallEncOutput<'vir, P: PurityCasters> {
    method: MethodEncOutputRef<'vir, P>,
    ty_args: GArgsTy<'vir>,
    inputs: Vec<GArgCaster<'vir, P>>,
    outputs: Vec<GArgCaster<'vir, P>>,
}

impl<'vir> MethodCallEncOutput<'vir, Impure> {
    pub fn call(
        &self,
        mut args: Vec<vir::ExprRef<'vir>>,
        ret: vir::ExprRef<'vir>,
    ) -> Vec<vir::Stmt<'vir>> {
        assert_eq!(self.inputs.len(), args.len());
        let generics = args.iter().zip(self.inputs.iter());
        let mut stmts: Vec<_> = generics
            .filter_map(|(arg, caster)| caster.cast_to_callee_ctx(arg))
            .collect();

        args.insert(0, ret);
        let call = self.method.method_ref.call()(
            (&args, self.ty_args.get_ty(), self.ty_args.get_const()),
            &[],
        );
        let call = vir::with_vcx(|vcx| vcx.alloc(vir::StmtGenData::new(vcx.alloc(call))));
        stmts.push(call);

        let result = self.outputs[0].cast_to_caller_ctx(ret);
        if let Some(result) = result {
            stmts.push(result);
        }
        stmts
    }
}

impl TaskEncoder for ImpureMethodCallEnc {
    task_encoder::encoder_cache!(ImpureMethodCallEnc);
    type TaskDescription<'tcx> = CallTaskDescription<'tcx>;
    type OutputFullDependency<'vir> = MethodCallEncOutput<'vir, Impure>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let method_ref = deps.require_ref::<ImpureMethodEnc>(task_key.callee)?;
        let signature = RustSignature::new(task_key.callee);
        let ty_args = deps.require_dep::<GArgsTyEnc>(task_key.gargs)?;
        let inputs = signature
            .inputs
            .iter()
            .map(|ty| {
                let normalized = ty.decompose_compare_normalize(signature.gparams, task_key.gargs);
                deps.require_dep::<GArgsCastEnc<Impure>>(normalized)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let normalized = signature
            .output
            .decompose_compare_normalize(signature.gparams, task_key.gargs);
        let output = deps.require_dep::<GArgsCastEnc<Impure>>(normalized)?;
        Ok((
            (),
            MethodCallEncOutput {
                method: method_ref,
                ty_args,
                inputs,
                outputs: vec![output],
            },
        ))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        ImpureMethodEnc::emit_outputs(program);
    }
}

impl<'vir> MethodCallEncOutput<'vir, Purified> {
    pub fn call(
        &self,
        args: Vec<vir::ExprSnap<'vir>>,
        rets: &'vir [vir::LocalDeclDyn<'vir>],
    ) -> Vec<vir::Stmt<'vir>> {
        assert_eq!(self.inputs.len(), args.len());
        assert_eq!(self.outputs.len(), rets.len());
        let inputs: Vec<_> = args
            .iter()
            .zip(self.inputs.iter())
            .map(|(arg, caster)| caster.cast_to_callee_ctx(arg))
            .collect();
        let call = self.method.method_ref.call()(
            (&inputs, self.ty_args.get_ty(), self.ty_args.get_const()),
            &rets,
        );
        let call = vir::with_vcx(|vcx| vcx.alloc(vir::StmtGenData::new(vcx.alloc(call))));
        vec![call]
    }
}

impl TaskEncoder for PurifiedMethodCallEnc {
    task_encoder::encoder_cache!(PurifiedMethodCallEnc);
    type TaskDescription<'tcx> = CallTaskDescription<'tcx>;
    type OutputFullDependency<'vir> = MethodCallEncOutput<'vir, Purified>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let method_ref = deps.require_ref::<PurifiedMethodEnc>(task_key.callee)?;
        let signature = RustSignature::new(task_key.callee);
        let ty_args = deps.require_dep::<GArgsTyEnc>(task_key.gargs)?;
        let inputs = signature
            .inputs
            .iter()
            .map(|ty| {
                let normalized = ty.decompose_compare_normalize(signature.gparams, task_key.gargs);
                deps.require_dep::<GArgsCastEnc<Purified>>(normalized)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let normalized = signature
            .output
            .decompose_compare_normalize(signature.gparams, task_key.gargs);
        let output = deps.require_dep::<GArgsCastEnc<Purified>>(normalized)?;
        Ok((
            (),
            MethodCallEncOutput {
                method: method_ref,
                ty_args,
                inputs,
                outputs: vec![output],
            },
        ))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        PurifiedMethodEnc::emit_outputs(program);
    }
}

// Method encoder

pub(super) struct ImpureMethodEnc;
pub(super) struct PurifiedMethodEnc;

#[derive(Debug, Clone)]
pub(super) struct MethodEncOutputRef<'vir, P: Purity> {
    method_ref: MethodIdn<'vir, (vir::Many<P::ArgTy>, vir::ManyTyVal, vir::ManyCSnap)>,
}

impl<'vir, P: Purity> OutputRefAny for MethodEncOutputRef<'vir, P> {}

#[derive(Debug, Clone, Copy)]
pub(super) struct MethodEncOutput<'vir> {
    method: vir::Method<'vir>,
}

#[derive(Clone, Debug)]
pub enum MethodEncError {}

impl TaskEncoder for ImpureMethodEnc {
    task_encoder::encoder_cache!(ImpureMethodEnc);
    type TaskDescription<'tcx> = DefId;

    type OutputRef<'vir> = MethodEncOutputRef<'vir, Impure>;
    type OutputFullLocal<'vir> = MethodEncOutput<'vir>;

    type EncodingError = MethodEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let def_id = *task_key;
        vir::with_vcx(|vcx| {
            use mir::visit::Visitor;

            let span = vcx.tcx().def_span(def_id);
            let trusted = crate::encoders::is_function_trusted(def_id);

            let arg_defs = deps.require_ref_spanned::<MirLocalDefEnc>(
                MirLocalDefEncTask::Local {
                    def_id,
                    all_locals: false,
                },
                span,
            )?;

            // Argument count for the Viper method:
            // - one (`Ref`) for the return place;
            // - one (`Ref`) for each MIR argument.
            //
            // Note that the return place is modelled as an argument of the
            // Viper method. This corresponds to an execution model where the
            // method can return data to the caller without a copy--it directly
            // modifies a place provided by the caller.
            //
            // TODO: type parameters: for generic methods we will want to pass
            //   values of type `Type` as well`
            let arg_count = arg_defs.arg_count + 1;

            // Create the identifier and use it as an output ref. This is what
            // is used when other methods call this one.
            let method_name =
                vir::vir_format_identifier!(vcx, "m_{}", vcx.tcx().def_path_str(def_id));
            let ref_args = vcx.alloc_slice(&vec![vir::TYPE_REF; arg_count]);
            let params = GParams::from(def_id);
            let generics = deps.require_dep_spanned::<GenericParamsEnc>(params, span)?;
            let method_ref = MethodIdn::new(
                method_name,
                (ref_args, generics.ty_args(), generics.const_args()),
            );
            deps.emit_output_ref(def_id, MethodEncOutputRef { method_ref })?;

            let arg_defs = deps.require_dep_spanned::<MirLocalDefEnc>(
                MirLocalDefEncTask::Local {
                    def_id,
                    all_locals: false,
                },
                span,
            )?;

            // Method contract. We will need to emit pre- and postconditions for
            // the permissions, the functional spec, and (in the postcondition)
            // wands in case of a reborrowing function.
            let mut pres = Vec::new();
            let mut posts = Vec::new();
            let spec = deps.require_dep_spanned::<MirSpecEnc>((def_id, false), span)?;
            let function_data = FunctionData::new(def_id, params.rust_params(), None);
            let wands = deps.require_dep_spanned::<WandEnc>(
                WandEncTask {
                    data: function_data,
                },
                span,
            )?;

            let gparams = GParams::from(def_id);
            // Add direct resources for inputs and outputs to the pre- and
            // postconditions, respectively. "Direct" here refers to owned
            // Viper resources that must be passed in/out given the signature,
            // without going through any dereferences.
            let mut args = Vec::with_capacity(arg_count + gparams.count());
            for arg_idx in (0..arg_count).map(mir::Local::from) {
                let name_p = arg_defs[arg_idx].local.name;
                args.push(vir::vir_local_decl! { vcx; [name_p] : Ref });
                if arg_idx != mir::RETURN_PLACE {
                    pres.push(arg_defs[arg_idx].impure_pred);
                }
            }
            posts.push(arg_defs[mir::RETURN_PLACE].impure_pred);

            // ..
            pres.extend(wands.indirect_pres(vcx, &arg_defs, deps));
            posts.extend(wands.indirect_posts(vcx, &arg_defs, deps));
            posts.extend(wands.wand_posts(vcx, &arg_defs, deps));

            // Do not encode the method body if it is external, trusted, just
            // a call stub, or a trait function without a default implementation
            let local_def_id = def_id
                .as_local()
                .filter(|_| !trusted && is_function_with_body(vcx.tcx(), def_id));
            let blocks = if let Some(local_def_id) = local_def_id {
                let body_with_facts = vcx.body_mut().get_impure_fn_body_with_facts(local_def_id);
                let body = &body_with_facts.body;
                let local_defs = deps.require_dep_spanned::<MirLocalDefEnc>(
                    MirLocalDefEncTask::Local {
                        def_id: local_def_id.to_def_id(),
                        all_locals: true,
                    },
                    span,
                )?;

                let bc = NllBorrowCheckerImpl::new(vcx.tcx(), &body_with_facts);
                let pcg_ctxt = pcg::PcgCtxt::new(&body_with_facts.body, vcx.tcx(), &bc);
                let fpcs_analysis = pcg::run_pcg(&pcg_ctxt);
                pcg_ctxt.update_debug_visualization_metadata();

                let block_count = body.basic_blocks.len();

                let mut encoded_blocks = Vec::with_capacity(
                    // extra blocks: Start, End
                    2 + block_count,
                );
                let mut start_stmts = Vec::new();
                for local in (arg_count..body.local_decls.len()).map(mir::Local::from) {
                    let name_p = local_defs[local].local.name;
                    start_stmts.push(
                        vcx.mk_local_decl_stmt(vir::vir_local_decl! { vcx; [name_p] : Ref }, None),
                    )
                }
                // This will be overwritten later.
                encoded_blocks.push(vcx.mk_cfg_block(
                    &vir::CfgBlockLabelData::Start,
                    &[],
                    &[],
                    vcx.mk_goto_stmt(&vir::CfgBlockLabelData::BasicBlock(0)),
                ));

                deps.check_cycle()?;
                let mut visitor = ImpureEncVisitor {
                    vcx,
                    deps,
                    def_id,
                    local_decls: &body.local_decls,
                    fpcs_analysis,
                    local_defs,
                    body,

                    wands,

                    tmp_ctr: 0,
                    label_ctr: 0,
                    call_labels: Default::default(),
                    from_to_vars: Default::default(),

                    current_block_label: None,
                    current_fpcs: None,

                    current_stmts: None,
                    current_terminator: None,
                    encoded_blocks,
                };
                visitor.visit_body(body);
                start_stmts.extend(
                    visitor
                        .from_to_vars
                        .decls()
                        .map(|v| vcx.mk_local_decl_stmt(v, Some(vcx.mk_bool::<false>()))),
                );
                visitor.encoded_blocks[0] = vcx.mk_cfg_block(
                    &vir::CfgBlockLabelData::Start,
                    &[],
                    vcx.alloc_slice(&start_stmts),
                    vcx.mk_goto_stmt(&vir::CfgBlockLabelData::BasicBlock(0)),
                );

                visitor.encoded_blocks.push(vcx.mk_cfg_block(
                    vcx.alloc(vir::CfgBlockLabelData::End),
                    &[],
                    &[],
                    vcx.alloc(vir::TerminatorStmtData::Exit),
                ));

                visitor.deps.check_cycle()?;

                Some(visitor.encoded_blocks)
            } else {
                None
            };

            // Add functional specification as the last pre- and postconditions.
            pres.extend(spec.pres);
            posts.extend(spec.posts);

            Ok((
                MethodEncOutput {
                    method: vcx.mk_method(
                        method_ref,
                        (&args, generics.ty_decls(), generics.const_decls()),
                        &[],
                        vcx.alloc_slice(&pres),
                        vcx.alloc_slice(&posts),
                        blocks.map(|blocks| vcx.alloc_slice(&blocks)),
                    ),
                },
                (),
            ))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors() {
            program.add_method(output.method);
        }
    }
}

impl TaskEncoder for PurifiedMethodEnc {
    task_encoder::encoder_cache!(PurifiedMethodEnc);
    type TaskDescription<'tcx> = DefId;

    type OutputRef<'vir> = MethodEncOutputRef<'vir, Purified>;
    type OutputFullLocal<'vir> = MethodEncOutput<'vir>;

    type EncodingError = MethodEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let def_id = *task_key;
        vir::with_vcx(|vcx| {
            use mir::visit::Visitor;

            let span = vcx.tcx().def_span(def_id);
            let trusted = crate::encoders::is_function_trusted(def_id);
            let signature = RustSignature::new(def_id);

            let local_defs = deps.require_dep_spanned::<PurifiedMirLocalDefEnc>(
                PurifiedMirLocalDefEncTask::Local {
                    def_id,
                    all_locals: false,
                },
                span,
            )?;

            // Argument count for the Viper method:
            // - one arg for each MIR argument.
            //
            // In this encoder, the return place is *not* modelled as an argument
            // of the Viper method. This is different from the Impure encoder.
            //
            // TODO: type parameters: for generic methods we will want to pass
            //   values of type `Type` as well`
            let arg_count = local_defs.arg_count + 1;

            // Create the identifier and use it as an output ref. This is what
            // is used when other methods call this one.
            let method_name =
                vir::vir_format_identifier!(vcx, "m_{}", vcx.tcx().def_path_str(def_id));
            let snap_args = vcx.alloc_slice(&local_defs.snap_ty_args().collect::<Vec<_>>());
            let gparams = GParams::from(def_id);
            let generics = deps.require_dep_spanned::<GenericParamsEnc>(gparams, span)?;
            let method_ref = MethodIdn::new(
                method_name,
                (snap_args, generics.ty_args(), generics.const_args()),
            );
            deps.emit_output_ref(def_id, MethodEncOutputRef { method_ref })?;

            // Method contract. We will need to emit pre- and postconditions for
            // parameter types and the functional spec.
            let mut pres = Vec::new();
            let mut posts = Vec::new();
            let spec = deps.require_dep_spanned::<PurifiedMirSpecEnc>((def_id, false), span)?;
            let function_data = FunctionData::new(def_id, gparams.rust_params(), None);
            let wands = deps.require_dep_spanned::<PurifiedWandEnc>(
                PurifiedWandEncTask {
                    data: function_data,
                },
                span,
            )?;

            let mut rets = vec![local_defs.ret().local_snap];
            let args = local_defs
                .local_decl_args()
                .map(|decl| {
                    vcx.mk_local_decl(
                        vir::vir_format_identifier!(vcx, "{}_param", decl.name).to_str(),
                        decl.ty,
                    )
                })
                .collect::<Vec<_>>();

            let mut return_to_remote = Vec::new();

            for (ty, decl) in signature.inputs.iter().zip(local_defs.local_decl_args()) {
                match ty.decompose(gparams).ty.specifics {
                    TySpecifics::MutRef(..) => {
                        let name_r =
                            vir::vir_format_identifier!(vcx, "{}_return", decl.name).to_str();
                        let decl = vcx.mk_local_decl(name_r, decl.ty);
                        rets.push(decl);
                        return_to_remote.push(decl);
                    }
                    _ => (),
                };
            }

            // Do not encode the method body if it is external, trusted, just
            // a call stub, or a trait function without a default implementation
            let local_def_id = def_id
                .as_local()
                .filter(|_| !trusted && is_function_with_body(vcx.tcx(), def_id));
            let blocks = if let Some(local_def_id) = local_def_id {
                let body_with_facts = vcx.body_mut().get_impure_fn_body_with_facts(local_def_id);
                let body = &body_with_facts.body;
                let local_defs = deps.require_dep_spanned::<PurifiedMirLocalDefEnc>(
                    PurifiedMirLocalDefEncTask::Local {
                        def_id: local_def_id.to_def_id(),
                        all_locals: true,
                    },
                    span,
                )?;

                let bc = NllBorrowCheckerImpl::new(vcx.tcx(), &body_with_facts);
                let pcg_ctxt = pcg::PcgCtxt::new(&body_with_facts.body, vcx.tcx(), &bc);
                let fpcs_analysis = pcg::run_pcg(&pcg_ctxt);
                pcg_ctxt.update_debug_visualization_metadata();

                let block_count = body.basic_blocks.len();

                let mut encoded_blocks = Vec::with_capacity(
                    // extra blocks: Start, End
                    2 + block_count,
                );

                let mut start_stmts = Vec::new();
                let mut end_stmts = Vec::new();

                for local in (1..arg_count).map(mir::Local::from) {
                    let name_s = local_defs[local].local_snap.name;
                    let type_s = local_defs[local].local_snap.ty;
                    start_stmts.push(vcx.mk_local_decl_stmt(
                        vir::vir_local_decl! { vcx; [name_s] : [type_s] },
                        Some(args[local.as_usize() - 1].expr(vcx)),
                    ))
                }
                for local in (arg_count..body.local_decls.len()).map(mir::Local::from) {
                    let name_s = local_defs[local].local_snap.name;
                    let type_s = local_defs[local].local_snap.ty;
                    start_stmts.push(vcx.mk_local_decl_stmt(
                        vir::vir_local_decl! { vcx; [name_s] : [type_s] },
                        None,
                    ))
                }
                // This will be overwritten later.
                encoded_blocks.push(vcx.mk_cfg_block(
                    &vir::CfgBlockLabelData::Start,
                    &[],
                    &[],
                    vcx.mk_goto_stmt(&vir::CfgBlockLabelData::BasicBlock(0)),
                ));

                deps.check_cycle()?;
                let mut visitor = PurifiedEncVisitor {
                    vcx,
                    deps,
                    def_id,
                    local_decls: &body.local_decls,
                    fpcs_analysis,
                    local_defs,
                    body,

                    wands,

                    // declared_remotes: Default::default(),
                    // remote_place_to_local_decl: Default::default(),
                    // return_to_remote,
                    declared_vars: Default::default(),
                    place_to_local_decl: Default::default(),

                    tmp_ctr: 0,
                    label_ctr: 0,
                    call_labels: Default::default(),
                    from_to_vars: Default::default(),

                    current_block_label: None,
                    current_fpcs: None,

                    current_stmts: None,
                    current_terminator: None,
                    encoded_blocks,
                };
                visitor.visit_body(body);
                start_stmts.extend(
                    visitor
                        .from_to_vars
                        .decls()
                        .map(|v| vcx.mk_local_decl_stmt(v, Some(vcx.mk_bool::<false>()))),
                );
                visitor.encoded_blocks[0] = vcx.mk_cfg_block(
                    &vir::CfgBlockLabelData::Start,
                    &[],
                    vcx.alloc_slice(&start_stmts),
                    vcx.mk_goto_stmt(&vir::CfgBlockLabelData::BasicBlock(0)),
                );

                visitor.encoded_blocks.push(vcx.mk_cfg_block(
                    vcx.alloc(vir::CfgBlockLabelData::End),
                    &[],
                    vcx.alloc_slice(&end_stmts),
                    vcx.alloc(vir::TerminatorStmtData::Exit),
                ));

                visitor.deps.check_cycle()?;

                Some(visitor.encoded_blocks)
            } else {
                None
            };

            // Add functional specification as the last pre- and postconditions.
            pres.extend(spec.pres);
            posts.extend(spec.posts);

            Ok((
                MethodEncOutput {
                    method: vcx.mk_method(
                        method_ref,
                        (&args, generics.ty_decls(), generics.const_decls()),
                        vcx.alloc_slice(&rets.as_dyn()),
                        vcx.alloc_slice(&pres),
                        vcx.alloc_slice(&posts),
                        blocks.map(|blocks| vcx.alloc_slice(&blocks)),
                    ),
                },
                (),
            ))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors() {
            program.add_method(output.method);
        }
    }
}
