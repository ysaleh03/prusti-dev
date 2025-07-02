use std::alloc::Global;

use pcg::{borrow_checker::r#impl::BorrowCheckerImpl, r#loop::LoopAnalysis};
use prusti_rustc_interface::middle::mir;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{MethodIdent, UnknownArity, ViperIdent};

use crate::{
    encoders::{
        lifted::func_def_ty_params::LiftedTyParamsEnc, MirPurifiedEnc, PurifiedEncVisitor,
        PurifiedLocalDef, PurifiedLocalDefEnc, PurifiedMirSpecEnc, PurifiedWandEnc,
        PurifiedWandEncTask,
    },
    trait_support::is_function_with_body,
};

use super::function_enc::FunctionEnc;

#[derive(Clone, Debug)]
pub struct PurifiedFunctionEncError;

#[derive(Clone, Debug)]
pub struct PurifiedFunctionEncOutputRef<'vir> {
    pub method_ref: MethodIdent<'vir, UnknownArity<'vir>>,
}
impl<'vir> task_encoder::OutputRefAny for PurifiedFunctionEncOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct PurifiedFunctionEncOutput<'vir> {
    pub method: vir::Method<'vir>,
}

const ENCODE_REACH_BB: bool = false;

pub trait PurifiedFunctionEnc
where
    Self: 'static
        + Sized
        + FunctionEnc
        + for<'vir> TaskEncoder<OutputRef<'vir> = PurifiedFunctionEncOutputRef<'vir>>,
{
    /// Generates the identifier for the method; for a monomorphic encoding,
    /// this should be a name including (mangled) type arguments
    fn mk_method_ident<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        task_key: &Self::TaskKey<'vir>,
    ) -> ViperIdent<'vir>;

    fn mk_conditions<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        task_key: &Self::TaskKey<'vir>,
        arg: &PurifiedLocalDef<'vir>,
        idx: usize,
    ) -> vir::Expr<'vir>;

    fn encode<'vir>(
        task_key: Self::TaskKey<'vir>,
        mut deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> Result<PurifiedFunctionEncOutput<'vir>, EncodeFullError<'vir, Self>> {
        let def_id = Self::get_def_id(&task_key);
        let caller_def_id = Self::get_caller_def_id(&task_key);
        vir::with_vcx(|vcx| {
            use mir::visit::Visitor;

            let substs = Self::get_substs(vcx, &task_key);
            let trusted = crate::encoders::is_function_trusted(def_id, substs);
            let local_defs =
                deps.require_local::<PurifiedLocalDefEnc>((def_id, substs, caller_def_id))?;

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
            let method_name = Self::mk_method_ident(vcx, &task_key);
            let mut args = Vec::with_capacity(arg_count);
            for arg_idx in 1..arg_count {
                let local_ty = local_defs.locals[arg_idx.into()].local.ty;
                args.push(local_ty);
            }
            let param_ty_decls = deps
                .require_local::<LiftedTyParamsEnc>(substs)?
                .iter()
                .map(|g| g.decl())
                .collect::<Vec<_>>();
            args.extend(param_ty_decls.iter().map(|decl| decl.ty));
            let args = UnknownArity::new(vcx.alloc_slice(&args));
            let ret_tys = vcx.alloc_slice(&[local_defs.locals[mir::RETURN_PLACE].ty.snapshot]);
            let method_ref = MethodIdent::new(method_name, args, ret_tys);
            deps.emit_output_ref(
                task_key.clone(),
                PurifiedFunctionEncOutputRef { method_ref },
            )?;

            // Method contract. We will need to emit pre- and postconditions for
            // the functional spec, and (in the postcondition)
            // wands in case of a reborrowing function.
            let mut pres = Vec::new();
            let mut posts = Vec::new();
            let spec = deps.require_local::<PurifiedMirSpecEnc>((def_id, substs, None, false))?;
            let wands = deps.require_local::<PurifiedWandEnc>(PurifiedWandEncTask { def_id })?;

            // Add direct resources for inputs and outputs to the pre- and
            // postconditions, respectively. "Direct" here refers to owned
            // Viper resources that must be passed in/out given the signature,
            // without going through any dereferences.
            let mut args = Vec::with_capacity(arg_count + substs.len());
            for arg_idx in 1..arg_count {
                let arg = local_defs.locals[arg_idx.into()];
                let name_s = vir::vir_format_identifier!(vcx, "{}_param", arg.local.name).to_str();
                let type_s = arg.ty.snapshot;
                args.push(vcx.mk_local_decl(name_s, type_s));
                pres.push(Self::mk_conditions(
                    vcx, &mut deps, &task_key, &arg, arg_idx,
                ));
            }
            let mut rets = Vec::with_capacity(1);
            let ret = local_defs.locals[mir::RETURN_PLACE];
            let name_ret = ret.local.name;
            let type_ret = ret.ty.snapshot;
            rets.push(vcx.mk_local_decl(name_ret, type_ret));
            posts.push(Self::mk_conditions(
                vcx,
                &mut deps,
                &task_key,
                &ret,
                mir::RETURN_PLACE.into(),
            ));

            // ..
            // pres.extend(wands.indirect_pres(vcx, &local_defs, deps));
            // posts.extend(wands.indirect_posts(vcx, &local_defs, deps));
            // posts.extend(wands.wand_posts(vcx, &local_defs, deps));

            // Do not encode the method body if it is external, trusted, just
            // a call stub, or a trait function without a default implementation
            let local_def_id = def_id
                .as_local()
                .filter(|_| !trusted && is_function_with_body(vcx.tcx(), def_id));

            let blocks = if let Some(local_def_id) = local_def_id {
                let body = vcx
                    .body_mut()
                    .get_impure_fn_body(local_def_id, substs, caller_def_id);

                let body_with_facts = vcx.body_mut().get_impure_fn_body_with_facts(local_def_id);

                let loop_analysis = LoopAnalysis::find_loops(&body);
                let bc = BorrowCheckerImpl::new(vcx.tcx(), &body_with_facts);
                let fpcs_analysis =
                    pcg::run_pcg(&body_with_facts.body, vcx.tcx(), &bc, Global, None);

                let block_count = body.basic_blocks.len();

                let mut encoded_blocks = Vec::with_capacity(
                    // extra blocks: Start, End
                    2 + block_count,
                );
                let mut start_stmts = Vec::new();

                for local in 1..arg_count {
                    let name_s = local_defs.locals[local.into()].local.name;
                    let type_s = local_defs.locals[local.into()].ty.snapshot;
                    let expr = vcx.mk_local_ex(args[local - 1].name, args[local - 1].ty);
                    start_stmts.push(vcx.mk_local_decl_stmt(
                        vir::vir_local_decl! {vcx; [name_s] : [type_s]},
                        Some(expr),
                    ))
                }
                for local in (arg_count..body.local_decls.len()).map(mir::Local::from) {
                    let name_s = local_defs.locals[local].local.name;
                    let type_s = local_defs.locals[local].ty.snapshot;
                    start_stmts.push(vcx.mk_local_decl_stmt(
                        vir::vir_local_decl! { vcx; [name_s] : [type_s] },
                        None,
                    ))
                }
                if ENCODE_REACH_BB {
                    start_stmts.extend((0..block_count).map(|block| {
                        let name = vir::vir_format!(vcx, "_reach_bb{block}");
                        vcx.mk_local_decl_stmt(
                            vir::vir_local_decl! { vcx; [name] : Bool },
                            Some(vcx.mk_todo_expr("false")),
                        )
                    }));
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
                    monomorphize: MirPurifiedEnc::monomorphize(),
                    vcx,
                    deps,
                    def_id,
                    local_decls: &body.local_decls,
                    fpcs_analysis,
                    local_defs,
                    body: &body,

                    loop_analysis,
                    wands,

                    declared_vars: Default::default(),
                    place_to_local_data: Default::default(),

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
                visitor.visit_body(&body);
                start_stmts.extend(visitor.from_to_vars.iter().flat_map(|(_, v)| v.iter()).map(
                    |(_, v)| {
                        vcx.mk_local_decl_stmt(
                            vir::vir_local_decl! { vcx; [v] : Bool },
                            Some(vcx.mk_bool::<false>()),
                        )
                    },
                ));
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

            args.extend(param_ty_decls.iter());

            // Add functional specification as the last pre- and postconditions.
            pres.extend(spec.pres);
            posts.extend(spec.posts);

            Ok(PurifiedFunctionEncOutput {
                method: vcx.mk_method(
                    method_ref,
                    vcx.alloc_slice(&args),
                    vcx.alloc_slice(&rets),
                    vcx.alloc_slice(&pres),
                    vcx.alloc_slice(&posts),
                    blocks.map(|blocks| vcx.alloc_slice(&blocks)),
                ),
            })
        })
    }
}
