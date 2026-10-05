use std::{
    cell::{Cell, RefCell},
    collections::HashSet,
};

use rustc_hash::FxHasher;
use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies};
use tracing::Instrument;

use super::{TyUsePureEnc, ty::RustTyDecomposition};

/// The state encoder encodes the state representation used for interior-mutability reasoning

#[derive(Debug, Clone, Copy)]
pub struct ImStateEncRef<'vir> {
    pub next_idn: vir::FunctionIdn<'vir, vir::ImState, vir::ImState>,
    pub lte_idn: vir::FunctionIdn<'vir, (vir::ImState, vir::ImState), vir::Bool>,
    pub pred_idn: vir::PredicateIdn<'vir, vir::Ref>,
    pub get_idn: vir::FunctionIdn<'vir, vir::Ref, vir::ImState>,
    pub bump_idn: vir::MethodIdn<'vir, vir::Ref>,
}

impl<'vir> OutputRefAny for ImStateEncRef<'vir> {}

#[derive(Debug, Clone, Copy)]
pub struct ImStateEncResult<'vir> {
    domain: vir::Domain<'vir>,
    pred: vir::Predicate<'vir>,
    get: vir::Function<'vir>,
    bump: vir::Method<'vir>,
}

pub struct ImStateEnc;

// TODO should we emit impure

impl TaskEncoder for ImStateEnc {
    task_encoder::encoder_cache!(ImStateEnc);
    const ENCODER_NAME: &'static str = "interior mutability (common) state encoder";

    type TaskDescription<'vir> = ();
    type OutputRef<'vir> = ImStateEncRef<'vir>;
    type OutputFullLocal<'vir> = ImStateEncResult<'vir>;
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let mut functions = Vec::new();
            let mut axioms = Vec::new();

            let next_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("st_next"),
                vir::TYPE_IMSTATE,
                vir::TYPE_IMSTATE,
            );

            let lte_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("st_lte"),
                (vir::TYPE_IMSTATE, vir::TYPE_IMSTATE),
                vir::TYPE_BOOL,
            );

            let pred_idn = vir::PredicateIdn::new(vir::ViperIdent::new("p_ImState"), vir::TYPE_REF);

            let get_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("st_get"),
                vir::TYPE_REF,
                vir::TYPE_IMSTATE,
            );

            let bump_idn = vir::MethodIdn::new(vir::ViperIdent::new("st_bump"), vir::TYPE_REF);

            deps.emit_output_ref(*task_key, ImStateEncRef {
                next_idn,
                lte_idn,
                pred_idn,
                get_idn,
                bump_idn,
            })?;

            // Functions

            let next_fn = vcx.mk_domain_function(next_idn, false, None);
            functions.push(next_fn);

            let lte_fn = vcx.mk_domain_function(lte_idn, false, None);
            functions.push(lte_fn);

            // General Axioms

            let one = vcx.mk_int::<1>();
            let next_defn = vcx.mk_domain_axiom(vir::ViperIdent::new("next_defn"), vir::expr! {
                forall s: ImState :: { [next_idn](s) } (([next_idn](s)) as Int) == ((((s) as Int) + (one)) as Int)
            });
            axioms.push(next_defn);

            let lte_defn = vcx.mk_domain_axiom(vir::ViperIdent::new("lte_defn"), vir::expr! {
                forall s0: ImState, s1: ImState :: { ([lte_idn](s0, s1)) }
                ([lte_idn](s0, s1)) == (((s0) as Int) < ((s1) as Int))
            });
            axioms.push(lte_defn);

            // Domain

            let domain = vcx.mk_domain(
                vir::ViperIdent::new("st_common"),
                &[],
                vcx.alloc_slice(&axioms[..]),
                vcx.alloc_slice(&functions[..]),
                None,
            );

            // ImState permission

            let ref_local = vcx.mk_local_decl("rf", vir::TYPE_REF);
            let ref_expr = vcx.mk_local_ex(ref_local);
            let pred = vcx.mk_predicate(pred_idn, (ref_local,), None);

            let ref_local = vcx.mk_local_decl("rf", vir::TYPE_REF);
            let get = vcx.mk_function(
                get_idn,
                (ref_local,),
                vcx.alloc_slice(&[vcx.mk_predicate_app_expr((pred_idn)(ref_expr)(None))]),
                &[],
                None,
                None,
            );

            let bump = vcx.mk_method(
                bump_idn,
                (ref_local,),
                &[],
                vcx.alloc_slice(&[vcx.mk_predicate_app_expr((pred_idn)(ref_expr)(None))]),
                vcx.alloc_slice(&[
                    vcx.mk_predicate_app_expr((pred_idn)(ref_expr)(None)),
                    vcx.mk_eq_expr(
                        (get_idn).call()(ref_expr),
                        next_idn.call()(vcx.mk_old_expr(get_idn.call()(ref_expr))),
                    ),
                ]),
                None,
            );

            Ok((
                ImStateEncResult {
                    domain,
                    pred,
                    get,
                    bump,
                },
                (),
            ))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors(program) {
            program.add_domain(output.domain);
            program.add_predicate(output.pred);
            program.add_function(output.get);
            program.add_method(output.bump);
        }
    }
}

thread_local! {
   static TYPE_CTR: Cell<usize> = Cell::new(0);
}

pub fn inc_type_ctr() -> usize {
    TYPE_CTR.replace(TYPE_CTR.get() + 1)
}

pub struct ImTyNameEnc;

impl TaskEncoder for ImTyNameEnc {
    task_encoder::encoder_cache!(ImTyNameEnc);
    const ENCODER_NAME: &'static str = "interior mutability type name encoder";

    type TaskDescription<'vir> = RustTyDecomposition<'vir>;
    type OutputFullDependency<'vir> = String;
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        Ok((
            (),
            format!("ImTy{}__{}", inc_type_ctr(), task_key.ty.data.name()),
        ))
    }
}

pub struct ImTyStateEnc;

#[derive(Debug, Clone, Copy)]
pub struct ImTyStateEncResult<'vir> {
    domain: vir::Domain<'vir>,
}

#[derive(Debug, Clone, Copy)]
pub struct ImTyStateEncRef<'vir> {
    pub get_snap_idn: vir::FunctionIdn<'vir, (vir::ImState, vir::Ref), vir::Snap>,
    pub allocated_idn: vir::FunctionIdn<'vir, (vir::ImState, vir::Ref), vir::Bool>,
    pub fresh_idn: vir::FunctionIdn<'vir, (vir::ImState, vir::Ref), vir::Bool>,
    pub modifiable_idn: vir::FunctionIdn<'vir, (vir::ImState, vir::Ref), vir::Bool>,
    pub not_modified_idn: vir::FunctionIdn<'vir, (vir::ImState, vir::Ref), vir::Bool>,
}

impl<'vir> OutputRefAny for ImTyStateEncRef<'vir> {}

impl TaskEncoder for ImTyStateEnc {
    task_encoder::encoder_cache!(ImTyStateEnc);
    const ENCODER_NAME: &'static str = "interior mutability (per-type) state encoder";

    type TaskDescription<'vir> = RustTyDecomposition<'vir>;
    type OutputRef<'vir> = ImTyStateEncRef<'vir>;
    type OutputFullLocal<'vir> = ImTyStateEncResult<'vir>;
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let mut functions = Vec::new();
            let mut axioms = Vec::new();

            let snap_ty = deps.require_dep::<TyUsePureEnc>(*task_key)?;

            let ty_name = deps.require_dep::<ImTyNameEnc>(*task_key)?;

            let get_snap_idn = vir::FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "st_get_snap_{}", ty_name),
                (vir::TYPE_IMSTATE, vir::TYPE_REF),
                snap_ty.snapshot,
            );

            let allocated_idn = vir::FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "st_allocated_{}", ty_name),
                (vir::TYPE_IMSTATE, vir::TYPE_REF),
                vir::TYPE_BOOL,
            );

            let fresh_idn = vir::FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "st_fresh_{}", ty_name),
                (vir::TYPE_IMSTATE, vir::TYPE_REF),
                vir::TYPE_BOOL,
            );

            let modifiable_idn = vir::FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "st_modifiable_{}", ty_name),
                (vir::TYPE_IMSTATE, vir::TYPE_REF),
                vir::TYPE_BOOL,
            );

            let not_modified_idn = vir::FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "st_not_modified_{}", ty_name),
                (vir::TYPE_IMSTATE, vir::TYPE_REF),
                vir::TYPE_BOOL,
            );

            deps.emit_output_ref(*task_key, ImTyStateEncRef {
                get_snap_idn,
                allocated_idn,
                fresh_idn,
                modifiable_idn,
                not_modified_idn,
            })?;

            let get_snap_fn = vcx.mk_domain_function(get_snap_idn, false, None);
            functions.push(get_snap_fn);

            let allocated_fn = vcx.mk_domain_function(allocated_idn, false, None);
            functions.push(allocated_fn);

            let fresh_fn = vcx.mk_domain_function(fresh_idn, false, None);
            functions.push(fresh_fn);

            let modifiable_fn = vcx.mk_domain_function(modifiable_idn, false, None);
            functions.push(modifiable_fn);

            let not_modified_fn = vcx.mk_domain_function(not_modified_idn, false, None);
            functions.push(not_modified_fn);

            // Axioms

            let im_state = deps.require_ref::<ImStateEnc>(())?;

            // TODO do we also need a "forward" trigger?
            let allocated_next = vcx.mk_domain_axiom(
                vir::vir_format_identifier!(vcx, "allocated_next_{}", ty_name),
                vir::expr! {
                    forall s: ImState, l: Ref :: { ([allocated_idn](([im_state.next_idn](s)), l)) }
                    ([allocated_idn](s, l)) ==> ([allocated_idn](([im_state.next_idn](s)), l))
                },
            );
            axioms.push(allocated_next);

            let fresh_allocated = vcx.mk_domain_axiom(
                vir::vir_format_identifier!(vcx, "fresh_allocated_{}", ty_name),
                vir::expr! {
                    forall s: ImState, l: Ref :: { ([fresh_idn](s, l)), ([allocated_idn](s, l)) }
                    (([fresh_idn](s, l)) && ([allocated_idn](s, l))) ==> (false)
                },
            );
            axioms.push(fresh_allocated);

            let fresh_modifiable = vcx.mk_domain_axiom(
                vir::vir_format_identifier!(vcx, "fresh_modifiable_{}", ty_name),
                vir::expr! {
                    forall s: ImState, l: Ref ::
                    { ([fresh_idn](s, l)) }
                    ([fresh_idn](s, l)) ==> ([modifiable_idn](s, l))
                },
            );
            axioms.push(fresh_modifiable);

            let modifiable_next = vcx.mk_domain_axiom(
                vir::vir_format_identifier!(vcx, "modifiable_next_{}", ty_name),
                vir::expr! {
                    forall s: ImState, l: Ref ::
                    { ([modifiable_idn](([im_state.next_idn](s)), l)) }
                    ([modifiable_idn](s, l)) ==> ([modifiable_idn](([im_state.next_idn](s)), l))
                },
            );
            axioms.push(modifiable_next);

            let domain = vcx.mk_domain(
                vir::vir_format_identifier!(vcx, "st__{}", ty_name),
                &[],
                vcx.alloc_slice(&axioms[..]),
                vcx.alloc_slice(&functions[..]),
                None,
            );
            Ok((ImTyStateEncResult { domain }, ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors(program) {
            program.add_domain(output.domain);
        }
    }
}
