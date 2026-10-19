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
    pub havocked_idn: vir::FunctionIdn<'vir, (vir::ImState, vir::ImState), vir::Bool>,
    pub lte_idn: vir::FunctionIdn<'vir, (vir::ImState, vir::ImState), vir::Bool>,

    pub get_snap_idn: vir::FunctionIdn<'vir, (vir::TyVal, vir::ImState, vir::Ref), vir::PSnap>,
    pub allocated_idn: vir::FunctionIdn<'vir, (vir::TyVal, vir::ImState, vir::Ref), vir::Bool>,
    pub fresh_idn: vir::FunctionIdn<'vir, (vir::TyVal, vir::ImState, vir::Ref), vir::Bool>,
    pub modifiable_idn: vir::FunctionIdn<'vir, vir::ImState, vir::Set>,
    pub modifies_idn: vir::FunctionIdn<'vir, vir::ImState, vir::Set>,

    pub mk_rep_idn: vir::FunctionIdn<'vir, (vir::ImState, vir::Ref, vir::PSnap), vir::GRep>,
    pub rep_eq_idn: vir::FunctionIdn<'vir, (vir::TyVal, vir::GRep, vir::GRep), vir::Bool>,

    pub addr_from_psnap_idn: vir::FunctionIdn<'vir, vir::PSnap, vir::Ref>,
    pub ty_from_psnap_idn: vir::FunctionIdn<'vir, vir::PSnap, vir::TyVal>,
    pub mk_aloc_psnap_idn: vir::FunctionIdn<'vir, (vir::TyVal, vir::Ref), vir::PSnap>,

    pub get_idn: vir::FunctionIdn<'vir, vir::Ref, vir::ImState>,
    pub pred_idn: vir::PredicateIdn<'vir, vir::Ref>,
    pub bump_idn: vir::MethodIdn<'vir, vir::Ref>,

    pub state_ref_decl: vir::LocalDecl<'vir, vir::Ref>,
    pub state_decl: vir::LocalDecl<'vir, vir::ImState>,
}

impl<'vir> OutputRefAny for ImStateEncRef<'vir> {}

#[derive(Debug, Clone, Copy)]
pub struct ImStateEncResult<'vir> {
    domain: vir::Domain<'vir>,
    get: vir::Function<'vir>,
    pred: vir::Predicate<'vir>,
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
            let mut domain_functions = Vec::new();
            let mut axioms = Vec::new();

            let next_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("im_next"),
                vir::TYPE_IMSTATE,
                vir::TYPE_IMSTATE,
            );

            let havocked_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("im_havocked"),
                (vir::TYPE_IMSTATE, vir::TYPE_IMSTATE),
                vir::TYPE_BOOL,
            );

            let get_snap_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("im_get_snap"),
                (vir::TYPE_TYVAL, vir::TYPE_IMSTATE, vir::TYPE_REF),
                vir::TYPE_PSNAP,
            );

            let allocated_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("im_allocated"),
                (vir::TYPE_TYVAL, vir::TYPE_IMSTATE, vir::TYPE_REF),
                vir::TYPE_BOOL,
            );

            let fresh_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("im_fresh"),
                (vir::TYPE_TYVAL, vir::TYPE_IMSTATE, vir::TYPE_REF),
                vir::TYPE_BOOL,
            );


            let modifiable_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("im_modifiable"),
                vir::TYPE_IMSTATE,
                vcx.mk_ty_set(vir::TYPE_PSNAP),
            );

            let modifies_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("im_modifies"),
                vir::TYPE_IMSTATE,
                vcx.mk_ty_set(vir::TYPE_PSNAP),
            );

            let lte_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("im_lte"),
                (vir::TYPE_IMSTATE, vir::TYPE_IMSTATE),
                vir::TYPE_BOOL,
            );

            let mk_rep_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("im_mk_rep"),
                (vir::TYPE_IMSTATE, vir::TYPE_REF, vir::TYPE_PSNAP),
                vir::TYPE_GREP,
            );

            let rep_eq_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("im_rep_eq"),
                (vir::TYPE_TYVAL, vir::TYPE_GREP, vir::TYPE_GREP),
                vir::TYPE_BOOL,
            );

            // This is a bit of a hack to be able to encode modifies-clauses without
            // having access to the ALoc type. When the ALoc type is encoded, we
            // emit an axiom that relates these functions to the ADT destructors.

            let mk_aloc_psnap_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("im_mk_aloc_psnap"),
                (vir::TYPE_TYVAL, vir::TYPE_REF),
                vir::TYPE_PSNAP,
            );

            let addr_from_psnap_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("im_addr_from_psnap"),
                vir::TYPE_PSNAP,
                vir::TYPE_REF,
            );

            let ty_from_psnap_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("im_ty_from_psnap"),
                vir::TYPE_PSNAP,
                vir::TYPE_TYVAL,
            );

            // Impure Ops

            let get_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("im_get"),
                vir::TYPE_REF,
                vir::TYPE_IMSTATE,
            );

            let pred_idn = vir::PredicateIdn::new(vir::ViperIdent::new("p_ImState"), vir::TYPE_REF);

            let bump_idn = vir::MethodIdn::new(vir::ViperIdent::new("im_bump"), vir::TYPE_REF);

            let state_ref_decl = vcx.mk_local_decl("im_state_ref", vir::TYPE_REF);

            let state_decl = vcx.mk_local_decl("im_state_ref", vir::TYPE_IMSTATE);

            deps.emit_output_ref(*task_key, ImStateEncRef {
                next_idn,
                lte_idn,
                havocked_idn,
                get_snap_idn,
                allocated_idn,
                fresh_idn,
                modifiable_idn,
                modifies_idn,
                mk_rep_idn,
                rep_eq_idn,
                get_idn,
                pred_idn,
                bump_idn,
                addr_from_psnap_idn,
                ty_from_psnap_idn,
                mk_aloc_psnap_idn,
                state_ref_decl,
                state_decl,
            })?;

            // Domain Functions

            domain_functions.push(vcx.mk_domain_function(next_idn, false, None));
            domain_functions.push(vcx.mk_domain_function(lte_idn, false, None));
            domain_functions.push(vcx.mk_domain_function(havocked_idn, false, None));
            domain_functions.push(vcx.mk_domain_function(get_snap_idn, false, None));
            domain_functions.push(vcx.mk_domain_function(allocated_idn, false, None));
            domain_functions.push(vcx.mk_domain_function(fresh_idn, false, None));
            domain_functions.push(vcx.mk_domain_function(modifiable_idn, false, None));
            domain_functions.push(vcx.mk_domain_function(modifies_idn, false, None));
            domain_functions.push(vcx.mk_domain_function(mk_rep_idn, false, None));
            domain_functions.push(vcx.mk_domain_function(rep_eq_idn, false, None));
            domain_functions.push(vcx.mk_domain_function(addr_from_psnap_idn, false, None));
            domain_functions.push(vcx.mk_domain_function(ty_from_psnap_idn, false, None));
            domain_functions.push(vcx.mk_domain_function(mk_aloc_psnap_idn, false, None));

            // General Axioms

            let one = vcx.mk_int::<1>();
            let next_defn = vcx.mk_domain_axiom(vir::ViperIdent::new("im_next_defn"), vir::expr! {
                forall s: ImState :: { [next_idn](s) } (([next_idn](s)) as Int) == ((((s) as Int) + (one)) as Int)
            });
            axioms.push(next_defn);

            let lte_defn = vcx.mk_domain_axiom(vir::ViperIdent::new("im_lte_defn"), vir::expr! {
                forall s0: ImState, s1: ImState :: { ([lte_idn](s0, s1)) }
                ([lte_idn](s0, s1)) == (((s0) as Int) < ((s1) as Int))
            });
            axioms.push(lte_defn);

            let allocated_next = vcx.mk_domain_axiom(
                vir::ViperIdent::new("im_allocated_next"),
                vir::expr! {
                    forall t: Type, s: ImState, l: Ref :: { ([allocated_idn](t, ([next_idn](s)), l)) }
                    ([allocated_idn](t, s, l)) ==> ([allocated_idn](t, ([next_idn](s)), l))
                },
            );
            axioms.push(allocated_next);

            let fresh_allocated = vcx.mk_domain_axiom(
                vir::ViperIdent::new("im_fresh_allocated"),
                vir::expr! {
                    forall t: Type, s: ImState, l: Ref :: { ([fresh_idn](t, s, l)), ([allocated_idn](t, s, l)) }
                    (([fresh_idn](t, s, l)) && ([allocated_idn](t, s, l))) ==> (false)
                },
            );
            axioms.push(fresh_allocated);

            let fresh_modifiable =
                vcx.mk_domain_axiom(vir::ViperIdent::new("im_fresh_modifiable"), vir::expr! {
                    forall t: Type, s: ImState, l: Ref ::
                    { ([fresh_idn](t, s, l)) }
                    ([fresh_idn](t, s, l)) ==> (([mk_aloc_psnap_idn](t, l)) in  ([modifiable_idn](s)))
                });
            axioms.push(fresh_modifiable);

            let modifiable_next =
                vcx.mk_domain_axiom(vir::ViperIdent::new("im_modifiable_next"), vir::expr! {
                    forall s: ImState ::
                    { ([modifiable_idn](([next_idn](s)))) }
                    ([modifiable_idn](s)) subset ([modifiable_idn](([next_idn](s))))
                });
            axioms.push(modifiable_next);

            let rep_eq_refl =
                vcx.mk_domain_axiom(vir::ViperIdent::new("im_rep_eq_refl"), vir::expr! {
                    forall
                        t: Type,
                        r: GRep ::
                    { ([rep_eq_idn](t, r, r)) }
                    [rep_eq_idn](t, r, r)
                });
            axioms.push(rep_eq_refl);

            let rep_eq_sym =
                vcx.mk_domain_axiom(vir::ViperIdent::new("im_rep_eq_sym"), vir::expr! {
                    forall
                        t: Type,
                        r0: GRep,
                        r1: GRep ::
                    { ([rep_eq_idn](t, r0, r1)) }
                    ([rep_eq_idn](t, r0, r1)) ==> ([rep_eq_idn](t, r1, r0))
                });
            axioms.push(rep_eq_sym);

            let rep_eq_trans = vcx.mk_domain_axiom(
                vir::ViperIdent::new("im_rep_eq_trans"),
                vir::expr! {
                    forall
                        t: Type,
                        r0: GRep,
                        r1: GRep,
                        r2: GRep ::
                    { ([rep_eq_idn](t, r0, r1)), ([rep_eq_idn](t, r1, r2)) }
                    (([rep_eq_idn](t, r0, r1)) && ([rep_eq_idn](t, r1, r2))) ==> ([rep_eq_idn](t, r0, r2))
                },
            );
            axioms.push(rep_eq_trans);

            let rep_eq_snap =
                vcx.mk_domain_axiom(vir::ViperIdent::new("im_rep_snap_eq"), vir::expr! {
                    forall
                        t: Type,
                        st0: ImState,
                        st1: ImState,
                        l0: Ref,
                        l1: Ref,
                        s0: PSnap,
                        s1: PSnap ::
                    { ([rep_eq_idn](t, ([mk_rep_idn](st0, l0, s0)), ([mk_rep_idn](st1, l1, s1)))) }
                    ([rep_eq_idn](t, ([mk_rep_idn](st0, l0, s0)), ([mk_rep_idn](st1, l1, s1))))
                            ==> ((s0) == (s1))
                });
            axioms.push(rep_eq_snap);

            // Domain

            let domain = vcx.mk_domain(
                vir::ViperIdent::new("im_state"),
                &[],
                vcx.alloc_slice(&axioms[..]),
                vcx.alloc_slice(&domain_functions[..]),
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
                    // TODO do we always want to consider the next state to be havocked from the current one?
                    havocked_idn.call()(
                        vcx.mk_old_expr(get_idn.call()(ref_expr)),
                        get_idn.call()(ref_expr),
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
            program.add_method(output.bump);
            program.add_function(output.get);
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
