use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies};

/// The state encoder encodes the state representation used for interior-mutability reasoning

#[derive(Debug, Clone, Copy)]
pub struct ImStateEncRef<'vir> {
    capabilities: CapabilityRef<'vir>,
    get_snap_idn: vir::FunctionIdn<'vir, (vir::ImState, vir::TyVal, vir::Ref), vir::PSnap>,
    next_idn: vir::FunctionIdn<'vir, vir::ImState, vir::ImState>,
    lte_idn: vir::FunctionIdn<'vir, (vir::ImState, vir::ImState), vir::Bool>,
    allocated_idn: vir::FunctionIdn<'vir, (vir::ImState, vir::TyVal, vir::Ref), vir::Bool>,
    fresh_idn: vir::FunctionIdn<'vir, (vir::ImState, vir::TyVal, vir::Ref), vir::Bool>,
    moved_idn: vir::FunctionIdn<
        'vir,
        (vir::TyVal, vir::ImState, vir::Ref, vir::ImState, vir::Ref),
        vir::Bool,
    >,
    modifiable_idn: vir::FunctionIdn<'vir, (vir::ImState, vir::TyVal, vir::Ref), vir::Bool>,
    not_modified_idn: vir::FunctionIdn<'vir, (vir::ImState, vir::TyVal, vir::Ref), vir::Bool>,
}

// TODO should e.g. modified go here as well so we can e.g. conditionally get exclusive from local?
// what about the modifies-set of a method? Also tracked here?

#[derive(Debug, Clone, Copy)]
pub struct CapabilityRef<'vir> {
    exclusive_idn:
        vir::FunctionIdn<'vir, (vir::ImState, vir::Int, vir::TyVal, vir::Ref), vir::Bool>,
    shared_idn: vir::FunctionIdn<'vir, (vir::ImState, vir::Int, vir::TyVal, vir::Ref), vir::Bool>,
    // First (Type, Ref) pair is the address/type which the second (Type, Ref) pair is shared under.
    local_exclusive_idn: vir::FunctionIdn<
        'vir,
        (
            vir::ImState,
            vir::Int,
            vir::TyVal,
            vir::Ref,
            vir::TyVal,
            vir::Ref,
        ),
        vir::Bool,
    >,
    // Without invariants, the first (Type, Ref) pair doesn't do anything, but might be used in future.
    atomic_exclusive_idn: vir::FunctionIdn<
        'vir,
        (
            vir::ImState,
            vir::Int,
            vir::TyVal,
            vir::Ref,
            vir::TyVal,
            vir::Ref,
        ),
        vir::Bool,
    >,
}

impl<'vir> OutputRefAny for ImStateEncRef<'vir> {}

#[derive(Debug, Clone, Copy)]
pub struct ImStateEncResult<'vir> {
    domain: vir::Domain<'vir>,
}

pub struct ImStateEnc;

impl TaskEncoder for ImStateEnc {
    task_encoder::encoder_cache!(ImStateEnc);
    const ENCODER_NAME: &'static str = "interior mutability state encoder";

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

            let exclusive_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("st_exclusive"),
                (
                    vir::TYPE_IMSTATE,
                    vir::TYPE_INT,
                    vir::TYPE_TYVAL,
                    vir::TYPE_REF,
                ),
                vir::TYPE_BOOL,
            );

            let shared_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("st_shared"),
                (
                    vir::TYPE_IMSTATE,
                    vir::TYPE_INT,
                    vir::TYPE_TYVAL,
                    vir::TYPE_REF,
                ),
                vir::TYPE_BOOL,
            );

            let local_exclusive_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("st_local_exclusive"),
                (
                    vir::TYPE_IMSTATE,
                    vir::TYPE_INT,
                    vir::TYPE_TYVAL,
                    vir::TYPE_REF,
                    vir::TYPE_TYVAL,
                    vir::TYPE_REF,
                ),
                vir::TYPE_BOOL,
            );

            let atomic_exclusive_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("st_atomic_exclusive"),
                (
                    vir::TYPE_IMSTATE,
                    vir::TYPE_INT,
                    vir::TYPE_TYVAL,
                    vir::TYPE_REF,
                    vir::TYPE_TYVAL,
                    vir::TYPE_REF,
                ),
                vir::TYPE_BOOL,
            );

            let capabilities = CapabilityRef {
                exclusive_idn,
                shared_idn,
                local_exclusive_idn,
                atomic_exclusive_idn,
            };

            let get_snap_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("st_get_snap"),
                (vir::TYPE_IMSTATE, vir::TYPE_TYVAL, vir::TYPE_REF),
                vir::TYPE_PSNAP,
            );

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

            let allocated_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("st_allocated"),
                (vir::TYPE_IMSTATE, vir::TYPE_TYVAL, vir::TYPE_REF),
                vir::TYPE_BOOL,
            );

            let fresh_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("st_fresh"),
                (vir::TYPE_IMSTATE, vir::TYPE_TYVAL, vir::TYPE_REF),
                vir::TYPE_BOOL,
            );

            let moved_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("st_moved"),
                (
                    vir::TYPE_TYVAL,
                    vir::TYPE_IMSTATE,
                    vir::TYPE_REF,
                    vir::TYPE_IMSTATE,
                    vir::TYPE_REF,
                ),
                vir::TYPE_BOOL,
            );

            let modifiable_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("st_modifiable"),
                (vir::TYPE_IMSTATE, vir::TYPE_TYVAL, vir::TYPE_REF),
                vir::TYPE_BOOL,
            );

            let not_modified_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("st_not_modified"),
                (vir::TYPE_IMSTATE, vir::TYPE_TYVAL, vir::TYPE_REF),
                vir::TYPE_BOOL,
            );

            deps.emit_output_ref(*task_key, ImStateEncRef {
                capabilities,
                get_snap_idn,
                next_idn,
                lte_idn,
                allocated_idn,
                fresh_idn,
                moved_idn,
                modifiable_idn,
                not_modified_idn,
            });

            // Capabilities

            let exclusive_fn = vcx.mk_domain_function(exclusive_idn, false, None);
            functions.push(exclusive_fn);

            let shared_fn = vcx.mk_domain_function(shared_idn, false, None);
            functions.push(shared_fn);

            let local_exclusive_fn = vcx.mk_domain_function(local_exclusive_idn, false, None);
            functions.push(local_exclusive_fn);

            let atomic_exclusive_fn = vcx.mk_domain_function(atomic_exclusive_idn, false, None);
            functions.push(atomic_exclusive_fn);

            // Functions

            let get_snap_fn = vcx.mk_domain_function(get_snap_idn, false, None);
            functions.push(get_snap_fn);

            let next_fn = vcx.mk_domain_function(next_idn, false, None);
            functions.push(next_fn);

            let lte_fn = vcx.mk_domain_function(lte_idn, false, None);
            functions.push(lte_fn);

            let allocated_fn = vcx.mk_domain_function(allocated_idn, false, None);
            functions.push(allocated_fn);

            let fresh_fn = vcx.mk_domain_function(fresh_idn, false, None);
            functions.push(fresh_fn);

            let moved_fn = vcx.mk_domain_function(moved_idn, false, None);
            functions.push(moved_fn);

            let modifiable_fn = vcx.mk_domain_function(modifiable_idn, false, None);
            functions.push(modifiable_fn);

            let not_modified_fn = vcx.mk_domain_function(not_modified_idn, false, None);
            functions.push(not_modified_fn);

            // General Axioms

            let next_lte = vcx.mk_domain_axiom(vir::ViperIdent::new("next_lte"), vir::expr! {
                forall s: ImState :: { [next_idn](s) } [lte_idn](s, ([next_idn](s)))
            });
            axioms.push(next_lte);

            let lte_trans = vcx.mk_domain_axiom(vir::ViperIdent::new("lte_trans"), vir::expr!{
                forall s0: ImState, s1: ImState, s2: ImState :: { ([lte_idn](s0, s1)), ([lte_idn](s1, s2)) }
                (([lte_idn](s0, s1)) && ([lte_idn](s1, s2))) ==> ([lte_idn](s0, s2))
            });
            axioms.push(lte_trans);

            let lte_refl = vcx.mk_domain_axiom(vir::ViperIdent::new("lte_refl"), vir::expr! {
                forall s0: ImState :: { [lte_idn](s0, s0) } [lte_idn](s0, s0)
            });
            axioms.push(lte_refl);

            // Triggers here search "backwards"
            // TODO do we also need a "forward" trigger?
            let allocated_lte = vcx.mk_domain_axiom(vir::ViperIdent::new("allocated_lte"), vir::expr!{
                forall s0: ImState, s1: ImState, t: Type, l: Ref :: { ([lte_idn](s0, s1)), ([allocated_idn](s1, t, l)) }
                (([allocated_idn](s0, t, l)) && ([lte_idn](s0, s1))) ==> ([allocated_idn](s1, t, l))
            });
            axioms.push(allocated_lte);

            let fresh_allocated =
                vcx.mk_domain_axiom(vir::ViperIdent::new("fresh_allocated"), vir::expr! {
                    forall s: ImState, t: Type, l: Ref :: { ([fresh_idn](s, t, l)), ([allocated_idn](s, t, l)) }
                    (([fresh_idn](s, t, l)) && ([allocated_idn](s, t, l))) ==> (false)
                });
            axioms.push(fresh_allocated);

            let moved_trans = vcx.mk_domain_axiom(vir::ViperIdent::new("moved_trans"), vir::expr!{
                forall t: Type, s0: ImState, s1: ImState, s2: ImState, l0: Ref, l1: Ref, l2: Ref ::
                { ([moved_idn](t, s0, l0, s1, l1)), ([moved_idn](t, s1, l1, s2, l2)) }
                (([moved_idn](t, s0, l0, s1, l1)) && ([moved_idn](t, s1, l1, s2, l2))) ==> ([moved_idn](t, s0, l0, s2, l2))
            });
            axioms.push(moved_trans);

            let moved_eq = vcx.mk_domain_axiom(vir::ViperIdent::new("moved_eq"), vir::expr!{
                forall t: Type, s0: ImState, s1: ImState, l0: Ref, l1: Ref ::
                { ([moved_idn](t, s0, l0, s1, l1)) }
                ([moved_idn](t, s0, l0, s1, l1)) ==> (([get_snap_idn](s0, t, l0)) == ([get_snap_idn](s1, t, l1)))
            });
            axioms.push(moved_eq);

            let fresh_modifiable =
                vcx.mk_domain_axiom(vir::ViperIdent::new("fresh_modifiable"), vir::expr! {
                    forall t: Type, s: ImState, l: Ref ::
                    { ([fresh_idn](s, t, l)) }
                    ([fresh_idn](s, t, l)) ==> ([modifiable_idn](s, t, l))
                });
            axioms.push(fresh_modifiable);

            let modifiable_lte =
                vcx.mk_domain_axiom(vir::ViperIdent::new("modifiable_lte"), vir::expr! {
                    forall t: Type, s: ImState, l: Ref, i: Int ::
                    { ([exclusive_idn](s, i, t, l)) }
                    ([exclusive_idn](s, i, t, l)) ==> ([shared_idn](s, i, t, l))
                });
            axioms.push(modifiable_lte);

            // Capability Implications

            let exclusive_shared =
                vcx.mk_domain_axiom(vir::ViperIdent::new("exclusive_shared"), vir::expr! {
                    forall t: Type, s: ImState, l: Ref, i: Int ::
                    { ([exclusive_idn](s, i, t, l)) }
                    ([exclusive_idn](s, i, t, l)) ==> ([shared_idn](s, i, t, l))
                });
            axioms.push(exclusive_shared);

            let local_exclusive_exclusive = vcx.mk_domain_axiom(vir::ViperIdent::new("local_exclusive_exclusive"), vir::expr!{
                forall s: ImState, tb: Type, t: Type, lb: Ref, l: Ref, i: Int ::
                { ([local_exclusive_idn](s, i, tb, lb, t, l)) }
                (([local_exclusive_idn](s, i, tb, lb, t, l)) &&
                 (([not_modified_idn](s, t, l)) &&
                  ([modifiable_idn](s, t, l)))) ==> ([exclusive_idn](s, i, t, l))
            });
            axioms.push(local_exclusive_exclusive);

            let local_exclusive_shared =
                vcx.mk_domain_axiom(vir::ViperIdent::new("local_exclusive_shared"), vir::expr! {
                    forall s: ImState, tb: Type, t: Type, lb: Ref, l: Ref, i: Int ::
                    { ([local_exclusive_idn](s, i, tb, lb, t, l)) }
                    (([local_exclusive_idn](s, i, tb, lb, t, l)) &&
                     ([not_modified_idn](s, t, l))) ==> ([shared_idn](s, i, t, l))
                });
            axioms.push(local_exclusive_shared);

            let exclusive_modifiable =
                vcx.mk_domain_axiom(vir::ViperIdent::new("exclusive_modifiable"), vir::expr! {
                    forall t: Type, s: ImState, l: Ref, i: Int ::
                    { ([exclusive_idn](s, i, t, l)) }
                    ([exclusive_idn](s, i, t, l)) ==> ([modifiable_idn](s, t, l))
                });
            axioms.push(exclusive_modifiable);

            // Two-State Axioms

            let shared_stable = vcx.mk_domain_axiom(vir::ViperIdent::new("shared_stable"), vir::expr!{
                forall t: Type, s: ImState, l: Ref, i: Int ::
                { ([shared_idn](s, i, t, l)) /* , (([get_snap_idn](([next_idn](s)), t, l)) as Dyn) */ }
                ([shared_idn](s, i, t, l)) ==> (([get_snap_idn](s, t, l)) == ([get_snap_idn](([next_idn](s)), t, l)))
            });
            axioms.push(shared_stable);

            let exclusive_moved =
                vcx.mk_domain_axiom(vir::ViperIdent::new("exclusive_moved"), vir::expr! {
                    forall t: Type, s: ImState, l: Ref, i: Int ::
                    { ([exclusive_idn](s, i, t, l)) }
                    ([exclusive_idn](s, i, t, l)) ==> ([moved_idn](t, s, l, ([next_idn](s)), l))
                });
            axioms.push(exclusive_moved);

            // Domain

            let domain = vcx.mk_domain(
                vir::ViperIdent::new("ImState"),
                &[],
                vcx.alloc_slice(&axioms[..]),
                vcx.alloc_slice(&functions[..]),
                None,
            );
            Ok((ImStateEncResult { domain }, ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors(program) {
            program.add_domain(output.domain);
        }
    }
}
