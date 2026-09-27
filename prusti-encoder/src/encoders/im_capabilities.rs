use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies};

use super::ImStateEnc;

#[derive(Debug, Clone, Copy)]
pub struct ImCapEncRef<'vir> {
    pub mutable_idn:
        vir::FunctionIdn<'vir, (vir::ImState, vir::Int, vir::TyVal, vir::Ref), vir::Bool>,
    pub immutable_idn:
        vir::FunctionIdn<'vir, (vir::ImState, vir::Int, vir::TyVal, vir::Ref), vir::Bool>,
    // TODO figure out type-refined versions of these:
    pub local_mutable_idn: vir::FunctionIdn<
        'vir,
        (vir::ImState, vir::Int, vir::TyVal, vir::Ref, vir::TyVal, vir::Ref),
        vir::Bool,
    >,
    pub atomic_mutable_idn: vir::FunctionIdn<
        'vir,
        (vir::ImState, vir::Int, vir::TyVal, vir::Ref, vir::TyVal, vir::Ref),
        vir::Bool,
    >,
    pub addr_to_idx_idn: vir::FunctionIdn<'vir, (vir::TyVal, vir::Ref), vir::Int>,
}

impl<'vir> OutputRefAny for ImCapEncRef<'vir> {}

#[derive(Debug, Clone, Copy)]
pub struct ImCapEncResult<'vir> {
    domain: vir::Domain<'vir>,
}

pub struct ImCapEnc;

impl TaskEncoder for ImCapEnc {
    task_encoder::encoder_cache!(ImCapEnc);
    const ENCODER_NAME: &'static str = "interior mutability state encoder";

    type TaskDescription<'vir> = ();
    type OutputRef<'vir> = ImCapEncRef<'vir>;
    type OutputFullLocal<'vir> = ImCapEncResult<'vir>;
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let im_state = deps.require_ref::<ImStateEnc>(())?;

        vir::with_vcx(|vcx| {
            let mut functions = Vec::new();
            let mut axioms = Vec::new();

            let mutable_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("cap_mutable"),
                (
                    vir::TYPE_IMSTATE,
                    vir::TYPE_INT,
                    vir::TYPE_TYVAL,
                    vir::TYPE_REF,
                ),
                vir::TYPE_BOOL,
            );

            let immutable_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("cap_immutable"),
                (
                    vir::TYPE_IMSTATE,
                    vir::TYPE_INT,
                    vir::TYPE_TYVAL,
                    vir::TYPE_REF,
                ),
                vir::TYPE_BOOL,
            );

            let local_mutable_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("cap_local"),
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

            let atomic_mutable_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("cap_atomic"),
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

            let addr_to_idx_idn = vir::FunctionIdn::new(
                vir::ViperIdent::new("cap_addr_to_idx"),
                (vir::TYPE_TYVAL, vir::TYPE_REF),
                vir::TYPE_INT,
            );

            deps.emit_output_ref(*task_key, ImCapEncRef {
                mutable_idn,
                immutable_idn,
                local_mutable_idn,
                atomic_mutable_idn,
                addr_to_idx_idn,
            })?;

            // Addr to index conversion for local capabilities

            functions.push(vcx.mk_domain_function(addr_to_idx_idn, false, None));

            let zero = vcx.mk_int::<0>();
            let addr_to_idx_neg =
                vcx.mk_domain_axiom(vir::ViperIdent::new("addr_to_idx_neg"), vir::expr! {
                    forall t: Type, l: Ref ::
                    { [addr_to_idx_idn](t, l) }
                    ([addr_to_idx_idn](t, l)) < (zero)
                });
            axioms.push(addr_to_idx_neg);

            let addr_to_idx_bi =
                vcx.mk_domain_axiom(vir::ViperIdent::new("addr_to_idx_bi"), vir::expr! {
                    forall t0: Type, t1: Type, l0: Ref, l1: Ref ::
                    { ([addr_to_idx_idn](t0, l0)), ([addr_to_idx_idn](t1, l1)) }
                    (([addr_to_idx_idn](t0, l0)) == ([addr_to_idx_idn](t1, l1))) == (((t0) == (t1)) && ((l0) == (l1)))
                });
            axioms.push(addr_to_idx_bi);

            // Capabilities

            functions.push(vcx.mk_domain_function(mutable_idn, false, None));
            functions.push(vcx.mk_domain_function(immutable_idn, false, None));
            functions.push(vcx.mk_domain_function(local_mutable_idn, false, None));
            functions.push(vcx.mk_domain_function(atomic_mutable_idn, false, None));

            // Capability Implications

            let mutable_immutable =
                vcx.mk_domain_axiom(vir::ViperIdent::new("mutable_immutable"), vir::expr! {
                    forall t: Type, s: ImState, l: Ref, i: Int ::
                    { ([mutable_idn](s, i, t, l)) }
                    ([mutable_idn](s, i, t, l)) ==> ([immutable_idn](s, i, t, l))
                });
            axioms.push(mutable_immutable);

            // local-capabilities are fully available when the address specified in `local` is not
            // modified and modifiable
            let local_mutable_full =
                vcx.mk_domain_axiom(vir::ViperIdent::new("local_mutable_full"), vir::expr! {
                    forall s: ImState, t0: Type, t1: Type, l0: Ref, l1: Ref, i: Int ::
                    { ([local_mutable_idn](s, i, t0, l0, t1, l1))  }
                    (([local_mutable_idn](s, i, t0, l0, t1, l1)) &&
                     (([im_state.modifiable_idn](s, t0, l0)) &&
                      ([im_state.not_modified_idn](s, t0, l0)))) ==>
                        ([mutable_idn](s, ([addr_to_idx_idn](t0, l0)), t1, l1))
                });
            axioms.push(local_mutable_full);

            // local-mutable is at least as strong as immutable when `local` is not modified
            let local_mutable_partial =
                vcx.mk_domain_axiom(vir::ViperIdent::new("local_mutable_partial"), vir::expr! {
                    forall s: ImState, t0: Type, t1: Type, l0: Ref, l1: Ref, i: Int ::
                    { ([local_mutable_idn](s, i, t0, l0, t1, l1))  }
                    (([local_mutable_idn](s, i, t0, l0, t1, l1)) &&
                        ([im_state.not_modified_idn](s, t0, l0))) ==>
                        ([immutable_idn](s, ([addr_to_idx_idn](t0, l0)), t1, l1))
                });
            axioms.push(local_mutable_partial);

            // local-immutable is at least as strong as immutable when `local` is not modified
            // let local_immutable_partial = vcx.mk_domain_axiom(
            //     vir::ViperIdent::new("local_immutable_partial"),
            //     vir::expr! {
            //         forall s: ImState, t0: Type, t1: Type, l0: Ref, l1: Ref, i: Int ::
            //         { ([in_state_idn](s, i, ([local_idn](t0, l0, ([immutable_idn](t1, l1))))))  }
            //         (([in_state_idn](s, i, ([local_idn](t0, l0, ([immutable_idn](t1, l1)))))) &&
            //             ([im_state.not_modified_idn](s, t0, l0))) ==>
            //             ([in_state_idn](s, ([addr_to_idx_idn](t0, l0)), ([immutable_idn](t1, l1))))
            //     },
            // );
            // axioms.push(local_immutable_partial);

            // Two-State Axioms

            let immutable_stable =
                vcx.mk_domain_axiom(vir::ViperIdent::new("immutable_stable"), vir::expr! {
                    forall t: Type, s: ImState, l: Ref, i: Int ::
                    { ([immutable_idn](s, i, t, l)) }
                    ([immutable_idn](s, i, t, l)) ==>
                        (([im_state.get_snap_idn](s, t, l)) == ([im_state.get_snap_idn](([im_state.next_idn](s)), t, l)))
                });
            axioms.push(immutable_stable);

            let mutable_moved =
                vcx.mk_domain_axiom(vir::ViperIdent::new("mutable_moved"), vir::expr! {
                    forall t: Type, s: ImState, l: Ref, i: Int ::
                    { ([mutable_idn](s, i, t, l)) }
                    ([mutable_idn](s, i, t, l)) ==>
                        ([im_state.moved_idn](t, s, l, ([im_state.next_idn](s)), l))
                });
            axioms.push(mutable_moved);

            let mutable_modifiable =
                vcx.mk_domain_axiom(vir::ViperIdent::new("mutable_modifiable"), vir::expr! {
                        forall t: Type, s: ImState, l: Ref, i: Int ::
                        { ([mutable_idn](s, i, t, l)) }
                        ([mutable_idn](s, i, t, l)) ==>
                            ([im_state.modifiable_idn](s, t, l))
                });
            axioms.push(mutable_modifiable);

            // Domain
            let domain = vcx.mk_domain(
                vir::ViperIdent::new("ImCap"),
                &[],
                vcx.alloc_slice(&axioms[..]),
                vcx.alloc_slice(&functions[..]),
                None,
            );
            Ok((ImCapEncResult { domain }, ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors(program) {
            program.add_domain(output.domain);
        }
    }
}
