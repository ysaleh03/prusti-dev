use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies};

use super::{ty::RustTyDecomposition, ImStateEnc, ImTyEnc, ImTyNameEnc, ImTyStateEnc};

#[derive(Debug, Clone, Copy)]
pub struct ImCapEncRef<'vir> {
    pub exclusive_idn: vir::FunctionIdn<'vir, (vir::ImState, vir::Int, vir::Ref), vir::Bool>,
    pub shared_idn: vir::FunctionIdn<'vir, (vir::ImState, vir::Int, vir::Ref), vir::Bool>,
    // TODO figure out type-refined versions of these:
    // pub local_exclusive_idn: vir::FunctionIdn<
    //     'vir,
    //     (vir::ImState, vir::Int, vir::TyVal, vir::Ref, vir::TyVal, vir::Ref),
    //     vir::Bool,
    // >,
    // pub atomic_exclusive_idn: vir::FunctionIdn<
    //     'vir,
    //     (vir::ImState, vir::Int, vir::TyVal, vir::Ref, vir::TyVal, vir::Ref),
    //     vir::Bool,
    // >,
    pub addr_to_idx_idn: vir::FunctionIdn<'vir, vir::Ref, vir::Int>,
}

// TODO take Option of parent type to optionally encode local/atomic exclusive

// #[derive(Debug, Clone, Copy)]
// pub struct ImCapEncRefNew<'vir> {
//     pub exclusive_idn:
//         vir::FunctionIdn<'vir, (vir::ImState, vir::Int, vir::Ref), vir::Bool>,
//     pub shared_idn:
//         vir::FunctionIdn<'vir, (vir::ImState, vir::Int, vir::Ref), vir::Bool>,
//     // TODO figure out type-refined versions of these:
//     // pub local_exclusive_idn: vir::FunctionIdn<
//     //     'vir,
//     //     (vir::ImState, vir::Int, vir::Ref, vir::Ref),
//     //     vir::Bool,
//     // >,
//     // pub atomic_exclusive_idn: vir::FunctionIdn<
//     //     'vir,
//     //     (vir::ImState, vir::Int, vir::TyVal, vir::Ref, vir::TyVal, vir::Ref),
//     //     vir::Bool,
//     // >,
//     pub addr_to_idx_idn: vir::FunctionIdn<'vir, vir::Ref, vir::Int>,
// }

impl<'vir> OutputRefAny for ImCapEncRef<'vir> {}

#[derive(Debug, Clone, Copy)]
pub struct ImCapEncResult<'vir> {
    domain: vir::Domain<'vir>,
}

pub struct ImCapEnc;

impl TaskEncoder for ImCapEnc {
    task_encoder::encoder_cache!(ImCapEnc);
    const ENCODER_NAME: &'static str = "interior mutability state encoder";

    type TaskDescription<'vir> = RustTyDecomposition<'vir>;
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
        // TODO remove

        let im_state = deps.require_ref::<ImStateEnc>(())?;
        let im_ty_state = deps.require_ref::<ImTyStateEnc>(*task_key)?;

        vir::with_vcx(|vcx| {
            let mut functions = Vec::new();
            let mut axioms = Vec::new();

            let ty_name = deps.require_dep::<ImTyNameEnc>(*task_key)?;

            let exclusive_idn = vir::FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "cap_exclusive_{}", ty_name),
                (vir::TYPE_IMSTATE, vir::TYPE_INT, vir::TYPE_REF),
                vir::TYPE_BOOL,
            );

            let shared_idn = vir::FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "cap_shared_{}", ty_name),
                (vir::TYPE_IMSTATE, vir::TYPE_INT, vir::TYPE_REF),
                vir::TYPE_BOOL,
            );

            // let local_exclusive_idn = vir::FunctionIdn::new(
            //     vir::ViperIdent::new("cap_local"),
            //     (
            //         vir::TYPE_IMSTATE,
            //         vir::TYPE_INT,
            //         vir::TYPE_TYVAL,
            //         vir::TYPE_REF,
            //         vir::TYPE_TYVAL,
            //         vir::TYPE_REF,
            //     ),
            //     vir::TYPE_BOOL,
            // );

            // let atomic_exclusive_idn = vir::FunctionIdn::new(
            //     vir::ViperIdent::new("cap_atomic"),
            //     (
            //         vir::TYPE_IMSTATE,
            //         vir::TYPE_INT,
            //         vir::TYPE_TYVAL,
            //         vir::TYPE_REF,
            //         vir::TYPE_TYVAL,
            //         vir::TYPE_REF,
            //     ),
            //     vir::TYPE_BOOL,
            // );

            let addr_to_idx_idn = vir::FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "cap_addr_to_idx_{}", ty_name),
                vir::TYPE_REF,
                vir::TYPE_INT,
            );

            deps.emit_output_ref(*task_key, ImCapEncRef {
                exclusive_idn,
                shared_idn,
                // local_exclusive_idn,
                // atomic_exclusive_idn,
                addr_to_idx_idn,
            })?;

            // Addr to index conversion for local capabilities

            functions.push(vcx.mk_domain_function(addr_to_idx_idn, false, None));

            let zero = vcx.mk_int::<0>();
            let addr_to_idx_neg = vcx.mk_domain_axiom(
                vir::vir_format_identifier!(vcx, "cap_addr_to_idx_neg_{}", ty_name),
                vir::expr! {
                    forall l: Ref ::
                    { [addr_to_idx_idn](l) }
                    ([addr_to_idx_idn](l)) < (zero)
                },
            );
            axioms.push(addr_to_idx_neg);

            let addr_to_idx_bi = vcx.mk_domain_axiom(
                vir::vir_format_identifier!(vcx, "cap_addr_to_idx_bi_{}", ty_name),
                vir::expr! {
                    forall l0: Ref, l1: Ref ::
                    { ([addr_to_idx_idn](l0)), ([addr_to_idx_idn](l1)) }
                    (([addr_to_idx_idn](l0)) == ([addr_to_idx_idn](l1))) == ((l0) == (l1))
                },
            );
            axioms.push(addr_to_idx_bi);

            // Capabilities

            functions.push(vcx.mk_domain_function(exclusive_idn, false, None));
            functions.push(vcx.mk_domain_function(shared_idn, false, None));
            // functions.push(vcx.mk_domain_function(local_exclusive_idn, false, None));
            // functions.push(vcx.mk_domain_function(atomic_exclusive_idn, false, None));

            // Capability Implications

            let exclusive_shared = vcx.mk_domain_axiom(
                vir::vir_format_identifier!(vcx, "cap_exclusive_shared_{}", ty_name),
                vir::expr! {
                    forall s: ImState, l: Ref, i: Int ::
                    { ([exclusive_idn](s, i, l)) }
                    ([exclusive_idn](s, i, l)) ==> ([shared_idn](s, i, l))
                },
            );
            axioms.push(exclusive_shared);

            // // local-capabilities are fully available when the address specified in `local` is not
            // // modified and modifiable
            // let local_exclusive_full =
            //     vcx.mk_domain_axiom(vir::ViperIdent::new("local_exclusive_full"), vir::expr! {
            //         forall s: ImState, t0: Type, t1: Type, l0: Ref, l1: Ref, i: Int ::
            //         { ([local_exclusive_idn](s, i, t0, l0, t1, l1))  }
            //         (([local_exclusive_idn](s, i, t0, l0, t1, l1)) &&
            //          (([im_state.modifiable_idn](s, t0, l0)) &&
            //           ([im_state.not_modified_idn](s, t0, l0)))) ==>
            //             ([exclusive_idn](s, ([addr_to_idx_idn](t0, l0)), t1, l1))
            //     });
            // axioms.push(local_exclusive_full);

            // // local-exclusive is at least as strong as shared when `local` is not modified
            // let local_exclusive_partial =
            //     vcx.mk_domain_axiom(vir::ViperIdent::new("local_exclusive_partial"), vir::expr! {
            //         forall s: ImState, t0: Type, t1: Type, l0: Ref, l1: Ref, i: Int ::
            //         { ([local_exclusive_idn](s, i, t0, l0, t1, l1))  }
            //         (([local_exclusive_idn](s, i, t0, l0, t1, l1)) &&
            //             ([im_state.not_modified_idn](s, t0, l0))) ==>
            //             ([shared_idn](s, ([addr_to_idx_idn](t0, l0)), t1, l1))
            //     });
            // axioms.push(local_exclusive_partial);

            // local-shared is at least as strong as shared when `local` is not modified
            // let local_shared_partial = vcx.mk_domain_axiom(
            //     vir::ViperIdent::new("local_shared_partial"),
            //     vir::expr! {
            //         forall s: ImState, t0: Type, t1: Type, l0: Ref, l1: Ref, i: Int ::
            //         { ([in_state_idn](s, i, ([local_idn](t0, l0, ([shared_idn](t1, l1))))))  }
            //         (([in_state_idn](s, i, ([local_idn](t0, l0, ([shared_idn](t1, l1)))))) &&
            //             ([im_state.not_modified_idn](s, t0, l0))) ==>
            //             ([in_state_idn](s, ([addr_to_idx_idn](t0, l0)), ([shared_idn](t1, l1))))
            //     },
            // );
            // axioms.push(local_shared_partial);

            // Two-State Axioms

            let shared_stable = vcx.mk_domain_axiom(
                vir::vir_format_identifier!(vcx, "cap_shared_stable_{}", ty_name),
                vir::expr! {
                    forall s: ImState, l: Ref, i: Int ::
                    { ([shared_idn](s, i, l)) }
                    ([shared_idn](s, i, l)) ==>
                        (([im_ty_state.get_snap_idn](s, l)) == ([im_ty_state.get_snap_idn](([im_state.next_idn](s)), l)))
                });
            axioms.push(shared_stable);

            let im_ty = deps.require_ref::<ImTyEnc>(*task_key)?;

            let exclusive_rep_eq = vcx.mk_domain_axiom(
                vir::vir_format_identifier!(vcx, "cap_exclusive_rep_eq_{}", ty_name),
                vir::expr! {
                    forall s: ImState, l: Ref, i: Int ::
                    { ([exclusive_idn](s, i, l)) }
                    ([exclusive_idn](s, i, l)) ==>
                        ([im_ty.common.rep_eq_idn](
                            ([im_ty.common.mk_rep_idn](s, l, ([im_ty_state.get_snap_idn](s, l)))),
                            ([im_ty.common.mk_rep_idn](s, l, ([im_ty_state.get_snap_idn](([im_state.next_idn](s)), l))))))
                },
            );
            axioms.push(exclusive_rep_eq);

            let exclusive_modifiable = vcx.mk_domain_axiom(
                vir::vir_format_identifier!(vcx, "cap_exclusive_modifiable_{}", ty_name),
                vir::expr! {
                        forall s: ImState, l: Ref, i: Int ::
                        { ([exclusive_idn](s, i, l)) }
                        ([exclusive_idn](s, i, l)) ==>
                            ([im_ty_state.modifiable_idn](s, l))
                },
            );
            axioms.push(exclusive_modifiable);

            // Domain
            let domain = vcx.mk_domain(
                vir::vir_format_identifier!(vcx, "im_cap_dom_{}", ty_name),
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
