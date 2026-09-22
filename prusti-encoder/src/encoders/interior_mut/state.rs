use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies};
use vir::ViperIdent;

/// The state encoder encodes the state representation used for interior-mutability reasoning

#[derive(Debug, Clone, Copy)]
pub struct ImStateEncRef<'vir> {
    get_snap_ref: vir::FunctionIdn<'vir, (vir::ImState, vir::TyVal, vir::Ref), vir::PSnap>,
    get_rep_ref: vir::FunctionIdn<'vir, (vir::ImState, vir::TyVal, vir::Ref), vir::GRep>,
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

            let get_rep_ref = vir::FunctionIdn::new(
                vir::ViperIdent::new("getrep"),
                (vir::TYPE_IMSTATE, vir::TYPE_TYVAL, vir::TYPE_REF),
                vir::TYPE_GREP,
            );
            let get_snap_ref = vir::FunctionIdn::new(
                vir::ViperIdent::new("getrep"),
                (vir::TYPE_IMSTATE, vir::TYPE_TYVAL, vir::TYPE_REF),
                vir::TYPE_PSNAP,
            );

            deps.emit_output_ref(*task_key, ImStateEncRef {
                get_rep_ref,
                get_snap_ref,
            });

            let get_rep = vcx.mk_domain_function(
                get_rep_ref,
                true,
                None
            );
            functions.push(get_rep);

            let get_snap = vcx.mk_domain_function(
                get_snap_ref,
                true,
                None,
            );
            functions.push(get_snap);

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
