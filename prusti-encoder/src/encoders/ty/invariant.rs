use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::CastType;

use crate::encoders::{Pure, TyUsePureEnc};

use super::{
    ImTyEnc, RustParamData, RustTy, RustTyDecomposition, RustTyNormalized, TySpecifics,
    generics::{GArgCaster, GArgsCastEnc, GArgsTy, GArgsTyEnc, GenericParamsEnc},
    lifted::TyConstructorEnc,
    pure::TyPureEnc,
};

#[derive(Debug, Clone, Copy)]
enum InvariantTyRef<'vir> {
    GenericParam,
    Constructor(vir::FunctionIdn<'vir, (vir::ManyTyVal, vir::ManyCSnap), vir::TyVal>),
}

#[derive(Debug, Clone, Copy)]
pub struct TyInvariantRef<'vir> {
    invariant: vir::FunctionIdn<'vir, (vir::TyVal, vir::PSnap), vir::Bool>,
    ty: InvariantTyRef<'vir>,
}

impl<'vir> task_encoder::OutputRefAny for TyInvariantRef<'vir> {}

impl<'vir> TyInvariantRef<'vir> {
    pub fn apply<Curr, Next>(
        &self,
        args: GArgsTy<'vir>,
        snap: vir::ExprGenPSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenBool<'vir, Curr, Next> {
        let ty: vir::ExprGenTyVal<'vir, Curr, Next> = match self.ty {
            InvariantTyRef::GenericParam => {
                assert_eq!(args.get_ty::<Curr, Next>().len(), 1);
                assert!(args.get_const::<Curr, Next>().is_empty());
                args.get_ty::<Curr, Next>()[0]
            }
            InvariantTyRef::Constructor(constructor) => {
                constructor.call()(args.get_ty::<Curr, Next>(), args.get_const::<Curr, Next>())
            }
        };
        self.invariant.call()(ty, snap)
    }
}

pub struct TyInvariantEnc;

impl TaskEncoder for TyInvariantEnc {
    task_encoder::encoder_cache!(TyInvariantEnc);
    const ENCODER_NAME: &'static str = "type invariant encoder";

    type TaskDescription<'vir> = RustTy<'vir>;
    type OutputRef<'vir> = TyInvariantRef<'vir>;
    type OutputFullLocal<'vir> = Option<vir::DomainAxiom<'vir>>;
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let invariant = Self::invariant_fn();
            let ty = if matches!(
                task_key.specifics,
                TySpecifics::Param(RustParamData::Generic)
            ) {
                InvariantTyRef::GenericParam
            } else {
                InvariantTyRef::Constructor(
                    deps.require_ref::<TyConstructorEnc>(*task_key)?
                        .ty_constructor,
                )
            };
            let output_ref = TyInvariantRef { invariant, ty };

            deps.emit_output_ref(*task_key, output_ref)?;

            let inv_fn = vcx.mk_domain_function(invariant, false, None);

            // No axiom should be emitted for fully generic parameters
            if matches!(ty, InvariantTyRef::GenericParam) {
                return Ok((None, ()));
            }

            let snap_decl = vcx.mk_local_decl("s", vir::TYPE_PSNAP);
            let snap_ex = vcx.mk_local_ex(snap_decl);
            let params = deps.require_dep::<GenericParamsEnc>(task_key.params)?;
            let args = GArgsTy::new(
                vcx.alloc_slice(params.ty_exprs()),
                vcx.alloc_slice(params.const_exprs()),
            );
            let lhs = output_ref.apply(args, snap_ex);

            let normalized = RustTyNormalized {
                param: RustTyDecomposition::param(),
                concrete: RustTyDecomposition::identity(task_key),
            };
            let snap_caster = deps.require_dep::<GArgsCastEnc<Pure>>(Some(normalized))?;
            let snap_ex = snap_caster
                .cast_to_caller_ctx(snap_ex.upcast_ty())
                .downcast_ty();

            let rhs = InvariantWalker { deps }.encode(task_key, args, snap_ex)?;
            let body = vcx.mk_eq_expr(lhs, rhs);
            let axiom_expr = vir::expr! {
                forall [snap_decl], ..[params.ty_decls()], ..[params.const_decls()] :: {[lhs]}
                    [body]
            };

            let axiom = vcx.mk_domain_axiom(
                vir::vir_format_identifier!(vcx, "ty_invariant_{}", task_key.name()),
                axiom_expr,
            );

            // TODO remove
            let _ = deps.require_dep::<ImTyEnc>(task_key)?;

            Ok((Some(axiom), ()))
        })

    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        let axioms = Self::all_outputs_local_no_errors(program)
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        vir::with_vcx(|vcx| {
            let invariant = vcx.mk_domain_function(Self::invariant_fn(), false, None);
            let domain = vcx.mk_domain(
                vir::ViperIdent::new("Invariant"),
                &[],
                vcx.alloc_slice(&axioms),
                vcx.alloc_slice(&[invariant]),
                None,
            );
            program.add_domain(domain);
        })
    }
}

impl TyInvariantEnc {
    fn invariant_fn<'vir>() -> vir::FunctionIdn<'vir, (vir::TyVal, vir::PSnap), vir::Bool> {
        vir::FunctionIdn::new(
            vir::ViperIdent::new("ty_invariant"),
            (vir::TYPE_TYVAL, vir::TYPE_PSNAP),
            vir::TYPE_BOOL,
        )
    }
}

struct InvariantWalker<'a, 'vir> {
    deps: &'a mut TaskEncoderDependencies<'vir, TyInvariantEnc>,
}

type EncResult<'vir, T> = Result<T, EncodeFullError<'vir, TyInvariantEnc>>;

impl<'a, 'vir> InvariantWalker<'a, 'vir> {
    fn encode(
        &mut self,
        ty: RustTy<'vir>,
        args: GArgsTy<'vir>,
        snap_ex: vir::ExprCSnap<'vir>,
    ) -> EncResult<'vir, vir::ExprBool<'vir>> {
        vir::with_vcx(|vcx| {
            let ty_pure = self.deps.require_dep::<TyPureEnc>(ty)?;
            // TODO cast the psnap to (the right) csnap
            // TODO we also need the const args and generic type args

            Ok(match &ty.specifics {
                TySpecifics::Param(RustParamData::Generic) => unreachable!(),
                // TODO should probably propagate invariants through reference types
                // TySpecifics::ImmRef(data) | TySpecifics::MutRef(data) => {
                //     let foo = data.referent.decompose(ty.params)
                //     self.encode_decomposition(data.referent.decompose(ty.params))?
                // }
                TySpecifics::Addr(_) => {
                    let addr_ty = ty_pure.expect_addr();
                    vcx.mk_eq_expr(addr_ty.common.type_access.call()(snap_ex), args.get_ty()[0])
                }
                TySpecifics::AddrDyn(_) => vir::with_vcx(|vcx| vcx.mk_bool::<true>()),
                TySpecifics::Rep(_) => vir::with_vcx(|vcx| vcx.mk_bool::<true>()),
                _ => vir::with_vcx(|vcx| vcx.mk_bool::<true>()),
            })
        })
    }

    fn encode_decomposition(
        &mut self,
        ty: RustTyDecomposition<'vir>,
        args: GArgsTy<'vir>,
        snap_ex: vir::ExprPSnap<'vir>,
    ) -> EncResult<'vir, vir::ExprBool<'vir>> {
        Ok(self
            .deps
            .require_ref::<TyUseInvariantEnc>(ty)?
            .invariant
            .apply(args, snap_ex))
    }
}

#[derive(Debug, Clone, Copy)]
pub struct TyUseInvariantRef<'vir> {
    invariant: TyInvariantRef<'vir>,
    args: GArgsTy<'vir>,
    snap_caster: GArgCaster<'vir, Pure>,
}

impl<'vir> task_encoder::OutputRefAny for TyUseInvariantRef<'vir> {}

impl<'vir> TyUseInvariantRef<'vir> {
    pub fn invariant<Curr, Next>(
        &self,
        snap: vir::ExprGenSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenBool<'vir, Curr, Next> {
        self.invariant.apply(
            self.args,
            self.snap_caster.cast_to_callee_ctx(snap).downcast_ty(),
        )
    }
}

pub struct TyUseInvariantEnc;

impl TaskEncoder for TyUseInvariantEnc {
    task_encoder::encoder_cache!(TyUseInvariantEnc);
    const ENCODER_NAME: &'static str = "invariant type use encoder";

    type TaskDescription<'vir> = RustTyDecomposition<'vir>;
    type OutputRef<'vir> = TyUseInvariantRef<'vir>;
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let invariant = deps.require_ref::<TyInvariantEnc>(task_key.ty)?;
        let args = deps.require_dep::<GArgsTyEnc>(task_key.args)?;

        let normalized = if task_key.ty.specifics.is_param() {
            None
        } else {
            Some(RustTyNormalized {
                param: RustTyDecomposition::param(),
                concrete: *task_key,
            })
        };
        let snap_caster = deps.require_dep::<GArgsCastEnc<Pure>>(normalized)?;
        let output_ref = TyUseInvariantRef {
            invariant,
            args,
            snap_caster,
        };
        deps.emit_output_ref(*task_key, output_ref)?;
        Ok(((), ()))
    }
}
