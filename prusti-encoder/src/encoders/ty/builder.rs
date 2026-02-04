// TODO: this lint is something we should fix; to address there should probably
//   be an indirection in error storage somewhere, maybe even in `task-encoder`?
#![allow(clippy::result_large_err)]
use std::ops::Deref;

use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::{
    Arity, BackendInterpretationPair, CastType, CompType, DomainAxiomData, DomainIdnSnap,
    FunctionIdn, Type,
};

use crate::encoders::{
    HasTyBuilder, Pure, Purified,
    ty::{
        RustTy,
        generics::GenericParamsEnc,
        pure::{TyPureEncLocal, TyPureEncLocalKind, TyPureRef},
        purified::{TyPurifiedEncLocal, TyPurifiedEncLocalKind, TyPurifiedRef},
    },
};

pub(crate) struct DomainBuilder<'vir, P: HasTyBuilder>(TyBuilder<'vir, P>);

impl<'vir, P: HasTyBuilder> DomainBuilder<'vir, P> {
    pub(crate) fn data(&mut self) -> &mut DomainBuilderData<'vir, P> {
        match &mut self.0.data {
            BuilderData::Domain(data) => data,
            _ => panic!("not a Domain builder"),
        }
    }
}

impl<'vir, P: HasTyBuilder> Deref for DomainBuilder<'vir, P> {
    type Target = TyBuilder<'vir, P>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[repr(transparent)]
pub(crate) struct AdtBuilder<'vir, P: HasTyBuilder>(TyBuilder<'vir, P>);

impl<'vir, P: HasTyBuilder> AdtBuilder<'vir, P> {
    pub(crate) fn data(&mut self) -> &mut AdtBuilderData<'vir> {
        match &mut self.0.data {
            BuilderData::Adt(data) => data,
            _ => panic!("not an ADT builder"),
        }
    }
}

impl<'vir, P: HasTyBuilder> Deref for AdtBuilder<'vir, P> {
    type Target = TyBuilder<'vir, P>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

pub(crate) struct TyBuilder<'vir, P: HasTyBuilder> {
    pub(crate) vcx: &'vir vir::VirCtxt<'vir>,
    name: &'vir str,
    domain_ident: vir::DomainIdnSnap<'vir>,
    self_type: vir::TypeSnap<'vir>,
    unreachable_to_snap: vir::FunctionIdn<'vir, vir::ManyTyVal, vir::Snap>,
    pub(super) params: super::generics::GenericParams<'vir>,
    data: BuilderData<'vir, P>,
}

pub enum BuilderData<'vir, P: HasTyBuilder> {
    Adt(AdtBuilderData<'vir>),
    Domain(DomainBuilderData<'vir, P>),
    None,
}

#[derive(Default)]
pub(crate) struct AdtBuilderData<'vir> {
    constructors: Vec<vir::AdtConstructor<'vir>>,
    discr_fn: Option<DiscrFnBuilder<'vir>>,
}

// #[derive(Default)]
pub(crate) struct DomainBuilderData<'vir, P: HasTyBuilder> {
    axioms: Vec<vir::DomainAxiom<'vir>>,
    functions: Vec<vir::DomainFunction<'vir>>,
    interpretation: Option<&'vir [&'vir vir::BackendInterpretationPair<'vir>]>,
    _purity: std::marker::PhantomData<P>,
}

impl<'vir, P: HasTyBuilder> Default for DomainBuilderData<'vir, P> {
    fn default() -> Self {
        Self {
            axioms: Default::default(),
            functions: Default::default(),
            interpretation: Default::default(),
            _purity: Default::default(),
        }
    }
}

#[derive(Clone, Copy)]
pub(crate) enum DiscrFnBuilder<'vir> {
    Building {
        param: vir::LocalDeclCSnap<'vir>,
        recv: vir::ExprCSnap<'vir>,
        acc: vir::ExprCSnap<'vir>,
    },
    Built(vir::Function<'vir>),
}

impl<'vir, P: HasTyBuilder> TyBuilder<'vir, P> {
    pub(crate) fn new<E: TaskEncoder>(
        deps: &mut TaskEncoderDependencies<'vir, E>,
        vcx: &'vir vir::VirCtxt<'vir>,
        ty: RustTy<'vir>,
    ) -> Self {
        let params = deps.require_dep::<GenericParamsEnc>(ty.params).unwrap();
        let name = vir::vir_format!(vcx, "s_{}", ty.name());
        let domain_ident = DomainIdnSnap::new(vir::ViperIdent::new(name), 0);
        let self_type = domain_ident();
        let unreachable_to_snap = FunctionIdn::new(
            vir::ViperIdent::new(vir::vir_format!(vcx, "{name}_unreachable")),
            params.ty_args(),
            self_type,
        );
        TyBuilder {
            vcx,
            name,
            domain_ident,
            self_type,
            unreachable_to_snap,
            params,
            data: BuilderData::None,
        }
    }

    pub(crate) fn self_type(&self) -> vir::TypeCSnap<'vir> {
        self.self_type.downcast_ty()
    }

    pub(crate) fn set_domain_builder(&mut self) -> &mut DomainBuilder<'vir, P> {
        match &mut self.data {
            BuilderData::Adt(_) => panic!("already an ADT builder"),
            BuilderData::Domain(_) => {}
            data @ BuilderData::None => {
                *data = BuilderData::Domain(DomainBuilderData::<P>::default());
            }
        }
        // SAFETY: `DomainBuilder` is repr transparent
        let builder = self as *mut Self as *mut DomainBuilder<'vir, P>;
        unsafe { &mut *builder }
    }

    pub(crate) fn set_adt_builder(&mut self) -> &mut AdtBuilder<'vir, P> {
        match &mut self.data {
            BuilderData::Domain(_) => panic!("already a Domain builder"),
            BuilderData::Adt(_) => {}
            data @ BuilderData::None => {
                *data = BuilderData::Adt(AdtBuilderData::default());
            }
        }
        // SAFETY: `AdtBuilder` is repr transparent
        let builder = self as *mut Self as *mut AdtBuilder<'vir, P>;
        unsafe { &mut *builder }
    }
}

impl<'vir> TyBuilder<'vir, Pure> {
    pub(crate) fn output_ref(&self) -> TyPureRef<'vir> {
        TyPureRef {
            domain: self.domain_ident.cast_ty(),
            unreachable_to_snap: self.unreachable_to_snap,
        }
    }

    pub(crate) fn build(self) -> TyPureEncLocal<'vir> {
        let unreachable_to_snap = vir::with_vcx(|vcx| {
            let false_ = vcx.alloc_array(&[vcx.mk_bool::<false>()]);
            vcx.mk_function(
                self.unreachable_to_snap,
                (self.params.ty_decls(),),
                false_,
                false_,
                None,
                None,
            )
        });
        let kind = self.build_kind();
        TyPureEncLocal {
            unreachable_to_snap,
            kind,
        }
    }

    fn build_kind(self) -> TyPureEncLocalKind<'vir> {
        match self.data {
            BuilderData::Domain(data) => {
                let domain = self.vcx.mk_domain(
                    self.domain_ident.name(),
                    &[],
                    self.vcx.alloc_slice(data.axioms.as_slice()),
                    self.vcx.alloc_slice(data.functions.as_slice()),
                    data.interpretation,
                );
                TyPureEncLocalKind::Domain { domain }
            }
            BuilderData::Adt(data) => {
                let adt = self.vcx.mk_adt(
                    self.domain_ident.name(),
                    &[],
                    self.vcx.alloc_slice(data.constructors.as_slice()),
                );
                let discr_fn = data.discr_fn.map(|df| {
                    let DiscrFnBuilder::Built(df) = df else {
                        panic!("discriminant function not built");
                    };
                    df
                });
                TyPureEncLocalKind::Adt { adt, discr_fn }
            }
            BuilderData::None => unreachable!("no builder data"),
        }
    }
}

impl<'vir> TyBuilder<'vir, Purified> {
    pub(crate) fn output_ref(&self) -> TyPurifiedRef<'vir> {
        TyPurifiedRef {
            domain: self.domain_ident.cast_ty(),
            unreachable_to_snap: self.unreachable_to_snap,
        }
    }

    pub(crate) fn build(self) -> TyPurifiedEncLocal<'vir> {
        let unreachable_to_snap = vir::with_vcx(|vcx| {
            let false_ = vcx.alloc_array(&[vcx.mk_bool::<false>()]);
            vcx.mk_function(
                self.unreachable_to_snap,
                (self.params.ty_decls(),),
                false_,
                false_,
                None,
                None,
            )
        });
        let kind = self.build_kind();
        TyPurifiedEncLocal {
            unreachable_to_snap,
            kind,
        }
    }

    fn build_kind(self) -> TyPurifiedEncLocalKind<'vir> {
        match self.data {
            BuilderData::Domain(data) => {
                let domain = self.vcx.mk_domain(
                    self.domain_ident.name(),
                    &[],
                    self.vcx.alloc_slice(data.axioms.as_slice()),
                    self.vcx.alloc_slice(data.functions.as_slice()),
                    data.interpretation,
                );
                TyPurifiedEncLocalKind::Domain { domain }
            }
            BuilderData::Adt(data) => {
                let adt = self.vcx.mk_adt(
                    self.domain_ident.name(),
                    &[],
                    self.vcx.alloc_slice(data.constructors.as_slice()),
                );
                let discr_fn = data.discr_fn.map(|df| {
                    let DiscrFnBuilder::Built(df) = df else {
                        panic!("discriminant function not built");
                    };
                    df
                });
                TyPurifiedEncLocalKind::Adt { adt, discr_fn }
            }
            BuilderData::None => unreachable!("no builder data"),
        }
    }
}

impl<'vir, P: HasTyBuilder> AdtBuilder<'vir, P> {
    pub(crate) fn constructor<A: vir::Arity>(
        &mut self,
        prefix: &str,
        fields: A::Tys<'vir>,
        discr: Option<vir::ExprCSnap<'vir>>,
    ) -> (
        FunctionIdn<'vir, A, vir::CSnap>,
        Vec<vir::AdtDestructor<'vir, vir::CSnap, vir::Dyn>>,
    ) {
        let name = format!("{prefix}cons");
        let self_ty = self.self_type();
        assert!(
            self.data().discr_fn.is_none() || discr.is_some(),
            "discr was passed previously, but now it wasn't"
        );
        let self_name = self.name;
        let name = vir::vir_format!(self.vcx, "{self_name}_{name}",);
        let locals = self.vcx.alloc_slice(
            &A::params(fields)
                .into_iter()
                .enumerate()
                .map(|(i, ty)| {
                    self.vcx
                        .mk_local_decl(vir::vir_format!(self.vcx, "{self_name}_{prefix}{i}",), ty)
                })
                .collect::<Vec<_>>(),
        );
        let constructor = self.vcx.mk_adt_constructor(name, locals);
        self.data().constructors.push(constructor);
        let ident = FunctionIdn::new(vir::ViperIdent::new(name), fields, self_ty);
        if let Some(discr) = discr {
            let df = self.data().discr_fn.take().map(|df| {
                let DiscrFnBuilder::Building { param, recv, acc } = df else {
                    panic!("discriminant function was already built");
                };
                let acc = self.vcx.mk_ternary_expr(
                    self.vcx.mk_adt_discriminator_expr(recv, name),
                    discr,
                    acc,
                );
                DiscrFnBuilder::Building { param, recv, acc }
            });
            let df = df.unwrap_or_else(|| {
                let param = self.vcx.mk_local_decl("self", self_ty);
                DiscrFnBuilder::Building {
                    param,
                    recv: self.vcx.mk_local_ex(param),
                    acc: discr,
                }
            });
            self.data().discr_fn = Some(df)
        }
        (
            ident,
            locals
                .iter()
                .map(|arg| self.vcx.mk_adt_destructor(arg.name, self_ty, arg.ty))
                .collect(),
        )
    }

    pub(crate) fn build_discr_fn(
        &mut self,
        ty: vir::TypeCSnap<'vir>,
    ) -> vir::FunctionIdn<'vir, vir::CSnap, vir::CSnap> {
        let self_ty = self.self_type();
        let param = self.vcx.mk_local_decl("self", self_ty);
        let ident = FunctionIdn::new(
            vir::ViperIdent::new(vir::vir_format!(self.vcx, "{}_discr", self.name)),
            param.ty,
            ty,
        );
        let (expr, posts) = if let Some(df) = self.data().discr_fn {
            let DiscrFnBuilder::Building { acc, .. } = df else {
                panic!("discriminant function already built");
            };
            (Some(acc), &[][..])
        } else {
            // We get here if we didn't add any constructors to the ADT (i.e.
            // this is an empty enum = uninhabitable type). Viper forbids this
            // (see silver#693, silver#696), so here we will just add a dummy
            // constructor that won't actually be used by the encoders. Instead
            // we encode the uninhabitability by adding an `ensures false` to
            // the discriminant function.
            // TODO: https://github.com/Aurel300/prusti-dev/pull/89#discussion_r2263306839
            let self_name = self.name;
            let name = vir::vir_format!(self.vcx, "{self_name}_DummyConstructor",);
            let constructor = self.vcx.mk_adt_constructor::<(), !, vir::Dyn>(name, &[]);
            self.data().constructors.push(constructor);
            (None, self.vcx.alloc_slice(&[self.vcx.mk_bool::<false>()]))
        };
        let built_fn = self
            .vcx
            .mk_function(ident, (param,), &[], posts, None, expr);
        self.data().discr_fn = Some(DiscrFnBuilder::Built(built_fn));
        ident
    }
}

impl<'vir, P: HasTyBuilder> DomainBuilder<'vir, P> {
    pub(crate) fn function<A: Arity, T: CompType>(
        &mut self,
        name: &str,
        args: A::Tys<'vir>,
        ret: Type<'vir, T>,
    ) -> FunctionIdn<'vir, A, T> {
        let name = vir::vir_format!(self.vcx, "{}_{name}", self.name);
        let ident = FunctionIdn::new(vir::ViperIdent::new(name), args, ret);
        let function = self.vcx.mk_domain_function(ident, false, None);
        self.data().functions.push(function);
        ident
    }

    pub(crate) fn backend_func<A: Arity, T: CompType>(
        &mut self,
        name: &str,
        args: A::Tys<'vir>,
        ret: Type<'vir, T>,
        interpretation: Option<&'static str>,
    ) -> FunctionIdn<'vir, A, T> {
        let name = vir::vir_format!(self.vcx, "{}_{name}", self.name);
        let ident = FunctionIdn::new(vir::ViperIdent::new(name), args, ret);
        let function = self.vcx.mk_domain_function(ident, false, interpretation);
        self.data().functions.push(function);
        ident
    }

    pub(crate) fn axiom(&mut self, name: &str, expr: vir::ExprBool<'vir>) {
        let name = vir::vir_format!(self.vcx, "{}_ax_{name}", self.name);
        let axiom = self.vcx.alloc(DomainAxiomData { name, expr });
        self.data().axioms.push(axiom);
    }

    pub(crate) fn set_interpretation(
        &mut self,
        interp: &'vir [&'vir BackendInterpretationPair<'vir>],
    ) {
        self.data().interpretation = Some(interp);
    }
}
