use crate::encoders::ty::{
    LazyRustTy, RustAbsPtr,
    impure::{PredicateBuilder, TyImpureAbsPtr, TyImpureEnc},
    pure::{DomainBuilder, TyPureAbsPtr, TyPureAbsPtrData, TyPureEnc},
};
use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::VirCtxt;

pub(crate) fn ty_pure<'vir>(
    _vcx: &'vir VirCtxt<'vir>,
    _data: &RustAbsPtr<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<TyPureAbsPtr<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    let arg_type = (builder.self_type(), vir::TYPE_INT);
    let ptr_deref = builder.function("ptr_deref", arg_type, vir::TYPE_PSNAP);

    // TODO: need s_AbsPtr_typeof and s_Param_typeof here..
    // builder.axiom(
    //     "ptr_deref",
    //     vir::expr! {
    //         forall s: [builder.self_type()], pc: Int :: {[ptr_deref](s, pc)}
    //     },
    // );

    let read = builder.function("read", arg_type, vir::TYPE_BOOL);
    let write = builder.function("write", arg_type, vir::TYPE_BOOL);
    let local = builder.function("local", arg_type, vir::TYPE_BOOL);
    let unique = builder.function("unique", arg_type, vir::TYPE_BOOL);
    let immutable = builder.function("immutable", arg_type, vir::TYPE_BOOL);
    let read_ref = builder.function("readRef", arg_type, vir::TYPE_BOOL);
    let write_ref = builder.function("writeRef", arg_type, vir::TYPE_BOOL);
    let no_read_ref = builder.function("noReadRef", arg_type, vir::TYPE_BOOL);
    let no_write_ref = builder.function("noWriteRef", arg_type, vir::TYPE_BOOL);

    builder.axiom("immutable", vir::expr! {
       forall s: [builder.self_type()], pc: Int :: {[immutable](s, pc)} ([immutable](s, pc)) ==> ([read](s, pc))
    });
    builder.axiom("local", vir::expr! {
       forall s: [builder.self_type()], pc: Int :: {[local](s, pc)} ([local](s, pc)) ==> ([read](s, pc))
    });
    builder.axiom("write", vir::expr! {
       forall s: [builder.self_type()], pc: Int :: {[write](s, pc)} ([write](s, pc)) ==> ([read](s, pc))
    });
    builder.axiom("unique", vir::expr! {
       forall s: [builder.self_type()], pc: Int :: {[unique](s, pc)} ([unique](s, pc)) ==> (([local](s, pc)) && ([write](s, pc)))
    });
    builder.axiom("readRef", vir::expr! {
       forall s: [builder.self_type()], pc: Int :: {[read_ref](s, pc)} ([read_ref](s, pc)) ==> ([immutable](s, pc))
    });
    builder.axiom("writeRef", vir::expr! {
       forall s: [builder.self_type()], pc: Int :: {[write_ref](s, pc)} ([write_ref](s, pc)) ==> (([read_ref](s, pc)) && ([unique](s, pc)))
    });
    builder.axiom("noReadRef", vir::expr! {
       forall s: [builder.self_type()], pc: Int :: {[no_read_ref](s, pc)} ([no_read_ref](s, pc)) ==> ([no_write_ref](s, pc))
    });

    Ok(TyPureAbsPtrData {
        ptr_deref,
        read,
        write,
        local,
        unique,
        immutable,
        read_ref,
        write_ref,
        no_read_ref,
        no_write_ref,
    })
}

pub(crate) fn ty_impure<'vir>(
    _data: &(&'vir LazyRustTy<'vir>, &'vir TyPureAbsPtrData<'vir>),
    _deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<TyImpureAbsPtr<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    super::primitive::set_primitive(builder);
    Ok(())
}
