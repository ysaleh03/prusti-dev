mod generic;
mod mir_builtin;
mod mir_pure;
mod mir_poly_impure;
mod mir_poly_purified;
mod mir_impure;
mod mir_purified;
mod spec;
mod mir_pure_function;
mod pure;
mod local_def;
mod purified_local_def;
mod r#type;
mod r#const;
mod mono;
// TODO: move `mir_impure` to this dir:
pub mod impure;
pub mod purified;

cfg_if::cfg_if! {
    if #[cfg(feature = "mono_function_encoding")] {
        pub use mono::mir_pure_function::MirMonoFunctionEnc as PureFunctionEnc;
    } else {
        pub use mir_pure_function::MirFunctionEnc as PureFunctionEnc;
    }
}

pub use domain::all_outputs as DomainEnc_all_outputs;
pub use generic::GenericEnc;
pub use impure::fn_wand::{WandEnc, WandEncOutput, WandEncTask};
pub use local_def::*;
pub use mir_builtin::{MirBuiltinEnc, MirBuiltinEncTask};
pub use mir_impure::{ImpureEncVisitor, MirImpureEnc};
pub use mir_poly_impure::MirPolyImpureEnc;
pub use mir_poly_purified::MirPolyPurifiedEnc;
pub use mir_pure::{MirPureEnc, MirPureEncTask, PureKind};
pub use mir_purified::{MirPurifiedEnc, PurifiedEncVisitor};
pub use mono::{
    mir_impure::MirMonoImpureEnc, mir_purified::MirMonoPurifiedEnc, task_description::*,
};
pub use predicate::{PredicateEnc, PredicateEncOutputRef};
pub use pure::spec::{MirSpecEnc, PurifiedMirSpecEnc};
pub use purified::fn_wand::{
    WandEnc as PurifiedWandEnc, WandEncOutput as PurifiedWandEncOutput,
    WandEncTask as PurifiedWandEncTask,
};
pub use purified_local_def::*;
pub use r#const::ConstEnc;
pub use r#type::*;
pub use snapshot::SnapshotEnc;
pub(super) use spec::with_proc_spec;
pub use spec::{is_function_trusted, is_type_trusted, SpecEnc, SpecEncTask};
pub use viper_tuple::{ViperTupleEnc, ViperTupleEncOutput};
