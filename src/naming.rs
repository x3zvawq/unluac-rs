//! Naming 层入口。

mod allocate;
mod assign;
mod ast_facts;
mod common;
mod debug;
mod error;
mod evidence;
mod hints;
mod lexical;
mod strategy;
mod support;
mod validate;

pub use assign::{assign_names, assign_names_with_evidence};
pub use common::{
    FunctionNameMap, NameInfo, NameMap, NameSource, NamingEvidence, NamingMode, NamingOptions,
};
pub use debug::dump_naming;
pub use error::NamingError;
pub use evidence::collect_naming_evidence;
