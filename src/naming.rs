//! Naming 层入口。

mod allocate;
mod assign;
mod common;
mod debug;
mod error;
mod evidence;
mod hints;
mod lexical;
mod strategy;
mod support;
mod validate;

pub use assign::assign_names;
pub use common::{FunctionNameMap, NameInfo, NameMap, NameSource, NamingMode, NamingOptions};
pub use debug::dump_naming;
pub use error::NamingError;
