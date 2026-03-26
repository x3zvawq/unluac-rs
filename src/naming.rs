//! Naming 层入口。

mod assign;
mod debug;
mod error;

pub use assign::{
    FunctionNameMap, NameInfo, NameMap, NameSource, NamingMode, NamingOptions, assign_names,
};
pub use debug::dump_naming;
pub use error::NamingError;
