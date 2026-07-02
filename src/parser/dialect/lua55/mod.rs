//! 这个模块承载 Lua 5.5 dialect 的 parser 细节。

#[cfg(feature = "decompile-debug")]
mod debug;
mod parser;
mod raw;

#[cfg(feature = "decompile-debug")]
pub(crate) use debug::dump_chunk;
pub(crate) use parser::Lua55Parser;
pub use raw::*;
