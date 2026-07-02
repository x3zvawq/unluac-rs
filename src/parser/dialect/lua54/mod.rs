//! 这个模块承载 Lua 5.4 dialect 的 parser 细节。

#[cfg(feature = "decompile-debug")]
mod debug;
mod parser;
mod raw;

#[cfg(feature = "decompile-debug")]
pub(crate) use debug::dump_chunk;
pub(crate) use parser::Lua54Parser;
pub use raw::*;
