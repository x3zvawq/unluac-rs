//! 这个模块承载 Lua 5.5 dialect 的 parser 细节。

mod debug;
mod parser;
mod raw;

pub(crate) use debug::dump_chunk;
pub(crate) use parser::Lua55Parser;
pub use raw::*;
