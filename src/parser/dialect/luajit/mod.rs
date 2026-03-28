//! 这个目录承载 LuaJIT dialect 的 parser 实现。
//!
//! LuaJIT dump 协议与 PUC-Lua / Luau 都不同，因此保持独立 family 边界。

mod debug;
mod parser;
mod raw;

pub(crate) use debug::dump_chunk;
pub(crate) use parser::LuaJitParser;
pub use raw::*;
