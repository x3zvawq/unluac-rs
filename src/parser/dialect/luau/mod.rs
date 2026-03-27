//! 这个目录承载 Luau dialect 的 parser 实现。
//!
//! Luau 的 chunk 协议与 PUC-Lua 头、常量池和 opcode 空间都不兼容，
//! 因此这里会独立演进，不复用 `puc_lua` 的解析协议。

mod debug;
mod parser;
mod raw;

pub(crate) use debug::dump_chunk;
pub(crate) use parser::LuauParser;
pub use raw::*;
