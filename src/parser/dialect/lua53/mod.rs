//! 这个模块承载 Lua 5.3 dialect 的 parser 细节。
//!
//! Lua 5.3 仍属于 PUC-Lua family，但它把整数/浮点常量标签分开、调整了 header
//! 校验、改了字符串长度编码，还新增了一组位运算 opcode；这些差异应该显式落在
//! 版本目录里，而不是继续塞回共享层。

mod debug;
mod parser;
mod raw;

pub(crate) use debug::dump_chunk;
pub(crate) use parser::Lua53Parser;
pub use raw::*;
