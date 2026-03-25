//! 这个模块承载 Lua 5.2 dialect 的 parser 细节。
//!
//! Lua 5.2 和 5.1 同属 PUC-Lua family，但 proto 布局、upvalue 描述符、`LOADKX`
//! / `EXTRAARG`、`GETTABUP` / `SETTABUP` 等规则都已经出现实质差异，所以继续保留
//! 独立版本目录，让差异显式落在这里。

mod debug;
mod parser;
mod raw;

pub(crate) use debug::dump_chunk;
pub(crate) use parser::Lua52Parser;
pub use raw::*;
