//! 这个目录承载 LuaJIT dialect 的 lowering 实现。
//!
//! LuaJIT 与 PUC-Lua / Luau 的 bytecode 语义都不是同一套 opcode 空间，因此保留独立模块。

mod lower;

pub(crate) use lower::lower_chunk;
