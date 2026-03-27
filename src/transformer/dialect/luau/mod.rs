//! 这个目录承载 Luau dialect 的 lowering 实现。
//!
//! Luau 的 opcode 语义与 PUC-Lua 的 lowering 规则不是同一套协议；这里先保留
//! 独立模块边界，后续直接在这里实现 raw -> low-IR 的 Luau 规则。
