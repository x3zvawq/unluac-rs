#![forbid(unsafe_code)]

//! unluac-rs 核心库：多方言 Lua 字节码反编译器。
//!
//! 流水线固定为五阶段：`Parser -> Transformer -> Analysis -> Ast -> Generate`。

pub mod analysis;
pub mod ast;
pub mod debug;
pub mod decompile;
pub mod generate;
mod lua_string;
pub mod parser;
pub mod transformer;

pub use lua_string::LuaString;
