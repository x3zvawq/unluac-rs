//! 这个模块承载 Lua 5.1 dialect 的 parser 细节。
//!
//! 之所以单独拆目录，是因为随着支持的 dialect 增多，Lua 5.1 专属的
//! opcode、operand、extra 和解析规则如果继续放在公共目录里，会让
//! parser 层越来越难维护。

mod parser;
mod raw;

pub(crate) use parser::Lua51Parser;
pub use raw::*;
