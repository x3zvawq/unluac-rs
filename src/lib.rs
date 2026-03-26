#![forbid(unsafe_code)]

//! 这个 crate 提供反编译流水线的库接口。
//!
//! 单独保留库层的原因是让 parser、transformer 和后续分析层在 CLI 稳定前
//! 就可以被单测、集成测试和调试工具直接复用。

pub mod ast;
pub mod cfg;
pub mod debug;
pub mod decompile;
pub mod generate;
pub mod hir;
pub mod naming;
pub mod parser;
pub mod readability;
pub mod structure;
mod timing;
pub mod transformer;
