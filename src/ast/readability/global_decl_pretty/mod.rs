//! 整理显式 global 声明的交接与 block 级可见性。
//!
//! 消费 HIR typed 协议及合法 AST gate；函数语法由 function-sugar 整理。

mod collective;
mod facts;
mod insert;
mod merge;
mod rewrite;

pub(in crate::ast::readability) use facts::{
    VisibleGlobals, extending_global_scope_preserves_expr,
};

pub(super) use rewrite::apply;
