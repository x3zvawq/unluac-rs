//! 整理显式 global 声明的 seed 交接与 block 级可见性。
//!
//! HIR 发布 typed global 协议，AST build 验证目标语法；本 pass 消费已有 gate，
//! 合并声明并选择满足 gate 的局部源码形状。没有 gate 时不凭全局访问发明声明，
//! 函数声明 sugar 交给 function_sugar，Generate 只输出已有 AST。
//! 例如同身份 singleton 的 local seed=value; global g=seed 可合成 global g=value。

mod collective;
mod facts;
mod insert;
mod merge;
mod rewrite;

pub(in crate::ast::readability) use facts::{
    VisibleGlobals, extending_global_scope_preserves_expr,
};

pub(super) use rewrite::apply;
