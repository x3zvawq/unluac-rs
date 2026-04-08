//! HIR simplify 子模块对 `hir::traverse` 共享宏的转发。
//!
//! 宏定义已提升到 [`crate::hir::traverse`]，这里只做 re-export 让
//! `walk.rs` / `visit.rs` 原有的 `use super::traverse::*` 路径继续工作。

pub(super) use crate::hir::traverse::{
    traverse_hir_call_children, traverse_hir_decision_children, traverse_hir_expr_children,
    traverse_hir_lvalue_children, traverse_hir_stmt_children,
    traverse_hir_table_constructor_children,
};
