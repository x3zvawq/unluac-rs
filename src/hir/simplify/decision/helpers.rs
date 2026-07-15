//! 这个文件承载 decision simplify 共享的表达式辅助逻辑。
//!
//! `decision/mod.rs`、`eliminate.rs` 和 `synthesize/mod.rs` 都会构造逻辑短路表达式。
//! 这里仅保留基础构造；形状整理统一由 `logical_simplify` pass 负责。

use crate::hir::common::{HirExpr, HirLogicalExpr};

pub(super) fn logical_and(lhs: HirExpr, rhs: HirExpr) -> HirExpr {
    HirExpr::LogicalAnd(Box::new(HirLogicalExpr { lhs, rhs }))
}

pub(super) fn logical_or(lhs: HirExpr, rhs: HirExpr) -> HirExpr {
    HirExpr::LogicalOr(Box::new(HirLogicalExpr { lhs, rhs }))
}
