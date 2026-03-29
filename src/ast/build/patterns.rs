//! AST build：需要看相邻 HIR 语句模式的 lowering。
//!
//! 这里先把模式分成两类：
//! - `syntax`：撤销前层 lowering，恢复“目标 dialect 的合法语法”。
//! - `shape`：在合法语法之上，再把结果收敛成更接近源码的形状。
//!
//! 先把边界显式化，后面再决定哪些 `shape` 规则要继续留在 AST build，
//! 哪些更适合迁回 Readability。

mod shape;
mod syntax;

#[cfg(test)]
mod tests;
