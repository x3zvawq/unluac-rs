//! AST build：需要看相邻 HIR 语句的合法语法化模式。
//!
//! 这里仅撤销前层 lowering，恢复目标 dialect 的合法语法。多值转发和物化属于 HIR
//! value-pack owner；可读性 sugar 属于 Readability，均不在 AST build 猜相邻形状。

mod syntax;
