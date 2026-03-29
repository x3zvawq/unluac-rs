//! global declaration 相关的 readability sugar。
//!
//! 这个 pass 会把缺失的全局声明补成显式前导，例如把嵌套函数里只读的
//! `math.max(x, 1)` 收敛成先声明 `global const math` 再使用它。
//!
//! 它是 AST 层 `global decl` 可读性恢复的单一 owner：
//! - AST build 只负责把字节码里显式存在的 `global ... = ...` 降回合法 AST
//! - 这里负责补 missing decl、合并 seed run、维护 block 级可见 global 集
//! - Generate 只负责把已经落在 AST 上的 `GlobalDecl` 原样输出，不再猜补
//!
//! 例子：
//! - 嵌套函数里第一次只读 `math.max`，这里会补 `global const math`
//! - 连续的 `global a = ...; global b = ...` 如果本来属于同一段声明，这里会合并
//! - 它不会越权把显式 `global f = function() end` 这种语法糖恢复成 `function f() end`，
//!   那属于 `function_sugar`

mod facts;
mod insert;
mod merge;
mod rewrite;

use super::ReadabilityContext;
use crate::ast::common::AstModule;

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    rewrite::apply(module, context)
}

#[cfg(test)]
mod tests;
