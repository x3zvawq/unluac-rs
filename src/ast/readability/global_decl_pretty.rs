//! global declaration 相关的 readability sugar。
//!
//! 这个 pass 负责维护 AST 上已经有证据支撑的 `global ...` 形状：把 seed run 合并成更自然
//! 的显式声明，并在“字节码能直接证明源码曾显式声明”的前提下保留这些前导。
//!
//! 它是 AST 层 `global decl` 可读性恢复的单一 owner：
//! - AST build 只负责把字节码里显式存在的 `global ... = ...` 降回合法 AST
//! - 这里负责合并 seed run、维护 block 级可见 global 集
//! - Generate 只负责把已经落在 AST 上的 `GlobalDecl` 原样输出，不再猜补
//!
//! 例子：
//! - 连续的 `global a = ...; global b = ...` 如果本来属于同一段声明，这里会合并
//! - 在 Lua 5.5 里，如果外层显式 global gate 让内层 block 重新需要声明全局名，
//!   这里会优先选择“最小 `do + global *`/`global<const> *`”这类较少发明具体名字的
//!   canonical 形状，而不是无根据地把缺失声明枚举成一串具体 global 名
//! - 它不会越权把显式 `global f = function() end` 这种语法糖恢复成 `function f() end`，
//!   那属于 `function_sugar`
//! - 对 Lua 5.5，像 `print(x)` 这种默认 `global *` 语义，在 stripped bytecode 下无法和
//!   “源码先写了 `global none, print`”可靠区分，所以这里不会再凭观测去补显式声明

mod collective;
mod facts;
mod insert;
mod merge;
mod rewrite;

pub(super) use rewrite::apply;

#[cfg(test)]
mod tests;
