//! global declaration 相关的 readability sugar。
//!
//! 这个 pass 负责维护 AST 上已有显式 gate 约束的 `global ...` 形状：把 singleton seed
//! handoff 合并成更自然的显式声明，并为受该 gate 约束的后缀选择等价源码形状。
//!
//! 它是 AST 层 `global decl` 可读性恢复的单一 owner：
//! - HIR 认领完整 initialized-global 协议并发布 typed `HirGlobalDecl`，AST build 只验证目标语法
//! - 这里负责合并 seed run、维护 block 级可见 global 集
//! - Generate 只负责把已经落在 AST 上的 `GlobalDecl` 原样输出，不再猜补
//!
//! 例子：
//! - `local seed = value; global g = seed` 的 singleton 同身份 handoff 可以折成
//!   `global g = value`；多个 target 保持分立，以免改变可观察的 store 顺序
//! - 在 Lua 5.5 里，如果外层显式 global gate 让内层 block 重新需要声明全局名，
//!   这里会优先选择“最小 `do + global *`/`global<const> *`”这类较少发明具体名字的
//!   canonical 形状，而不是无根据地把缺失声明枚举成一串具体 global 名
//! - 它不会越权把显式 `global f = function() end` 这种语法糖恢复成 `function f() end`，
//!   那属于 `function_sugar`
//! - 前层没有发布任何显式 gate 时，这里不会仅凭 AST 中的 global 访问发明声明

mod collective;
mod facts;
mod insert;
mod merge;
mod rewrite;

pub(in crate::ast::readability) use facts::{
    VisibleGlobals, extending_global_scope_preserves_expr,
};

pub(super) use rewrite::apply;
