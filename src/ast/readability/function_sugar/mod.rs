//! 函数声明相关的 readability sugar。
//!
//! 这里保留 AST 已明确携带的 method 声明边界，并处理 `local f = obj.method; f(obj)` 这类
//! 局部 method-alias 壳，以及把纯转发的局部函数壳吸收到下一条语句里。普通
//! `obj.field = function(...) ... end` 的字节码无法证明原始语法是否为 method，因此保持
//! plain field 形式，避免隐式 `self` 改变调用语义。

mod chain;
mod constructor;
mod direct;
mod forwarded;
mod method_alias;
mod rewrite;

pub(super) use method_alias::run_belongs_to_method_alias_owner;
pub(super) use rewrite::apply;
