//! 函数声明相关的 readability sugar。
//!
//! 例如把 `obj.field = function(self, x) ... end` 收回成更接近源码的
//! `function obj:field(x) ... end`，把 `local f = obj.method; f(obj)` 这类局部 method-alias
//! 壳收回 `obj:method()`，以及把纯转发的局部函数壳吸收到下一条语句里。

mod analysis;
mod chain;
mod constructor;
mod direct;
mod forwarded;
mod method_alias;
mod rewrite;

pub(super) use method_alias::run_belongs_to_method_alias_owner;
pub(super) use rewrite::apply;
