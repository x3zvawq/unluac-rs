//! 整理 AST 函数声明、转发壳与方法别名。
//!
//! 消费已合法的绑定和方法事实，保持捕获关系与隐式参数的词法身份。

mod chain;
mod constructor;
mod direct;
mod forwarded;
mod method_alias;
mod method_decl;
mod method_plan;
mod rewrite;

pub(super) use method_alias::run_belongs_to_method_alias_owner;
pub(super) use rewrite::apply;
