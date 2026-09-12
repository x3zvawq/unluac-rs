//! 函数声明相关的 readability sugar。
//!
//! 这里保留 AST 已明确携带的 method 声明边界，并处理 `local f = obj.method; f(obj)` 这类
//! 局部 method-alias 壳，以及把纯转发的局部函数壳吸收到下一条语句里。方法调用名只提供
//! 声明风格提示；冒号声明另以参数身份和词法遮蔽检查证明，不推断两个同名字段指向同一闭包。

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
