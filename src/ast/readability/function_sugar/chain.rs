//! 这个子模块负责回收“局部别名 + method call”形成的调用链。
//!
//! 它依赖 binding-flow 已统计好的使用次数，只处理纯机械 alias 链，不会越权推断新的
//! 函数 sugar。
//! 例如：`local x = obj:first(); x:finish()` 会在这里尝试折回
//! `obj:first():finish()`。
//! 无用声明由前置 cleanup/fixed-point 删除；这里不跨越其它语句寻找链段。

use super::super::binding_flow::BindingUseIndex;
use super::super::binding_ref::name_matches_binding;
use crate::ast::common::{
    AstBindingRef, AstCallKind, AstExpr, AstLocalAttr, AstLocalBinding, AstLocalOrigin,
    AstMethodCallExpr, AstStmt,
};

pub(super) fn try_chain_local_method_call_stmt(
    stmts: &[AstStmt],
    use_index: &BindingUseIndex,
    stmt_base: usize,
) -> Option<(AstStmt, usize)> {
    let [first, second, ..] = stmts else {
        // 候选忽略[NotApplicable]：method chain 至少需要结果声明和紧邻的后续调用两句。
        return None;
    };
    let (binding, first_call) = single_method_call_local(first)?;
    let chained =
        chain_local_method_call_stmt(first_call, binding.id, second, use_index, stmt_base + 1)?;

    // 到这里第二句已经精确形成“同一 binding 作为唯一 receiver”的 chain 候选；
    // 声明属性、provenance 和后续生命周期才是候选拒绝条件，不能标记普通相邻语句。
    match binding.attr {
        AstLocalAttr::None => {}
        AstLocalAttr::Close => {
            // 候选拒绝[SemanticBarrier:Lifetime]：链化会删除 `<close>` 的离域关闭动作，反例见 regress_415。
            return None;
        }
        AstLocalAttr::Const => {
            // 候选拒绝[PolicyBoundary]：项目选择在函数糖中保留显式 `<const>` 声明身份。
            return None;
        }
    }
    match binding.origin {
        AstLocalOrigin::Recovered => {}
        AstLocalOrigin::DebugHinted | AstLocalOrigin::DebugHintedPhysicalRoot => {
            // 候选拒绝[SemanticBarrier:DebugScope]：删除 debug local 会改变 debug.getlocal 可见的名字与区间，反例见 regress_333。
            return None;
        }
        AstLocalOrigin::PhysicalRoot => {
            // 候选拒绝[SemanticBarrier:Lifetime]：提前释放 call-result 强根会让后续 callback 观察到对象已回收，反例见 regress_412。
            return None;
        }
    }
    if use_index.count_uses_in_suffix(stmt_base + 2, binding.id) != 0 {
        // 候选拒绝[SemanticBarrier:Lifetime]：链化会删除第二次调用后仍活跃的 receiver，反例见 regress_38。
        return None;
    }
    Some((chained, 2))
}

fn single_method_call_local(stmt: &AstStmt) -> Option<(&AstLocalBinding, &AstMethodCallExpr)> {
    let AstStmt::LocalDecl(local_decl) = stmt else {
        // 候选忽略[NotApplicable]：首句不是 local call-result 声明。
        return None;
    };
    let ([binding], [AstExpr::MethodCall(call)]) =
        (local_decl.bindings.as_slice(), local_decl.values.as_slice())
    else {
        // 候选忽略[NotApplicable]：这里只拥有单 binding、单 method-call initializer。
        return None;
    };
    Some((binding, call))
}

fn chain_local_method_call_stmt(
    first_call: &AstMethodCallExpr,
    binding: AstBindingRef,
    second: &AstStmt,
    use_index: &BindingUseIndex,
    second_index: usize,
) -> Option<AstStmt> {
    let AstStmt::CallStmt(call_stmt) = second else {
        // 候选忽略[NotApplicable]：第二句不是可直接接到 receiver 的调用语句。
        return None;
    };
    let AstCallKind::MethodCall(second_call) = &call_stmt.call else {
        // 候选忽略[NotApplicable]：普通 call 没有可附着的 method receiver 链。
        return None;
    };
    let AstExpr::Var(name) = &second_call.receiver else {
        // 候选忽略[NotApplicable]：第二段 receiver 不是首句声明的直接 binding use。
        return None;
    };
    if !name_matches_binding(name, binding)
        || use_index.count_uses_in_range(second_index, second_index + 1, binding) != 1
    {
        // 候选拒绝[SemanticBarrier:EvalCount]：第二句必须恰好把同一快照用作唯一 receiver；额外 use 不能随链化消失。
        return None;
    }

    // 这里只收回“一次 method 调用立刻接下一次 method 调用”的局部壳：
    // 它本质上是 VM / HIR 为了保存中间 receiver 才拆出来的临时 local，
    // 不是源码里有意义的阶段变量。把它压回 `a:b():c()` 能明显更接近原形，
    // 同时不会放宽到普通任意调用结果的跨语句内联。
    Some(AstStmt::CallStmt(Box::new(
        crate::ast::common::AstCallStmt {
            call: AstCallKind::MethodCall(Box::new(crate::ast::common::AstMethodCallExpr {
                receiver: AstExpr::MethodCall(Box::new(first_call.clone())),
                method: second_call.method.clone(),
                args: second_call.args.clone(),
            })),
        },
    )))
}
