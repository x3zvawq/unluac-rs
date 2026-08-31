//! 这个子模块负责回收“局部别名 + method call”形成的调用链。
//!
//! 它依赖 binding-flow 已统计好的使用次数，只处理纯机械 alias 链，不会越权推断新的
//! 函数 sugar。
//! 例如：`local f = obj.m; f(obj, 1)` 会在这里尝试折回 `obj:m(1)`。

use super::super::binding_flow::BindingUseIndex;
use super::super::binding_ref::name_matches_binding;
use super::super::expr_analysis::is_discard_safe_expr;
use crate::ast::common::{AstBindingRef, AstCallKind, AstExpr, AstLocalAttr, AstStmt};

pub(super) fn try_chain_local_method_call_stmt(
    stmts: &[AstStmt],
    use_index: &BindingUseIndex,
    stmt_base: usize,
) -> Option<(AstStmt, usize)> {
    let [first, second, third, ..] = stmts else {
        return try_chain_local_method_call_stmt_without_dead_alias(stmts, use_index, stmt_base);
    };

    let AstStmt::LocalDecl(dead_alias) = first else {
        return try_chain_local_method_call_stmt_without_dead_alias(stmts, use_index, stmt_base);
    };
    if dead_alias.bindings.len() != 1
        || dead_alias.values.len() != 1
        || dead_alias.bindings[0].attr != AstLocalAttr::None
    {
        return try_chain_local_method_call_stmt_without_dead_alias(stmts, use_index, stmt_base);
    }
    if use_index.count_uses_in_suffix(stmt_base + 1, dead_alias.bindings[0].id) != 0 {
        // 候选拒绝[SemanticBarrier:Scope]：所谓 dead alias 仍有后续引用，删除会留下未绑定 use。
        return try_chain_local_method_call_stmt_without_dead_alias(stmts, use_index, stmt_base);
    }
    if !is_discard_safe_expr(&dead_alias.values[0]) {
        // 候选拒绝[SemanticBarrier:EvalCount]：`local dead=f()` 即使结果未用也必须执行调用；只有无事件表达式可删除。
        return try_chain_local_method_call_stmt_without_dead_alias(stmts, use_index, stmt_base);
    }
    // 证明缺陷[PotentialPolicyViolation]：dead alias 的 DebugHinted origin 未检查；即使 RHS 可安全丢弃，也不应无证据抹掉源码身份。

    let chained_binding = single_method_call_local_binding(second)?;
    if use_index.count_uses_in_suffix(stmt_base + 3, chained_binding) != 0 {
        // 候选拒绝[SemanticBarrier:Lifetime]：链中间值在第二次调用后仍被读取，压入 receiver 会删除该共享 local。
        return try_chain_local_method_call_stmt_without_dead_alias(stmts, use_index, stmt_base);
    }

    let chained = chain_local_method_call_stmt(second, third, use_index, stmt_base + 2)?;
    Some((chained, 3))
}

fn try_chain_local_method_call_stmt_without_dead_alias(
    stmts: &[AstStmt],
    use_index: &BindingUseIndex,
    stmt_base: usize,
) -> Option<(AstStmt, usize)> {
    let [first, second, ..] = stmts else {
        return None;
    };
    let chained_binding = single_method_call_local_binding(first)?;
    if use_index.count_uses_in_suffix(stmt_base + 2, chained_binding) != 0 {
        // 候选拒绝[SemanticBarrier:Lifetime]：`local x=a:b(); x:c(); use(x)` 不能压成链后删除仍存活的 `x`。
        return None;
    }
    Some((
        chain_local_method_call_stmt(first, second, use_index, stmt_base + 1)?,
        2,
    ))
}

fn single_method_call_local_binding(stmt: &AstStmt) -> Option<AstBindingRef> {
    let AstStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    if local_decl.bindings.len() != 1
        || local_decl.values.len() != 1
        || local_decl.bindings[0].attr != AstLocalAttr::None
    {
        return None;
    }
    if !matches!(local_decl.values[0], AstExpr::MethodCall(_)) {
        return None;
    }
    // 证明缺陷[PotentialUnsoundness:Lifetime]：这里只检查 attr，未拒绝 PhysicalRoot；链化会把原本活到 block 末的 local 提前释放，弱表/`__gc` 可观察。
    // 证明缺陷[PotentialPolicyViolation]：DebugHinted 的源码身份也会被无条件删去。
    Some(local_decl.bindings[0].id)
}

fn chain_local_method_call_stmt(
    first: &AstStmt,
    second: &AstStmt,
    use_index: &BindingUseIndex,
    second_index: usize,
) -> Option<AstStmt> {
    let AstStmt::LocalDecl(local_decl) = first else {
        return None;
    };
    if local_decl.bindings.len() != 1
        || local_decl.values.len() != 1
        || local_decl.bindings[0].attr != AstLocalAttr::None
    {
        return None;
    }
    let AstExpr::MethodCall(first_call) = &local_decl.values[0] else {
        return None;
    };
    let AstStmt::CallStmt(call_stmt) = second else {
        return None;
    };
    let AstCallKind::MethodCall(second_call) = &call_stmt.call else {
        return None;
    };
    let AstExpr::Var(name) = &second_call.receiver else {
        return None;
    };
    if !name_matches_binding(name, local_decl.bindings[0].id)
        || use_index.count_uses_in_range(second_index, second_index + 1, local_decl.bindings[0].id)
            != 1
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
                receiver: AstExpr::MethodCall(first_call.clone()),
                method: second_call.method.clone(),
                args: second_call.args.clone(),
            })),
        },
    )))
}
