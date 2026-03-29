//! 这个子模块负责回收“局部别名 + method call”形成的调用链。
//!
//! 它依赖 binding-flow 已统计好的使用次数，只处理纯机械 alias 链，不会越权推断新的
//! 函数 sugar。
//! 例如：`local f = obj.m; f(obj, 1)` 会在这里尝试折回 `obj:m(1)`。

use super::super::binding_flow::{count_binding_uses_in_stmts_deep, name_matches_binding};
use crate::ast::common::{AstCallKind, AstExpr, AstLocalAttr, AstStmt};

pub(super) fn try_chain_local_method_call_stmt(stmts: &[AstStmt]) -> Option<(AstStmt, usize)> {
    let [first, second, third, ..] = stmts else {
        return try_chain_local_method_call_stmt_without_dead_alias(stmts);
    };

    let AstStmt::LocalDecl(dead_alias) = first else {
        return try_chain_local_method_call_stmt_without_dead_alias(stmts);
    };
    if dead_alias.bindings.len() != 1
        || dead_alias.values.len() != 1
        || dead_alias.bindings[0].attr != AstLocalAttr::None
    {
        return try_chain_local_method_call_stmt_without_dead_alias(stmts);
    }
    if count_binding_uses_in_stmts_deep(&stmts[1..], dead_alias.bindings[0].id) != 0 {
        return try_chain_local_method_call_stmt_without_dead_alias(stmts);
    }

    let chained = chain_local_method_call_stmt(second, third)?;
    Some((chained, 3))
}

fn try_chain_local_method_call_stmt_without_dead_alias(
    stmts: &[AstStmt],
) -> Option<(AstStmt, usize)> {
    let [first, second, ..] = stmts else {
        return None;
    };
    Some((chain_local_method_call_stmt(first, second)?, 2))
}

fn chain_local_method_call_stmt(first: &AstStmt, second: &AstStmt) -> Option<AstStmt> {
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
        || count_binding_uses_in_stmts_deep(std::slice::from_ref(second), local_decl.bindings[0].id)
            != 1
    {
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
