//! 这个子模块负责吸收“先放进 local，再立刻转发出去”的函数壳。
//!
//! 它依赖 binding-flow 和 capture provenance 已确认这个局部只是纯转发壳，不会越权把
//! 真正有闭包依赖的 local function 折叠掉。
//! 例如：`local f = function() ... end; t.f = f` 会在这里尝试合成 `function t.f() ... end`。

use super::super::binding_flow::BindingUseIndex;
use super::super::binding_ref::name_matches_binding;
use super::super::expr_analysis::is_context_safe_expr;
use super::direct::function_decl_target_from_lvalue;
use crate::ast::common::{
    AstBindingRef, AstExpr, AstFunctionDecl, AstFunctionExpr, AstGlobalBindingTarget, AstLValue,
    AstLocalAttr, AstNamePath, AstNameRef, AstStmt, AstTargetDialect,
};

pub(super) fn try_lower_forwarded_function_stmt(
    stmts: &[AstStmt],
    use_index: &BindingUseIndex,
    stmt_base: usize,
    target: AstTargetDialect,
) -> Option<(AstStmt, usize)> {
    let [AstStmt::LocalDecl(local_decl), next, ..] = stmts else {
        return None;
    };
    if local_decl.bindings.len() != 1 || local_decl.values.len() != 1 {
        return None;
    }
    let local_binding = &local_decl.bindings[0];
    let binding = local_binding.id;
    let AstExpr::FunctionExpr(function) = &local_decl.values[0] else {
        return None;
    };
    let stmt = inline_function_into_stmt(next, binding, function.as_ref().clone(), target)?;

    // 精确转发 sink 已经形成；从这里开始的退出才会拒绝真实候选。
    match local_binding.attr {
        AstLocalAttr::None => {}
        AstLocalAttr::Close => {
            // 候选拒绝[SemanticBarrier:Lifetime]：删除 `<close>` 转发壳会同时删除离域关闭动作，反例形状见 regress_415。
            return None;
        }
        AstLocalAttr::Const => {
            // 候选拒绝[PolicyBoundary]：项目选择在函数糖中保留显式 `<const>` 声明身份。
            return None;
        }
    }
    if local_binding.origin.is_debug_hinted() {
        // 候选拒绝[SemanticBarrier:DebugScope]：删除 DebugHinted 转发壳会抹掉 debug.getlocal 可见的名字与区间，反例见 regress_333。
        return None;
    }
    if local_binding.origin.is_physical_root() {
        // 候选拒绝[SemanticBarrier:Lifetime]：转发后的函数对象不能替代原槽承担词法域末端前的强根生命周期，反例形状见 regress_400。
        return None;
    }
    // 只有“纯转发”的函数壳才适合被下一条语句吸收。
    // 递归 local function 这类 case 在 AST 函数体里往往已经只剩 `u0` 之类的 upvalue 引用，
    // 直接扫 body 看不到它对当前 binding 槽位的依赖；所以这里优先使用 AST build
    // 带下来的 capture provenance，确认这个局部槽位是不是闭包初始化的一部分。
    if function.captured_bindings.contains(&binding) {
        // 候选拒绝[SemanticBarrier:Capture]：递归闭包依赖这个 local 槽；删除声明会改变自引用 binding，反例见 regress_26。
        return None;
    }
    if use_index.count_uses_in_suffix(stmt_base + 1, binding) != 1 {
        // 候选拒绝[SemanticBarrier:EvalCount]：精确 sink 已读取一次；额外读取仍需共享同一个 closure 对象，反例见 regress_333。
        return None;
    }
    Some((stmt, 2))
}

fn inline_function_into_stmt(
    stmt: &AstStmt,
    binding: AstBindingRef,
    function: AstFunctionExpr,
    target: AstTargetDialect,
) -> Option<AstStmt> {
    match stmt {
        AstStmt::GlobalDecl(global_decl)
            if global_decl.bindings.len() == 1 && global_decl.values.len() == 1 =>
        {
            let AstExpr::Var(name) = &global_decl.values[0] else {
                return None;
            };
            if !name_matches_binding(name, binding) {
                return None;
            }
            if global_decl.bindings[0].attr == crate::ast::common::AstGlobalAttr::None
                && target.caps.global_decl
            {
                let AstGlobalBindingTarget::Name(name) = &global_decl.bindings[0].target else {
                    return None;
                };
                return Some(AstStmt::FunctionDecl(Box::new(AstFunctionDecl {
                    target: crate::ast::common::AstFunctionName::Plain(AstNamePath {
                        root: AstNameRef::Global(name.clone()),
                        fields: Vec::new(),
                    }),
                    func: function,
                })));
            }

            let mut global_decl = global_decl.as_ref().clone();
            global_decl.values[0] = AstExpr::FunctionExpr(Box::new(function));
            Some(AstStmt::GlobalDecl(Box::new(global_decl)))
        }
        AstStmt::Assign(assign) if assign.targets.len() == 1 && assign.values.len() == 1 => {
            let AstExpr::Var(name) = &assign.values[0] else {
                return None;
            };
            if !name_matches_binding(name, binding) {
                return None;
            }
            if !lvalue_prefix_can_move_before_closure(&assign.targets[0]) {
                // 候选拒绝[SemanticBarrier:EvalOrder]：转发会把 lvalue 的地址求值
                // 搬到 closure 分配之前；lookup、global 读取或其它运行时事件可观察到
                // 相反顺序，反例见 regress_401。
                return None;
            }
            if let Some((target_name, function)) =
                function_decl_target_from_lvalue(&assign.targets[0], &function, target)
            {
                return Some(AstStmt::FunctionDecl(Box::new(AstFunctionDecl {
                    target: target_name,
                    func: function,
                })));
            }

            let mut assign = assign.as_ref().clone();
            assign.values[0] = AstExpr::FunctionExpr(Box::new(function));
            Some(AstStmt::Assign(Box::new(assign)))
        }
        _ => None,
    }
}

fn lvalue_prefix_can_move_before_closure(target: &AstLValue) -> bool {
    match target {
        AstLValue::Name(_) => true,
        AstLValue::FieldAccess(access) => is_context_safe_expr(&access.base),
        AstLValue::IndexAccess(access) => {
            is_context_safe_expr(&access.base) && is_context_safe_expr(&access.index)
        }
    }
}
