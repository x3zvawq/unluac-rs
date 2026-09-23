//! 这个子模块负责吸收“先放进 local，再立刻转发出去”的函数壳。
//!
//! 它依赖 binding-flow、可写 capture 快照和 capture provenance 已确认这个局部只是纯
//! 转发壳，不会越权把真正有闭包依赖的 local function 折叠掉，也不会把可变 lvalue
//! 地址的读取搬到 closure 分配之前。
//! 例如：`local f = function() ... end; t.f = f` 会在这里尝试合成 `function t.f() ... end`。
//! 删除许可先消费已有身份与 capture 事实；sink 识别借用函数，成功后才构造一次输出。

use super::super::binding_flow::{BindingUseIndex, MutableSnapshotNames};
use super::super::expr_analysis::is_stable_context_expr;
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
    mutable_snapshots: &MutableSnapshotNames,
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
    // 先复核删除许可，避免为必须保留的 local 身份复制函数。
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
    if !local_binding.rewrite_authority.may_remove_binding() {
        // 候选拒绝[LayerBoundary]：HIR 已要求保留该 binding；函数转发 sugar 只能判断
        // Lua 语法形状，不能推翻底层生命周期或 value-epoch 结论。
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
        // 候选拒绝[SemanticBarrier:EvalCount]：转发 sink 必须是唯一读取；额外读取仍需共享同一个 closure 对象，反例见 regress_333。
        return None;
    }
    let stmt = inline_function_into_stmt(next, binding, function, target, mutable_snapshots)?;
    Some((stmt, 2))
}

fn inline_function_into_stmt(
    stmt: &AstStmt,
    binding: AstBindingRef,
    function: &AstFunctionExpr,
    target: AstTargetDialect,
    mutable_snapshots: &MutableSnapshotNames,
) -> Option<AstStmt> {
    match stmt {
        AstStmt::GlobalDecl(global_decl)
            if global_decl.bindings.len() == 1 && global_decl.values.len() == 1 =>
        {
            let AstExpr::Var(name) = &global_decl.values[0] else {
                return None;
            };
            if !binding.matches_name_ref(name) {
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
                    global_declaration: true,
                    func: function.clone(),
                })));
            }

            let mut global_decl = global_decl.as_ref().clone();
            global_decl.values[0] = AstExpr::FunctionExpr(Box::new(function.clone()));
            Some(AstStmt::GlobalDecl(Box::new(global_decl)))
        }
        AstStmt::Assign(assign) if assign.targets.len() == 1 && assign.values.len() == 1 => {
            let AstExpr::Var(name) = &assign.values[0] else {
                return None;
            };
            if !binding.matches_name_ref(name) {
                return None;
            }
            let target_name = function_decl_target_from_lvalue(&assign.targets[0]);
            // Luau 的具名函数声明先创建闭包再求目标，与当前转发序列相同；
            // 普通赋值仍先求 lvalue，不能把该许可传给无法使用声明语法的目标。
            let preserves_closure_first =
                target.version == crate::decompile::DecompileDialect::Luau && target_name.is_some();
            if !preserves_closure_first
                && !lvalue_prefix_can_move_before_closure(&assign.targets[0], mutable_snapshots)
            {
                // 候选拒绝[SemanticBarrier:EvalOrder]：转发会把 lvalue 的地址求值
                // 搬到 closure 分配之前；lookup、global 读取或其它运行时事件可观察到
                // 相反顺序，反例见 regress_401。
                return None;
            }
            if let Some(target_name) = target_name {
                return Some(AstStmt::FunctionDecl(Box::new(AstFunctionDecl {
                    target: target_name,
                    global_declaration: false,
                    func: function.clone(),
                })));
            }

            let mut assign = assign.as_ref().clone();
            assign.values[0] = AstExpr::FunctionExpr(Box::new(function.clone()));
            Some(AstStmt::Assign(Box::new(assign)))
        }
        _ => None,
    }
}

pub(super) fn lvalue_prefix_can_move_before_closure(
    target: &AstLValue,
    mutable_snapshots: &MutableSnapshotNames,
) -> bool {
    match target {
        AstLValue::Name(_) => true,
        AstLValue::FieldAccess(access) => is_stable_context_expr(&access.base, mutable_snapshots),
        AstLValue::IndexAccess(access) => {
            is_stable_context_expr(&access.base, mutable_snapshots)
                && is_stable_context_expr(&access.index, mutable_snapshots)
        }
    }
}
