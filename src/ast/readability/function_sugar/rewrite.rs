//! 这个子模块是 `function_sugar` pass 的主调度器。
//!
//! 它依赖 `analysis/direct/forwarded/constructor/chain/method_alias` 已提供的局部规则，
//! 只负责按固定顺序在 block 上收敛这些 sugar，不会回头改 AST build 语义。
//! 例如：一段 `local f = function...; t.f = f` 会先在这里被路由到 forwarded 规则处理；
//! 而已经在 HIR 收成值表达式的 `obj.field(obj, ...) and ... or ...`，则会在这里继续交给
//! `method_alias` 统一判断是否值得收回 `obj:field(...)`。

use std::collections::BTreeSet;

use super::super::ReadabilityContext;
use super::analysis::{collect_method_field_names, collect_method_field_names_in_block};
use super::chain::try_chain_local_method_call_stmt;
use super::constructor::{
    try_inline_terminal_constructor_call, try_inline_terminal_constructor_fields,
};
use super::direct::lower_direct_function_stmt;
use super::forwarded::try_lower_forwarded_function_stmt;
use super::method_alias::try_recover_method_alias_stmt;
use crate::ast::common::{
    AstAssign, AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstLValue,
    AstLocalAttr, AstLocalBinding, AstLocalDecl, AstLocalOrigin, AstModule, AstNameRef, AstStmt,
    AstTableField, AstTableKey, AstTargetDialect,
};

pub(in crate::ast::readability) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    let method_fields = collect_method_field_names(module);
    rewrite_block(&mut module.body, context.target, &method_fields)
}

fn rewrite_block(
    block: &mut AstBlock,
    target: AstTargetDialect,
    method_fields: &BTreeSet<String>,
) -> bool {
    let mut changed = false;
    for stmt in &mut block.stmts {
        changed |= rewrite_nested(stmt, target, method_fields);
    }

    let old_stmts = std::mem::take(&mut block.stmts);

    // 收集互递归/前向声明组：如果某个 local-closure 声明捕获了后面才声明的 binding，
    // 该组的所有成员都不能用 `local function` 语法。
    let forward_capture_blocked = collect_forward_capture_blocked(&old_stmts);

    let mut new_stmts = Vec::with_capacity(old_stmts.len());
    let mut index = 0;
    while index < old_stmts.len() {
        if let Some((stmt, consumed)) = try_inline_terminal_constructor_fields(&old_stmts[index..])
        {
            new_stmts.push(stmt);
            changed = true;
            index += consumed;
            continue;
        }

        if let Some((stmt, consumed)) =
            try_inline_terminal_constructor_call(&old_stmts[index..], method_fields)
        {
            new_stmts.push(stmt);
            changed = true;
            index += consumed;
            continue;
        }

        if let Some((stmt, consumed)) = try_recover_method_alias_stmt(&old_stmts[index..]) {
            new_stmts.push(stmt);
            changed = true;
            index += consumed;
            continue;
        }

        if let Some((stmt, consumed)) = try_chain_local_method_call_stmt(&old_stmts[index..]) {
            new_stmts.push(stmt);
            changed = true;
            index += consumed;
            continue;
        }

        if let Some((stmt, consumed)) =
            try_lower_forwarded_function_stmt(&old_stmts[index..], target, method_fields)
        {
            new_stmts.push(stmt);
            changed = true;
            index += consumed;
            continue;
        }

        let stmt = lower_direct_function_stmt(
            old_stmts[index].clone(),
            target,
            method_fields,
            &forward_capture_blocked,
        );
        changed |= stmt != old_stmts[index];
        new_stmts.push(stmt);
        index += 1;
    }

    // 互递归组的 local 声明拆分：把 `local X = function()` 拆成
    // 先前前向声明 `local X, Y, ...`，然后赋值 `X = function()`, `Y = function()`。
    if !forward_capture_blocked.is_empty() {
        changed |= split_forward_capture_locals(&mut new_stmts, &forward_capture_blocked);
    }

    block.stmts = new_stmts;
    changed
}

fn rewrite_nested(
    stmt: &mut AstStmt,
    target: AstTargetDialect,
    method_fields: &BTreeSet<String>,
) -> bool {
    match stmt {
        AstStmt::If(if_stmt) => {
            let mut changed = rewrite_block(&mut if_stmt.then_block, target, method_fields);
            if let Some(else_block) = &mut if_stmt.else_block {
                changed |= rewrite_block(else_block, target, method_fields);
            }
            changed |= rewrite_function_exprs_in_expr(&mut if_stmt.cond, target);
            changed
        }
        AstStmt::While(while_stmt) => {
            rewrite_function_exprs_in_expr(&mut while_stmt.cond, target)
                | rewrite_block(&mut while_stmt.body, target, method_fields)
        }
        AstStmt::Repeat(repeat_stmt) => {
            rewrite_block(&mut repeat_stmt.body, target, method_fields)
                | rewrite_function_exprs_in_expr(&mut repeat_stmt.cond, target)
        }
        AstStmt::NumericFor(numeric_for) => {
            let mut changed = rewrite_function_exprs_in_expr(&mut numeric_for.start, target);
            changed |= rewrite_function_exprs_in_expr(&mut numeric_for.limit, target);
            changed |= rewrite_function_exprs_in_expr(&mut numeric_for.step, target);
            changed |= rewrite_block(&mut numeric_for.body, target, method_fields);
            changed
        }
        AstStmt::GenericFor(generic_for) => {
            let mut changed = false;
            for expr in &mut generic_for.iterator {
                changed |= rewrite_function_exprs_in_expr(expr, target);
            }
            changed |= rewrite_block(&mut generic_for.body, target, method_fields);
            changed
        }
        AstStmt::DoBlock(block) => rewrite_block(block, target, method_fields),
        AstStmt::FunctionDecl(function_decl) => {
            rewrite_function_expr(&mut function_decl.func, target)
        }
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            rewrite_function_expr(&mut local_function_decl.func, target)
        }
        AstStmt::LocalDecl(local_decl) => {
            let mut changed = false;
            for value in &mut local_decl.values {
                changed |= rewrite_function_exprs_in_expr(value, target);
            }
            changed
        }
        AstStmt::GlobalDecl(global_decl) => {
            let mut changed = false;
            for value in &mut global_decl.values {
                changed |= rewrite_function_exprs_in_expr(value, target);
            }
            changed
        }
        AstStmt::Assign(assign) => {
            let mut changed = false;
            for target_lvalue in &mut assign.targets {
                changed |= rewrite_function_exprs_in_lvalue(target_lvalue, target);
            }
            for value in &mut assign.values {
                changed |= rewrite_function_exprs_in_expr(value, target);
            }
            changed
        }
        AstStmt::CallStmt(call_stmt) => rewrite_function_exprs_in_call(&mut call_stmt.call, target),
        AstStmt::Return(ret) => {
            let mut changed = false;
            for value in &mut ret.values {
                changed |= rewrite_function_exprs_in_expr(value, target);
            }
            changed
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) | AstStmt::Error(_) => false,
    }
}

fn rewrite_function_expr(function: &mut AstFunctionExpr, target: AstTargetDialect) -> bool {
    let mut method_fields = BTreeSet::new();
    collect_method_field_names_in_block(&function.body, &mut method_fields);
    rewrite_block(&mut function.body, target, &method_fields)
}

fn rewrite_function_exprs_in_call(call: &mut AstCallKind, target: AstTargetDialect) -> bool {
    match call {
        AstCallKind::Call(call) => {
            let mut changed = rewrite_function_exprs_in_expr(&mut call.callee, target);
            for arg in &mut call.args {
                changed |= rewrite_function_exprs_in_expr(arg, target);
            }
            changed
        }
        AstCallKind::MethodCall(call) => {
            let mut changed = rewrite_function_exprs_in_expr(&mut call.receiver, target);
            for arg in &mut call.args {
                changed |= rewrite_function_exprs_in_expr(arg, target);
            }
            changed
        }
    }
}

fn rewrite_function_exprs_in_lvalue(
    target_lvalue: &mut AstLValue,
    target: AstTargetDialect,
) -> bool {
    match target_lvalue {
        AstLValue::Name(_) => false,
        AstLValue::FieldAccess(access) => rewrite_function_exprs_in_expr(&mut access.base, target),
        AstLValue::IndexAccess(access) => {
            rewrite_function_exprs_in_expr(&mut access.base, target)
                | rewrite_function_exprs_in_expr(&mut access.index, target)
        }
    }
}

fn rewrite_function_exprs_in_expr(expr: &mut AstExpr, target: AstTargetDialect) -> bool {
    match expr {
        AstExpr::FieldAccess(access) => rewrite_function_exprs_in_expr(&mut access.base, target),
        AstExpr::IndexAccess(access) => {
            rewrite_function_exprs_in_expr(&mut access.base, target)
                | rewrite_function_exprs_in_expr(&mut access.index, target)
        }
        AstExpr::Unary(unary) => rewrite_function_exprs_in_expr(&mut unary.expr, target),
        AstExpr::Binary(binary) => {
            rewrite_function_exprs_in_expr(&mut binary.lhs, target)
                | rewrite_function_exprs_in_expr(&mut binary.rhs, target)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            rewrite_function_exprs_in_expr(&mut logical.lhs, target)
                | rewrite_function_exprs_in_expr(&mut logical.rhs, target)
        }
        AstExpr::Call(call) => {
            let mut changed = rewrite_function_exprs_in_expr(&mut call.callee, target);
            for arg in &mut call.args {
                changed |= rewrite_function_exprs_in_expr(arg, target);
            }
            changed
        }
        AstExpr::MethodCall(call) => {
            let mut changed = rewrite_function_exprs_in_expr(&mut call.receiver, target);
            for arg in &mut call.args {
                changed |= rewrite_function_exprs_in_expr(arg, target);
            }
            changed
        }
        AstExpr::SingleValue(expr) => rewrite_function_exprs_in_expr(expr, target),
        AstExpr::TableConstructor(table) => {
            let mut changed = false;
            for field in &mut table.fields {
                match field {
                    AstTableField::Array(value) => {
                        changed |= rewrite_function_exprs_in_expr(value, target);
                    }
                    AstTableField::Record(record) => {
                        if let AstTableKey::Expr(key) = &mut record.key {
                            changed |= rewrite_function_exprs_in_expr(key, target);
                        }
                        changed |= rewrite_function_exprs_in_expr(&mut record.value, target);
                    }
                }
            }
            changed
        }
        AstExpr::FunctionExpr(function) => rewrite_function_expr(function, target),
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Complex { .. }
        | AstExpr::Var(_)
        | AstExpr::VarArg | AstExpr::Error(_) => false,
    }
}

/// 把互递归/前向声明组的 `local X = function()` 拆分成：
/// 先合并前向声明 `local X, Y`，然后逐个赋值 `X = function()`, `Y = function()`。
///
/// 这让 Lua 编译器能正确把 closure 的 upvalue 绑定到同一组 local 槽位。
fn split_forward_capture_locals(
    stmts: &mut Vec<AstStmt>,
    blocked: &BTreeSet<AstBindingRef>,
) -> bool {
    let mut changed = false;
    let mut i = 0;
    while i < stmts.len() {
        // 找连续的 blocked LocalDecl 组
        let group_start = i;
        let mut group_bindings = Vec::new();
        while i < stmts.len() {
            if let AstStmt::LocalDecl(local_decl) = &stmts[i]
                && local_decl.bindings.len() == 1
                && blocked.contains(&local_decl.bindings[0].id)
            {
                group_bindings.push(local_decl.bindings[0].clone());
                i += 1;
                continue;
            }
            break;
        }
        if group_bindings.len() < 2 {
            // 不足 2 个 blocked local，不需要拆分
            i = group_start + 1;
            continue;
        }
        // 构建前向声明：`local X, Y, ...`（无初始值）
        let forward_decl = AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: group_bindings
                .iter()
                .map(|b| AstLocalBinding {
                    id: b.id,
                    attr: AstLocalAttr::None,
                    origin: AstLocalOrigin::Recovered,
                })
                .collect(),
            values: Vec::new(),
        }));
        // 把每个 `local X = expr` 转成 `X = expr`
        let assignments: Vec<AstStmt> = stmts[group_start..group_start + group_bindings.len()]
            .iter()
            .map(|stmt| {
                let AstStmt::LocalDecl(local_decl) = stmt else {
                    unreachable!();
                };
                let binding_ref = local_decl.bindings[0].id;
                let lvalue = AstLValue::Name(name_ref_from_binding_ref(binding_ref));
                AstStmt::Assign(Box::new(AstAssign {
                    targets: vec![lvalue],
                    values: local_decl.values.clone(),
                }))
            })
            .collect();
        let group_len = group_bindings.len();
        // 替换原始 stmts: 移除 group，插入 forward_decl + assignments
        let mut replacement = Vec::with_capacity(1 + group_len);
        replacement.push(forward_decl);
        replacement.extend(assignments);
        stmts.splice(group_start..group_start + group_len, replacement);
        changed = true;
        // 跳过刚插入的 stmts（1 + group_len）
        i = group_start + 1 + group_len;
    }
    changed
}

fn name_ref_from_binding_ref(binding: AstBindingRef) -> AstNameRef {
    match binding {
        AstBindingRef::Local(id) => AstNameRef::Local(id),
        AstBindingRef::SyntheticLocal(id) => AstNameRef::SyntheticLocal(id),
        AstBindingRef::Temp(id) => AstNameRef::Temp(id),
    }
}

/// 从一条 stmt 中提取它声明的 local bindings 和 closure 的 captured_bindings。
fn extract_local_closure_info(
    stmt: &AstStmt,
) -> Option<(BTreeSet<AstBindingRef>, BTreeSet<AstBindingRef>)> {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            let declared: BTreeSet<AstBindingRef> =
                local_decl.bindings.iter().map(|b| b.id).collect();
            let mut captured = BTreeSet::new();
            for value in &local_decl.values {
                if let AstExpr::FunctionExpr(func) = value {
                    captured.extend(&func.captured_bindings);
                }
            }
            if captured.is_empty() {
                return None;
            }
            Some((declared, captured))
        }
        AstStmt::LocalFunctionDecl(func_decl) => {
            let declared: BTreeSet<AstBindingRef> = [func_decl.name].into_iter().collect();
            let captured = func_decl.func.captured_bindings.clone();
            if captured.is_empty() {
                return None;
            }
            Some((declared, captured))
        }
        _ => None,
    }
}

/// 收集互递归/前向声明组中所有应被禁止使用 `local function` 语法的 bindings。
///
/// 规则：如果某个 local-closure 声明 A 捕获了 block 中更后面才声明的 binding B，
/// 则 A 和 B（及 B 捕获的其他同 block local）都必须保持 `local X = function() end`
/// 形式——否则 Lua 编译器不会把它们绑定到同一个 upvalue 槽。
fn collect_forward_capture_blocked(stmts: &[AstStmt]) -> BTreeSet<AstBindingRef> {
    // 第一步：收集每条 stmt 声明的 bindings 和它的 closure captures
    let infos: Vec<Option<(BTreeSet<AstBindingRef>, BTreeSet<AstBindingRef>)>> =
        stmts.iter().map(extract_local_closure_info).collect();

    // 第二步：构建 binding→声明位置 的映射
    let mut binding_index: std::collections::HashMap<AstBindingRef, usize> =
        std::collections::HashMap::new();
    for (i, info) in infos.iter().enumerate() {
        if let Some((declared, _)) = info {
            for b in declared {
                binding_index.insert(*b, i);
            }
        }
    }

    // 第三步：找出所有前向捕获关系，把涉及的所有 binding 加入 blocked 集合
    let mut blocked = BTreeSet::new();
    for (i, info) in infos.iter().enumerate() {
        if let Some((declared, captured)) = info {
            let has_forward_capture = captured.iter().any(|cap| {
                // 排除自递归捕获（自身 binding）
                if declared.contains(cap) {
                    return false;
                }
                // 如果被捕获的 binding 在当前 stmt 之后才声明 → 前向捕获
                binding_index.get(cap).is_some_and(|&j| j > i)
            });
            if has_forward_capture {
                // 把当前声明的 bindings 和所有被前向捕获的 bindings 都加入 blocked
                blocked.extend(declared);
                for cap in captured {
                    if !declared.contains(cap) && binding_index.contains_key(cap) {
                        blocked.insert(*cap);
                    }
                }
            }
        }
    }

    blocked
}
