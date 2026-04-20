//! 这个 pass 负责消除 “参数槽位被前层 SSA-merge 拆出来的 local 别名”。
//!
//! 背景：当函数参数 `x` 在分支里被条件改写、merge 点又只有一个 reaching def 时，
//! 前层为了给 phi 起一个稳定名字，会在函数入口插入 `t1 = p0` 拷贝；`locals` pass
//! 再把 `t1` 升格成 `local l0 = p0`。整体形状变成：
//!     local l0 = p0
//!     if cond then l0 = ... end
//!     return l0
//! 而原始 Lua 源码其实就是直接改写参数 `x`。
//!
//! 由于字节码层面这两个槽位是同一个，把别名局部 `l0` 重命名回参数 `p0` 不会改变
//! 语义。我们在这里只处理一种非常窄的形状：
//!   - 函数体首条语句是 `local L = Var(Param(P))`
//!   - L 是普通 `Local`（非 const/close、非 Temp/SyntheticLocal）
//!   - L 没有被任何嵌套闭包通过 `captured_bindings` 抓走
//!
//! 满足时，把 body 里所有 `Var(Local(L))` 重写成 `Var(Param(P))`，
//! 所有 `LValue::Name(Local(L))` 重写成 `LValue::Name(Param(P))`，并丢掉首条 alias 声明。
//!
//! 输入形状 -> 输出形状：
//!   function(p0)                       function(p0)
//!     local l0 = p0                       if p0 > 0 then
//!     if p0 > 0 then           ====>          p0 = p0 + 1
//!       l0 = p0 + 1                       end
//!     end                                 return p0
//!     return l0                         end
//!   end

use super::super::common::{
    AstAssign, AstBlock, AstExpr, AstFunctionExpr, AstLValue, AstLocalAttr, AstLocalDecl,
    AstModule, AstNameRef, AstStmt, AstTableField, AstTableKey,
};
use super::ReadabilityContext;
use super::walk::{self, AstRewritePass, BlockKind};
use crate::ast::common::AstBindingRef;
use crate::hir::{LocalId, ParamId};
use crate::ast::traverse::{
    traverse_call_children, traverse_expr_children, traverse_lvalue_children,
    traverse_stmt_children,
};

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    let _ = context.target;
    walk::rewrite_module(module, &mut ParamAliasCoalescePass)
}

struct ParamAliasCoalescePass;

impl AstRewritePass for ParamAliasCoalescePass {
    fn rewrite_block(&mut self, block: &mut AstBlock, kind: BlockKind) -> bool {
        if !matches!(kind, BlockKind::FunctionBody) {
            return false;
        }
        let Some((local_id, param_id)) = match_param_alias_first_stmt(block) else {
            return false;
        };
        // 跳过前置 alias 声明，扫描“余下 body”。
        let rest = &block.stmts[1..];
        if any_closure_captures_local(rest, local_id) {
            return false;
        }
        // 安全条件：参数 P 不能在 L 已经被写过之后还被读取，否则会把
        // “参数原值”和“被改写后的 L 值”混淆。例如下面这种形状必须拒绝：
        //   local acc = seed
        //   acc = mutate_loop(...)
        //   print(seed, acc)        -- 这里 seed 仍然是原值，acc 已经变了
        if !rest_reads_of_param_safe_against_writes_of_local(rest, local_id, param_id) {
            return false;
        }
        // 额外限制：L 不能在任何 for/while/repeat 循环体内被写入。把循环里的
        // 累积写改写成对参数槽位的写，会让 round-1 重新反编译时丢失累加器形态
        // （lifter 难以从“被改写过的参数”恢复 phi 入口），导致 regen 输出无法运行。
        if any_local_write_inside_loop(rest, local_id) {
            return false;
        }
        let mut tail = block.stmts.split_off(1);
        rename_local_to_param_in_stmts(&mut tail, local_id, param_id);
        block.stmts.append(&mut tail);
        block.stmts.remove(0);
        true
    }
}

fn match_param_alias_first_stmt(block: &AstBlock) -> Option<(LocalId, ParamId)> {
    let first = block.stmts.first()?;
    let AstStmt::LocalDecl(local_decl) = first else {
        return None;
    };
    let local_id = single_plain_local_binding(local_decl)?;
    let [value] = local_decl.values.as_slice() else {
        return None;
    };
    let AstExpr::Var(AstNameRef::Param(param_id)) = value else {
        return None;
    };
    Some((local_id, *param_id))
}

fn single_plain_local_binding(local_decl: &AstLocalDecl) -> Option<LocalId> {
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    if binding.attr != AstLocalAttr::None {
        return None;
    }
    match binding.id {
        AstBindingRef::Local(id) => Some(id),
        _ => None,
    }
}

// === 闭包捕获扫描 =========================================================

fn any_closure_captures_local(stmts: &[AstStmt], local: LocalId) -> bool {
    stmts.iter().any(|stmt| stmt_has_closure_capturing_local(stmt, local))
}

fn block_has_closure_capturing_local(block: &AstBlock, local: LocalId) -> bool {
    any_closure_captures_local(&block.stmts, local)
}

fn stmt_has_closure_capturing_local(stmt: &AstStmt, local: LocalId) -> bool {
    let mut found = false;
    traverse_stmt_children!(
        stmt,
        iter = iter,
        opt = as_ref,
        borrow = [&],
        expr(expr) => { if expr_has_closure_capturing_local(expr, local) { found = true; } },
        lvalue(lvalue) => { if lvalue_has_closure_capturing_local(lvalue, local) { found = true; } },
        block(block) => { if block_has_closure_capturing_local(block, local) { found = true; } },
        function(function) => { if function_captures_or_inner_captures(function, local) { found = true; } },
        condition(cond) => { if expr_has_closure_capturing_local(cond, local) { found = true; } },
        call(call) => { if call_has_closure_capturing_local(call, local) { found = true; } }
    );
    found
}

fn expr_has_closure_capturing_local(expr: &AstExpr, local: LocalId) -> bool {
    let mut found = false;
    traverse_expr_children!(
        expr,
        iter = iter,
        borrow = [&],
        expr(child) => { if expr_has_closure_capturing_local(child, local) { found = true; } },
        function(function) => { if function_captures_or_inner_captures(function, local) { found = true; } }
    );
    found
}

fn lvalue_has_closure_capturing_local(lvalue: &AstLValue, local: LocalId) -> bool {
    let mut found = false;
    traverse_lvalue_children!(
        lvalue,
        borrow = [&],
        expr(child) => { if expr_has_closure_capturing_local(child, local) { found = true; } }
    );
    found
}

fn call_has_closure_capturing_local(call: &crate::ast::common::AstCallKind, local: LocalId) -> bool {
    let mut found = false;
    traverse_call_children!(
        call,
        iter = iter,
        borrow = [&],
        expr(child) => { if expr_has_closure_capturing_local(child, local) { found = true; } }
    );
    found
}

fn function_captures_or_inner_captures(function: &AstFunctionExpr, local: LocalId) -> bool {
    if function
        .captured_bindings
        .contains(&AstBindingRef::Local(local))
    {
        return true;
    }
    // 嵌套闭包内部如果出现进一步的闭包捕获了该 local，也要保守拒绝。
    block_has_closure_capturing_local(&function.body, local)
}

// === “P 读取必须先于 L 写入” 安全检查 ====================================
//
// 我们按 stmt 顺序扫描余下 body：每条语句既看作“是否读取 P”，又看作“是否写入 L”。
// 一旦在某条 stmt 之前已经出现过 L 的写入，再有任何 P 读取就拒绝；同一条 stmt 内
// 同时读 P 和写 L 是安全的（cond/RHS 总是在赋值前求值）。
fn rest_reads_of_param_safe_against_writes_of_local(
    stmts: &[AstStmt],
    local: LocalId,
    param: ParamId,
) -> bool {
    let mut seen_local_write = false;
    for stmt in stmts {
        let writes_local = stmt_writes_local(stmt, local);
        let reads_param = stmt_reads_param(stmt, param);
        if reads_param && seen_local_write {
            return false;
        }
        if writes_local {
            seen_local_write = true;
        }
    }
    true
}

fn stmt_writes_local(stmt: &AstStmt, local: LocalId) -> bool {
    let mut found = false;
    traverse_stmt_children!(
        stmt,
        iter = iter,
        opt = as_ref,
        borrow = [&],
        expr(_e) => { /* expressions don't write */ },
        lvalue(lvalue) => { if lvalue_writes_local(lvalue, local) { found = true; } },
        block(block) => { if block_writes_local(block, local) { found = true; } },
        function(_function) => { /* 嵌套函数体里的 LocalId 属于子作用域，不算父 L 的写入 */ },
        condition(_c) => { /* condition 是表达式，不写 */ },
        call(_c) => { /* call 表达式不直接写 lvalue */ }
    );
    found
}

fn block_writes_local(block: &AstBlock, local: LocalId) -> bool {
    block.stmts.iter().any(|s| stmt_writes_local(s, local))
}

fn lvalue_writes_local(lvalue: &AstLValue, local: LocalId) -> bool {
    matches!(lvalue, AstLValue::Name(AstNameRef::Local(id)) if *id == local)
}

// 检查 L 是否在 stmts 中的任何循环体内被写入。
fn any_local_write_inside_loop(stmts: &[AstStmt], local: LocalId) -> bool {
    stmts.iter().any(|s| stmt_has_local_write_inside_loop(s, local))
}

fn stmt_has_local_write_inside_loop(stmt: &AstStmt, local: LocalId) -> bool {
    match stmt {
        AstStmt::While(while_stmt) => block_writes_local(&while_stmt.body, local),
        AstStmt::Repeat(repeat_stmt) => block_writes_local(&repeat_stmt.body, local),
        AstStmt::NumericFor(numeric_for) => block_writes_local(&numeric_for.body, local),
        AstStmt::GenericFor(generic_for) => block_writes_local(&generic_for.body, local),
        AstStmt::If(if_stmt) => {
            any_local_write_inside_loop(&if_stmt.then_block.stmts, local)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(|b| any_local_write_inside_loop(&b.stmts, local))
        }
        AstStmt::DoBlock(block) => any_local_write_inside_loop(&block.stmts, local),
        _ => false,
    }
}

fn stmt_reads_param(stmt: &AstStmt, param: ParamId) -> bool {
    let mut found = false;
    traverse_stmt_children!(
        stmt,
        iter = iter,
        opt = as_ref,
        borrow = [&],
        expr(expr) => { if expr_reads_param(expr, param) { found = true; } },
        lvalue(lvalue) => { if lvalue_reads_param(lvalue, param) { found = true; } },
        block(block) => { if block_reads_param(block, param) { found = true; } },
        function(_function) => { /* 嵌套函数对父参数的读取走的是 upvalue，不属于此 ParamId */ },
        condition(cond) => { if expr_reads_param(cond, param) { found = true; } },
        call(call) => { if call_reads_param(call, param) { found = true; } }
    );
    found
}

fn block_reads_param(block: &AstBlock, param: ParamId) -> bool {
    block.stmts.iter().any(|s| stmt_reads_param(s, param))
}

fn expr_reads_param(expr: &AstExpr, param: ParamId) -> bool {
    if let AstExpr::Var(AstNameRef::Param(id)) = expr
        && *id == param
    {
        return true;
    }
    let mut found = false;
    traverse_expr_children!(
        expr,
        iter = iter,
        borrow = [&],
        expr(child) => { if expr_reads_param(child, param) { found = true; } },
        function(_function) => { /* 子函数体内的同名 ParamId 属于子作用域，不算 */ }
    );
    found
}

fn lvalue_reads_param(lvalue: &AstLValue, param: ParamId) -> bool {
    let mut found = false;
    traverse_lvalue_children!(
        lvalue,
        borrow = [&],
        expr(child) => { if expr_reads_param(child, param) { found = true; } }
    );
    found
}

fn call_reads_param(call: &crate::ast::common::AstCallKind, param: ParamId) -> bool {
    let mut found = false;
    traverse_call_children!(
        call,
        iter = iter,
        borrow = [&],
        expr(child) => { if expr_reads_param(child, param) { found = true; } }
    );
    found
}

// === 重命名 ==============================================================

fn rename_local_to_param_in_stmts(stmts: &mut [AstStmt], from: LocalId, to: ParamId) {
    for stmt in stmts {
        rename_local_to_param_in_stmt(stmt, from, to);
    }
}

fn rename_local_to_param_in_stmt(stmt: &mut AstStmt, from: LocalId, to: ParamId) {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            for value in &mut local_decl.values {
                rename_local_to_param_in_expr(value, from, to);
            }
        }
        AstStmt::GlobalDecl(global_decl) => {
            for value in &mut global_decl.values {
                rename_local_to_param_in_expr(value, from, to);
            }
        }
        AstStmt::Assign(assign) => rename_local_to_param_in_assign(assign, from, to),
        AstStmt::CallStmt(call_stmt) => {
            rename_local_to_param_in_call_kind(&mut call_stmt.call, from, to);
        }
        AstStmt::Return(ret) => {
            for value in &mut ret.values {
                rename_local_to_param_in_expr(value, from, to);
            }
        }
        AstStmt::If(if_stmt) => {
            rename_local_to_param_in_expr(&mut if_stmt.cond, from, to);
            rename_local_to_param_in_stmts(&mut if_stmt.then_block.stmts, from, to);
            if let Some(else_block) = &mut if_stmt.else_block {
                rename_local_to_param_in_stmts(&mut else_block.stmts, from, to);
            }
        }
        AstStmt::While(while_stmt) => {
            rename_local_to_param_in_expr(&mut while_stmt.cond, from, to);
            rename_local_to_param_in_stmts(&mut while_stmt.body.stmts, from, to);
        }
        AstStmt::Repeat(repeat_stmt) => {
            rename_local_to_param_in_stmts(&mut repeat_stmt.body.stmts, from, to);
            rename_local_to_param_in_expr(&mut repeat_stmt.cond, from, to);
        }
        AstStmt::NumericFor(numeric_for) => {
            rename_local_to_param_in_expr(&mut numeric_for.start, from, to);
            rename_local_to_param_in_expr(&mut numeric_for.limit, from, to);
            rename_local_to_param_in_expr(&mut numeric_for.step, from, to);
            rename_local_to_param_in_stmts(&mut numeric_for.body.stmts, from, to);
        }
        AstStmt::GenericFor(generic_for) => {
            for expr in &mut generic_for.iterator {
                rename_local_to_param_in_expr(expr, from, to);
            }
            rename_local_to_param_in_stmts(&mut generic_for.body.stmts, from, to);
        }
        AstStmt::DoBlock(block) => rename_local_to_param_in_stmts(&mut block.stmts, from, to),
        AstStmt::FunctionDecl(_)
        | AstStmt::LocalFunctionDecl(_)
        | AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_)
        | AstStmt::Error(_) => {}
    }
}

fn rename_local_to_param_in_call_kind(
    call: &mut crate::ast::common::AstCallKind,
    from: LocalId,
    to: ParamId,
) {
    match call {
        crate::ast::common::AstCallKind::Call(call_expr) => {
            rename_local_to_param_in_expr(&mut call_expr.callee, from, to);
            for arg in &mut call_expr.args {
                rename_local_to_param_in_expr(arg, from, to);
            }
        }
        crate::ast::common::AstCallKind::MethodCall(call_expr) => {
            rename_local_to_param_in_expr(&mut call_expr.receiver, from, to);
            for arg in &mut call_expr.args {
                rename_local_to_param_in_expr(arg, from, to);
            }
        }
    }
}

fn rename_local_to_param_in_assign(assign: &mut AstAssign, from: LocalId, to: ParamId) {
    for target in &mut assign.targets {
        rename_local_to_param_in_lvalue(target, from, to);
    }
    for value in &mut assign.values {
        rename_local_to_param_in_expr(value, from, to);
    }
}

fn rename_local_to_param_in_lvalue(lvalue: &mut AstLValue, from: LocalId, to: ParamId) {
    match lvalue {
        AstLValue::Name(name) => {
            if matches!(name, AstNameRef::Local(id) if *id == from) {
                *name = AstNameRef::Param(to);
            }
        }
        AstLValue::FieldAccess(access) => rename_local_to_param_in_expr(&mut access.base, from, to),
        AstLValue::IndexAccess(access) => {
            rename_local_to_param_in_expr(&mut access.base, from, to);
            rename_local_to_param_in_expr(&mut access.index, from, to);
        }
    }
}

fn rename_local_to_param_in_expr(expr: &mut AstExpr, from: LocalId, to: ParamId) {
    match expr {
        AstExpr::Var(name) => {
            if matches!(name, AstNameRef::Local(id) if *id == from) {
                *name = AstNameRef::Param(to);
            }
        }
        AstExpr::FieldAccess(access) => {
            rename_local_to_param_in_expr(&mut access.base, from, to);
        }
        AstExpr::IndexAccess(access) => {
            rename_local_to_param_in_expr(&mut access.base, from, to);
            rename_local_to_param_in_expr(&mut access.index, from, to);
        }
        AstExpr::Unary(unary) => rename_local_to_param_in_expr(&mut unary.expr, from, to),
        AstExpr::Binary(binary) => {
            rename_local_to_param_in_expr(&mut binary.lhs, from, to);
            rename_local_to_param_in_expr(&mut binary.rhs, from, to);
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            rename_local_to_param_in_expr(&mut logical.lhs, from, to);
            rename_local_to_param_in_expr(&mut logical.rhs, from, to);
        }
        AstExpr::Call(call) => {
            rename_local_to_param_in_expr(&mut call.callee, from, to);
            for arg in &mut call.args {
                rename_local_to_param_in_expr(arg, from, to);
            }
        }
        AstExpr::MethodCall(call) => {
            rename_local_to_param_in_expr(&mut call.receiver, from, to);
            for arg in &mut call.args {
                rename_local_to_param_in_expr(arg, from, to);
            }
        }
        AstExpr::SingleValue(inner) => rename_local_to_param_in_expr(inner, from, to),
        AstExpr::TableConstructor(table) => {
            for field in &mut table.fields {
                match field {
                    AstTableField::Array(value) => rename_local_to_param_in_expr(value, from, to),
                    AstTableField::Record(record) => {
                        if let AstTableKey::Expr(key) = &mut record.key {
                            rename_local_to_param_in_expr(key, from, to);
                        }
                        rename_local_to_param_in_expr(&mut record.value, from, to);
                    }
                }
            }
        }
        AstExpr::FunctionExpr(_)
        | AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Complex { .. }
        | AstExpr::VarArg
        | AstExpr::Error(_) => {
            // 不进入嵌套函数体：那里 LocalId 属于父作用域，但子作用域只能通过 upvalue
            // 引用它。`captured_bindings` 检查已经把这种情况否决，剩下的引用都不应该
            // 出现在子函数 body 里。
        }
    }
}
