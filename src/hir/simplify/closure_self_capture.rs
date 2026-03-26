//! 这个文件负责把递归闭包初始化里残留的“自引用 temp”认回真实 binding。
//!
//! Lua 会先为递归局部函数准备一个自引用槽位，再把 closure 本体写回这个槽位。
//! HIR lowering 里这条关系最初只能安全地表示成一个 `TempRef` capture；如果后面不把它
//! 收回真实 binding，Naming/AST 只能把它当普通 upvalue，最终就会输出成 `u0(...)`。
//!
//! 这里不做宽泛猜测，只处理一个非常窄的结构：
//! - closure 直接作为某个 local/assign 的初始化值
//! - capture 里出现了一个在当前 proto 里从未被任何语句显式定义过的 temp
//!
//! 这种“悬空 temp”正是递归 self slot 在 HIR 里的残影，把它改写成当前初始化目标，
//! 后面的 AST/Readability/Naming 就都能看到稳定的绑定身份。

use std::collections::BTreeSet;

use crate::hir::common::{HirBlock, HirExpr, HirLValue, HirProto, HirStmt, TempId};

pub(super) fn resolve_recursive_closure_self_captures_in_proto(proto: &mut HirProto) -> bool {
    let defined_temps = collect_defined_temps(&proto.body);
    rewrite_block(&mut proto.body, &defined_temps)
}

fn rewrite_block(block: &mut HirBlock, defined_temps: &BTreeSet<TempId>) -> bool {
    let mut changed = false;
    for stmt in &mut block.stmts {
        changed |= rewrite_nested(stmt, defined_temps);
        changed |= rewrite_stmt_self_captures(stmt, defined_temps);
    }
    changed
}

fn rewrite_nested(stmt: &mut HirStmt, defined_temps: &BTreeSet<TempId>) -> bool {
    match stmt {
        HirStmt::If(if_stmt) => {
            let mut changed = rewrite_block(&mut if_stmt.then_block, defined_temps);
            if let Some(else_block) = &mut if_stmt.else_block {
                changed |= rewrite_block(else_block, defined_temps);
            }
            changed
        }
        HirStmt::While(while_stmt) => rewrite_block(&mut while_stmt.body, defined_temps),
        HirStmt::Repeat(repeat_stmt) => rewrite_block(&mut repeat_stmt.body, defined_temps),
        HirStmt::NumericFor(numeric_for) => rewrite_block(&mut numeric_for.body, defined_temps),
        HirStmt::GenericFor(generic_for) => rewrite_block(&mut generic_for.body, defined_temps),
        HirStmt::Block(block) => rewrite_block(block, defined_temps),
        HirStmt::Unstructured(unstructured) => rewrite_block(&mut unstructured.body, defined_temps),
        HirStmt::LocalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => false,
    }
}

fn rewrite_stmt_self_captures(stmt: &mut HirStmt, defined_temps: &BTreeSet<TempId>) -> bool {
    match stmt {
        HirStmt::LocalDecl(local_decl)
            if local_decl.bindings.len() == 1 && local_decl.values.len() == 1 =>
        {
            rewrite_closure_self_captures(
                &mut local_decl.values[0],
                HirExpr::LocalRef(local_decl.bindings[0]),
                defined_temps,
            )
        }
        HirStmt::Assign(assign) if assign.targets.len() == 1 && assign.values.len() == 1 => {
            let Some(binding_expr) = lvalue_as_expr(&assign.targets[0]) else {
                return false;
            };
            rewrite_closure_self_captures(&mut assign.values[0], binding_expr, defined_temps)
        }
        _ => false,
    }
}

fn rewrite_closure_self_captures(
    expr: &mut HirExpr,
    replacement: HirExpr,
    defined_temps: &BTreeSet<TempId>,
) -> bool {
    let HirExpr::Closure(closure) = expr else {
        return false;
    };

    let mut changed = false;
    for capture in &mut closure.captures {
        let HirExpr::TempRef(temp) = capture.value else {
            continue;
        };
        if defined_temps.contains(&temp) {
            continue;
        }
        capture.value = replacement.clone();
        changed = true;
    }
    changed
}

fn lvalue_as_expr(target: &HirLValue) -> Option<HirExpr> {
    match target {
        HirLValue::Temp(temp) => Some(HirExpr::TempRef(*temp)),
        HirLValue::Local(local) => Some(HirExpr::LocalRef(*local)),
        HirLValue::Upvalue(upvalue) => Some(HirExpr::UpvalueRef(*upvalue)),
        HirLValue::Global(global) => Some(HirExpr::GlobalRef(global.clone())),
        HirLValue::TableAccess(_) => None,
    }
}

fn collect_defined_temps(block: &HirBlock) -> BTreeSet<TempId> {
    let mut defined = BTreeSet::new();
    collect_defined_temps_in_block(block, &mut defined);
    defined
}

fn collect_defined_temps_in_block(block: &HirBlock, defined: &mut BTreeSet<TempId>) {
    for stmt in &block.stmts {
        collect_defined_temps_in_stmt(stmt, defined);
    }
}

fn collect_defined_temps_in_stmt(stmt: &HirStmt, defined: &mut BTreeSet<TempId>) {
    match stmt {
        HirStmt::Assign(assign) => {
            for target in &assign.targets {
                if let HirLValue::Temp(temp) = target {
                    defined.insert(*temp);
                }
            }
        }
        HirStmt::If(if_stmt) => {
            collect_defined_temps_in_block(&if_stmt.then_block, defined);
            if let Some(else_block) = &if_stmt.else_block {
                collect_defined_temps_in_block(else_block, defined);
            }
        }
        HirStmt::While(while_stmt) => collect_defined_temps_in_block(&while_stmt.body, defined),
        HirStmt::Repeat(repeat_stmt) => collect_defined_temps_in_block(&repeat_stmt.body, defined),
        HirStmt::NumericFor(numeric_for) => {
            collect_defined_temps_in_block(&numeric_for.body, defined);
        }
        HirStmt::GenericFor(generic_for) => {
            collect_defined_temps_in_block(&generic_for.body, defined);
        }
        HirStmt::Block(block) => collect_defined_temps_in_block(block, defined),
        HirStmt::Unstructured(unstructured) => {
            collect_defined_temps_in_block(&unstructured.body, defined);
        }
        HirStmt::LocalDecl(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => {}
    }
}

#[cfg(test)]
mod tests;
