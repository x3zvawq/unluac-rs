//! 这个文件负责清理已经失去职责的布尔物化分支壳。
//!
//! 当 HIR 前面已经把 merge 值恢复成直接的布尔表达式时，原先那种
//! `if cond then t=true else f=false end` 的结构壳就只剩下机械噪音了。
//! 这里专门删除这一类“纯布尔物化、无副作用、目标 temp 已经没人再读”的壳，
//! 避免把普通 if/else 结构误删掉。

use std::collections::BTreeMap;

use crate::hir::common::{HirBlock, HirExpr, HirLValue, HirProto, HirStmt, HirTableField, TempId};

pub(super) fn remove_boolean_materialization_shells_in_proto(proto: &mut HirProto) -> bool {
    let mut use_counts = BTreeMap::new();
    collect_block_temp_uses(&proto.body, &mut use_counts);
    remove_boolean_materialization_shells_in_block(&mut proto.body, &use_counts)
}

fn remove_boolean_materialization_shells_in_block(
    block: &mut HirBlock,
    use_counts: &BTreeMap<TempId, usize>,
) -> bool {
    let mut changed = false;

    for stmt in &mut block.stmts {
        changed |= remove_boolean_materialization_shells_in_nested(stmt, use_counts);
    }

    let mut index = 0;
    while index < block.stmts.len() {
        if removable_boolean_materialization_shell(&block.stmts[index], use_counts) {
            block.stmts.remove(index);
            changed = true;
            continue;
        }
        index += 1;
    }

    changed
}

fn remove_boolean_materialization_shells_in_nested(
    stmt: &mut HirStmt,
    use_counts: &BTreeMap<TempId, usize>,
) -> bool {
    match stmt {
        HirStmt::If(if_stmt) => {
            let mut changed =
                remove_boolean_materialization_shells_in_block(&mut if_stmt.then_block, use_counts);
            if let Some(else_block) = &mut if_stmt.else_block {
                changed |= remove_boolean_materialization_shells_in_block(else_block, use_counts);
            }
            changed
        }
        HirStmt::While(while_stmt) => {
            remove_boolean_materialization_shells_in_block(&mut while_stmt.body, use_counts)
        }
        HirStmt::Repeat(repeat_stmt) => {
            remove_boolean_materialization_shells_in_block(&mut repeat_stmt.body, use_counts)
        }
        HirStmt::NumericFor(numeric_for) => {
            remove_boolean_materialization_shells_in_block(&mut numeric_for.body, use_counts)
        }
        HirStmt::GenericFor(generic_for) => {
            remove_boolean_materialization_shells_in_block(&mut generic_for.body, use_counts)
        }
        HirStmt::Block(block) => remove_boolean_materialization_shells_in_block(block, use_counts),
        HirStmt::Unstructured(unstructured) => {
            remove_boolean_materialization_shells_in_block(&mut unstructured.body, use_counts)
        }
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

fn removable_boolean_materialization_shell(
    stmt: &HirStmt,
    use_counts: &BTreeMap<TempId, usize>,
) -> bool {
    let HirStmt::If(if_stmt) = stmt else {
        return false;
    };
    let Some(else_block) = &if_stmt.else_block else {
        return false;
    };
    if !expr_is_side_effect_free(&if_stmt.cond) {
        return false;
    }

    let Some((then_temp, then_value)) = bool_assign_pattern(&if_stmt.then_block) else {
        return false;
    };
    let Some((else_temp, else_value)) = bool_assign_pattern(else_block) else {
        return false;
    };

    if use_counts.get(&then_temp).copied().unwrap_or(0) != 0
        || use_counts.get(&else_temp).copied().unwrap_or(0) != 0
    {
        return false;
    }

    matches!((then_value, else_value), (true, false) | (false, true))
}

fn bool_assign_pattern(block: &HirBlock) -> Option<(TempId, bool)> {
    let [HirStmt::Assign(assign)] = block.stmts.as_slice() else {
        return None;
    };
    let [HirLValue::Temp(temp)] = assign.targets.as_slice() else {
        return None;
    };
    let [HirExpr::Boolean(value)] = assign.values.as_slice() else {
        return None;
    };

    Some((*temp, *value))
}

fn collect_block_temp_uses(block: &HirBlock, use_counts: &mut BTreeMap<TempId, usize>) {
    for stmt in &block.stmts {
        collect_stmt_temp_uses(stmt, use_counts);
    }
}

fn collect_stmt_temp_uses(stmt: &HirStmt, use_counts: &mut BTreeMap<TempId, usize>) {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            for value in &local_decl.values {
                collect_expr_temp_uses(value, use_counts);
            }
        }
        HirStmt::Assign(assign) => {
            for target in &assign.targets {
                collect_lvalue_temp_uses(target, use_counts);
            }
            for value in &assign.values {
                collect_expr_temp_uses(value, use_counts);
            }
        }
        HirStmt::TableSetList(set_list) => {
            collect_expr_temp_uses(&set_list.base, use_counts);
            for value in &set_list.values {
                collect_expr_temp_uses(value, use_counts);
            }
            if let Some(trailing) = &set_list.trailing_multivalue {
                collect_expr_temp_uses(trailing, use_counts);
            }
        }
        HirStmt::ErrNil(err_nil) => {
            collect_expr_temp_uses(&err_nil.value, use_counts);
        }
        HirStmt::ToBeClosed(to_be_closed) => {
            collect_expr_temp_uses(&to_be_closed.value, use_counts);
        }
        HirStmt::CallStmt(call_stmt) => {
            collect_expr_temp_uses(&call_stmt.call.callee, use_counts);
            for arg in &call_stmt.call.args {
                collect_expr_temp_uses(arg, use_counts);
            }
        }
        HirStmt::Return(ret) => {
            for value in &ret.values {
                collect_expr_temp_uses(value, use_counts);
            }
        }
        HirStmt::If(if_stmt) => {
            collect_expr_temp_uses(&if_stmt.cond, use_counts);
            collect_block_temp_uses(&if_stmt.then_block, use_counts);
            if let Some(else_block) = &if_stmt.else_block {
                collect_block_temp_uses(else_block, use_counts);
            }
        }
        HirStmt::While(while_stmt) => {
            collect_expr_temp_uses(&while_stmt.cond, use_counts);
            collect_block_temp_uses(&while_stmt.body, use_counts);
        }
        HirStmt::Repeat(repeat_stmt) => {
            collect_block_temp_uses(&repeat_stmt.body, use_counts);
            collect_expr_temp_uses(&repeat_stmt.cond, use_counts);
        }
        HirStmt::NumericFor(numeric_for) => {
            collect_expr_temp_uses(&numeric_for.start, use_counts);
            collect_expr_temp_uses(&numeric_for.limit, use_counts);
            collect_expr_temp_uses(&numeric_for.step, use_counts);
            collect_block_temp_uses(&numeric_for.body, use_counts);
        }
        HirStmt::GenericFor(generic_for) => {
            for value in &generic_for.iterator {
                collect_expr_temp_uses(value, use_counts);
            }
            collect_block_temp_uses(&generic_for.body, use_counts);
        }
        HirStmt::Block(block) => collect_block_temp_uses(block, use_counts),
        HirStmt::Unstructured(unstructured) => {
            collect_block_temp_uses(&unstructured.body, use_counts)
        }
        HirStmt::Break
        | HirStmt::Close(_)
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => {}
    }
}

fn collect_lvalue_temp_uses(lvalue: &HirLValue, use_counts: &mut BTreeMap<TempId, usize>) {
    if let HirLValue::TableAccess(access) = lvalue {
        collect_expr_temp_uses(&access.base, use_counts);
        collect_expr_temp_uses(&access.key, use_counts);
    }
}

fn collect_expr_temp_uses(expr: &HirExpr, use_counts: &mut BTreeMap<TempId, usize>) {
    match expr {
        HirExpr::TempRef(temp) => {
            *use_counts.entry(*temp).or_insert(0) += 1;
        }
        HirExpr::TableAccess(access) => {
            collect_expr_temp_uses(&access.base, use_counts);
            collect_expr_temp_uses(&access.key, use_counts);
        }
        HirExpr::Unary(unary) => collect_expr_temp_uses(&unary.expr, use_counts),
        HirExpr::Binary(binary) => {
            collect_expr_temp_uses(&binary.lhs, use_counts);
            collect_expr_temp_uses(&binary.rhs, use_counts);
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            collect_expr_temp_uses(&logical.lhs, use_counts);
            collect_expr_temp_uses(&logical.rhs, use_counts);
        }
        HirExpr::Decision(decision) => {
            for node in &decision.nodes {
                collect_expr_temp_uses(&node.test, use_counts);
                collect_decision_target_temp_uses(&node.truthy, use_counts);
                collect_decision_target_temp_uses(&node.falsy, use_counts);
            }
        }
        HirExpr::Call(call) => {
            collect_expr_temp_uses(&call.callee, use_counts);
            for arg in &call.args {
                collect_expr_temp_uses(arg, use_counts);
            }
        }
        HirExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    HirTableField::Array(expr) => collect_expr_temp_uses(expr, use_counts),
                    HirTableField::Record(field) => {
                        if let crate::hir::common::HirTableKey::Expr(expr) = &field.key {
                            collect_expr_temp_uses(expr, use_counts);
                        }
                        collect_expr_temp_uses(&field.value, use_counts);
                    }
                }
            }
            if let Some(expr) = &table.trailing_multivalue {
                collect_expr_temp_uses(expr, use_counts);
            }
        }
        HirExpr::Closure(closure) => {
            for capture in &closure.captures {
                collect_expr_temp_uses(&capture.value, use_counts);
            }
        }
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => {}
    }
}

fn collect_decision_target_temp_uses(
    target: &crate::hir::common::HirDecisionTarget,
    use_counts: &mut BTreeMap<TempId, usize>,
) {
    if let crate::hir::common::HirDecisionTarget::Expr(expr) = target {
        collect_expr_temp_uses(expr, use_counts);
    }
}

fn expr_is_side_effect_free(expr: &HirExpr) -> bool {
    match expr {
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_) => true,
        HirExpr::Unary(unary) => expr_is_side_effect_free(&unary.expr),
        HirExpr::Binary(binary) => {
            expr_is_side_effect_free(&binary.lhs) && expr_is_side_effect_free(&binary.rhs)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_is_side_effect_free(&logical.lhs) && expr_is_side_effect_free(&logical.rhs)
        }
        HirExpr::Decision(decision) => decision.nodes.iter().all(|node| {
            expr_is_side_effect_free(&node.test)
                && decision_target_is_side_effect_free(&node.truthy)
                && decision_target_is_side_effect_free(&node.falsy)
        }),
        HirExpr::TableAccess(_)
        | HirExpr::Call(_)
        | HirExpr::VarArg
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => false,
    }
}

fn decision_target_is_side_effect_free(target: &crate::hir::common::HirDecisionTarget) -> bool {
    match target {
        crate::hir::common::HirDecisionTarget::Node(_)
        | crate::hir::common::HirDecisionTarget::CurrentValue => true,
        crate::hir::common::HirDecisionTarget::Expr(expr) => expr_is_side_effect_free(expr),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::common::{
        HirAssign, HirBinaryExpr, HirBinaryOpKind, HirCallExpr, HirCallStmt, HirGlobalRef, HirIf,
        HirProtoRef,
    };

    #[test]
    fn removes_dead_boolean_materialization_shell() {
        let mut proto = dummy_proto(HirBlock {
            stmts: vec![
                HirStmt::If(Box::new(HirIf {
                    cond: HirExpr::Binary(Box::new(HirBinaryExpr {
                        op: HirBinaryOpKind::Eq,
                        lhs: HirExpr::LocalRef(crate::hir::common::LocalId(0)),
                        rhs: HirExpr::Nil,
                    })),
                    then_block: HirBlock {
                        stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                            targets: vec![HirLValue::Temp(TempId(0))],
                            values: vec![HirExpr::Boolean(true)],
                        }))],
                    },
                    else_block: Some(HirBlock {
                        stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                            targets: vec![HirLValue::Temp(TempId(1))],
                            values: vec![HirExpr::Boolean(false)],
                        }))],
                    }),
                })),
                HirStmt::CallStmt(Box::new(HirCallStmt {
                    call: HirCallExpr {
                        callee: HirExpr::GlobalRef(HirGlobalRef {
                            name: "print".to_owned(),
                        }),
                        args: vec![HirExpr::Binary(Box::new(HirBinaryExpr {
                            op: HirBinaryOpKind::Eq,
                            lhs: HirExpr::LocalRef(crate::hir::common::LocalId(0)),
                            rhs: HirExpr::Nil,
                        }))],
                        multiret: false,
                        method: false,
                    },
                })),
            ],
        });

        assert!(remove_boolean_materialization_shells_in_proto(&mut proto));
        assert!(matches!(
            proto.body.stmts.as_slice(),
            [HirStmt::CallStmt(_)]
        ));
    }

    fn dummy_proto(body: HirBlock) -> crate::hir::common::HirProto {
        crate::hir::common::HirProto {
            id: HirProtoRef(0),
            source: None,
            line_range: crate::parser::ProtoLineRange {
                defined_start: 0,
                defined_end: 0,
            },
            signature: crate::parser::ProtoSignature {
                num_params: 0,
                is_vararg: false,
                has_vararg_param_reg: false,
                named_vararg_table: false,
            },
            params: Vec::new(),
            locals: vec![crate::hir::common::LocalId(0)],
            upvalues: Vec::new(),
            temps: vec![TempId(0), TempId(1)],
            temp_debug_locals: vec![None, None],
            body,
            children: Vec::new(),
        }
    }
}
