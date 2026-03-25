//! 这个文件实现 HIR 的第一批 temp inlining。
//!
//! 我们故意把规则收得很保守：只折叠“单目标 temp 赋值，并且被紧邻下一条简单语句
//! 使用一次”的情况。这样可以先清掉大量机械性的寄存器搬运，又不会把求值顺序、
//! 控制流边界或 debug 语义悄悄改坏。

use crate::hir::common::{
    HirBlock, HirCallExpr, HirExpr, HirLValue, HirProto, HirStmt, HirTableField, TempId,
};

/// 对单个 proto 递归执行局部 temp 折叠。
pub(super) fn inline_temps_in_proto(proto: &mut HirProto) -> bool {
    inline_temps_in_block(&mut proto.body)
}

fn inline_temps_in_block(block: &mut HirBlock) -> bool {
    let mut changed = false;

    for stmt in &mut block.stmts {
        changed |= inline_temps_in_nested_blocks(stmt);
    }

    loop {
        let mut pass_changed = false;
        let mut index = 0;

        while index + 1 < block.stmts.len() {
            let Some((temp, value)) = inline_candidate(&block.stmts[index]) else {
                index += 1;
                continue;
            };

            let future_use_count = block.stmts[index + 1..]
                .iter()
                .map(|stmt| stmt_temp_use_count(stmt, temp))
                .sum::<usize>();
            if future_use_count != 1 {
                index += 1;
                continue;
            }

            let next_stmt = &mut block.stmts[index + 1];
            if simple_stmt_temp_use_count(next_stmt, temp) != Some(1) {
                index += 1;
                continue;
            }

            replace_temp_in_simple_stmt(next_stmt, temp, &value);
            block.stmts.remove(index);
            pass_changed = true;
            changed = true;

            index = index.saturating_sub(1);
        }

        if !pass_changed {
            break;
        }
    }

    changed
}

fn inline_temps_in_nested_blocks(stmt: &mut HirStmt) -> bool {
    match stmt {
        HirStmt::If(if_stmt) => {
            let mut changed = inline_temps_in_block(&mut if_stmt.then_block);
            if let Some(else_block) = &mut if_stmt.else_block {
                changed |= inline_temps_in_block(else_block);
            }
            changed
        }
        HirStmt::While(while_stmt) => inline_temps_in_block(&mut while_stmt.body),
        HirStmt::Repeat(repeat_stmt) => inline_temps_in_block(&mut repeat_stmt.body),
        HirStmt::NumericFor(numeric_for) => inline_temps_in_block(&mut numeric_for.body),
        HirStmt::GenericFor(generic_for) => inline_temps_in_block(&mut generic_for.body),
        HirStmt::Block(block) => inline_temps_in_block(block),
        HirStmt::Unstructured(unstructured) => inline_temps_in_block(&mut unstructured.body),
        HirStmt::LocalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => false,
    }
}

fn inline_candidate(stmt: &HirStmt) -> Option<(TempId, HirExpr)> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [HirLValue::Temp(temp)] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.as_slice() else {
        return None;
    };

    Some((*temp, value.clone()))
}

fn simple_stmt_temp_use_count(stmt: &HirStmt, temp: TempId) -> Option<usize> {
    match stmt {
        HirStmt::LocalDecl(local_decl) => Some(
            local_decl
                .values
                .iter()
                .map(|value| temp_use_count_in_expr(value, temp))
                .sum(),
        ),
        HirStmt::Assign(assign) => Some(
            assign
                .targets
                .iter()
                .map(|target| temp_use_count_in_lvalue(target, temp))
                .sum::<usize>()
                + assign
                    .values
                    .iter()
                    .map(|value| temp_use_count_in_expr(value, temp))
                    .sum::<usize>(),
        ),
        HirStmt::TableSetList(set_list) => Some(
            temp_use_count_in_expr(&set_list.base, temp)
                + set_list
                    .values
                    .iter()
                    .map(|value| temp_use_count_in_expr(value, temp))
                    .sum::<usize>()
                + set_list
                    .trailing_multivalue
                    .as_ref()
                    .map_or(0, |expr| temp_use_count_in_expr(expr, temp)),
        ),
        HirStmt::CallStmt(call_stmt) => Some(temp_use_count_in_call_expr(&call_stmt.call, temp)),
        HirStmt::Return(ret) => Some(
            ret.values
                .iter()
                .map(|value| temp_use_count_in_expr(value, temp))
                .sum(),
        ),
        HirStmt::If(_)
        | HirStmt::While(_)
        | HirStmt::Repeat(_)
        | HirStmt::NumericFor(_)
        | HirStmt::GenericFor(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_)
        | HirStmt::Block(_)
        | HirStmt::Unstructured(_) => None,
    }
}

fn stmt_temp_use_count(stmt: &HirStmt, temp: TempId) -> usize {
    match stmt {
        HirStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter()
            .map(|value| temp_use_count_in_expr(value, temp))
            .sum(),
        HirStmt::Assign(assign) => {
            assign
                .targets
                .iter()
                .map(|target| temp_use_count_in_lvalue(target, temp))
                .sum::<usize>()
                + assign
                    .values
                    .iter()
                    .map(|value| temp_use_count_in_expr(value, temp))
                    .sum::<usize>()
        }
        HirStmt::TableSetList(set_list) => {
            temp_use_count_in_expr(&set_list.base, temp)
                + set_list
                    .values
                    .iter()
                    .map(|value| temp_use_count_in_expr(value, temp))
                    .sum::<usize>()
                + set_list
                    .trailing_multivalue
                    .as_ref()
                    .map_or(0, |expr| temp_use_count_in_expr(expr, temp))
        }
        HirStmt::CallStmt(call_stmt) => temp_use_count_in_call_expr(&call_stmt.call, temp),
        HirStmt::Return(ret) => ret
            .values
            .iter()
            .map(|value| temp_use_count_in_expr(value, temp))
            .sum(),
        HirStmt::If(if_stmt) => {
            temp_use_count_in_expr(&if_stmt.cond, temp)
                + if_stmt
                    .then_block
                    .stmts
                    .iter()
                    .map(|stmt| stmt_temp_use_count(stmt, temp))
                    .sum::<usize>()
                + if_stmt.else_block.as_ref().map_or(0, |else_block| {
                    else_block
                        .stmts
                        .iter()
                        .map(|stmt| stmt_temp_use_count(stmt, temp))
                        .sum::<usize>()
                })
        }
        HirStmt::While(while_stmt) => {
            temp_use_count_in_expr(&while_stmt.cond, temp)
                + while_stmt
                    .body
                    .stmts
                    .iter()
                    .map(|stmt| stmt_temp_use_count(stmt, temp))
                    .sum::<usize>()
        }
        HirStmt::Repeat(repeat_stmt) => {
            repeat_stmt
                .body
                .stmts
                .iter()
                .map(|stmt| stmt_temp_use_count(stmt, temp))
                .sum::<usize>()
                + temp_use_count_in_expr(&repeat_stmt.cond, temp)
        }
        HirStmt::NumericFor(numeric_for) => {
            temp_use_count_in_expr(&numeric_for.start, temp)
                + temp_use_count_in_expr(&numeric_for.limit, temp)
                + temp_use_count_in_expr(&numeric_for.step, temp)
                + numeric_for
                    .body
                    .stmts
                    .iter()
                    .map(|stmt| stmt_temp_use_count(stmt, temp))
                    .sum::<usize>()
        }
        HirStmt::GenericFor(generic_for) => {
            generic_for
                .iterator
                .iter()
                .map(|expr| temp_use_count_in_expr(expr, temp))
                .sum::<usize>()
                + generic_for
                    .body
                    .stmts
                    .iter()
                    .map(|stmt| stmt_temp_use_count(stmt, temp))
                    .sum::<usize>()
        }
        HirStmt::Break | HirStmt::Continue | HirStmt::Goto(_) | HirStmt::Label(_) => 0,
        HirStmt::Block(block) => block
            .stmts
            .iter()
            .map(|stmt| stmt_temp_use_count(stmt, temp))
            .sum(),
        HirStmt::Unstructured(unstructured) => unstructured
            .body
            .stmts
            .iter()
            .map(|stmt| stmt_temp_use_count(stmt, temp))
            .sum(),
    }
}

fn replace_temp_in_simple_stmt(stmt: &mut HirStmt, temp: TempId, replacement: &HirExpr) {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            for value in &mut local_decl.values {
                replace_temp_in_expr(value, temp, replacement);
            }
        }
        HirStmt::Assign(assign) => {
            for target in &mut assign.targets {
                replace_temp_in_lvalue(target, temp, replacement);
            }
            for value in &mut assign.values {
                replace_temp_in_expr(value, temp, replacement);
            }
        }
        HirStmt::TableSetList(set_list) => {
            replace_temp_in_expr(&mut set_list.base, temp, replacement);
            for value in &mut set_list.values {
                replace_temp_in_expr(value, temp, replacement);
            }
            if let Some(expr) = &mut set_list.trailing_multivalue {
                replace_temp_in_expr(expr, temp, replacement);
            }
        }
        HirStmt::CallStmt(call_stmt) => {
            replace_temp_in_call_expr(&mut call_stmt.call, temp, replacement)
        }
        HirStmt::Return(ret) => {
            for value in &mut ret.values {
                replace_temp_in_expr(value, temp, replacement);
            }
        }
        HirStmt::If(_)
        | HirStmt::While(_)
        | HirStmt::Repeat(_)
        | HirStmt::NumericFor(_)
        | HirStmt::GenericFor(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_)
        | HirStmt::Block(_)
        | HirStmt::Unstructured(_) => {}
    }
}

fn temp_use_count_in_call_expr(call: &HirCallExpr, temp: TempId) -> usize {
    temp_use_count_in_expr(&call.callee, temp)
        + call
            .args
            .iter()
            .map(|arg| temp_use_count_in_expr(arg, temp))
            .sum::<usize>()
}

fn replace_temp_in_call_expr(call: &mut HirCallExpr, temp: TempId, replacement: &HirExpr) {
    replace_temp_in_expr(&mut call.callee, temp, replacement);
    for arg in &mut call.args {
        replace_temp_in_expr(arg, temp, replacement);
    }
}

fn temp_use_count_in_lvalue(lvalue: &HirLValue, temp: TempId) -> usize {
    match lvalue {
        HirLValue::Temp(_) | HirLValue::Local(_) | HirLValue::Upvalue(_) | HirLValue::Global(_) => {
            0
        }
        HirLValue::TableAccess(access) => {
            temp_use_count_in_expr(&access.base, temp) + temp_use_count_in_expr(&access.key, temp)
        }
    }
}

fn replace_temp_in_lvalue(lvalue: &mut HirLValue, temp: TempId, replacement: &HirExpr) {
    if let HirLValue::TableAccess(access) = lvalue {
        replace_temp_in_expr(&mut access.base, temp, replacement);
        replace_temp_in_expr(&mut access.key, temp, replacement);
    }
}

fn temp_use_count_in_expr(expr: &HirExpr, temp: TempId) -> usize {
    match expr {
        HirExpr::TempRef(other) => usize::from(*other == temp),
        HirExpr::TableAccess(access) => {
            temp_use_count_in_expr(&access.base, temp) + temp_use_count_in_expr(&access.key, temp)
        }
        HirExpr::Unary(unary) => temp_use_count_in_expr(&unary.expr, temp),
        HirExpr::Binary(binary) => {
            temp_use_count_in_expr(&binary.lhs, temp) + temp_use_count_in_expr(&binary.rhs, temp)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            temp_use_count_in_expr(&logical.lhs, temp) + temp_use_count_in_expr(&logical.rhs, temp)
        }
        HirExpr::Decision(decision) => decision
            .nodes
            .iter()
            .map(|node| {
                temp_use_count_in_expr(&node.test, temp)
                    + temp_use_count_in_decision_target(&node.truthy, temp)
                    + temp_use_count_in_decision_target(&node.falsy, temp)
            })
            .sum(),
        HirExpr::Call(call) => temp_use_count_in_call_expr(call, temp),
        HirExpr::TableConstructor(table) => {
            table
                .fields
                .iter()
                .map(|field| match field {
                    HirTableField::Array(expr) => temp_use_count_in_expr(expr, temp),
                    HirTableField::Record(field) => {
                        temp_use_count_in_table_key(&field.key, temp)
                            + temp_use_count_in_expr(&field.value, temp)
                    }
                })
                .sum::<usize>()
                + table
                    .trailing_multivalue
                    .as_ref()
                    .map_or(0, |expr| temp_use_count_in_expr(expr, temp))
        }
        HirExpr::Closure(closure) => closure
            .captures
            .iter()
            .map(|capture| temp_use_count_in_expr(&capture.value, temp))
            .sum(),
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
        | HirExpr::Unresolved(_) => 0,
    }
}

fn replace_temp_in_expr(expr: &mut HirExpr, temp: TempId, replacement: &HirExpr) {
    match expr {
        HirExpr::TempRef(other) if *other == temp => {
            *expr = replacement.clone();
        }
        HirExpr::TableAccess(access) => {
            replace_temp_in_expr(&mut access.base, temp, replacement);
            replace_temp_in_expr(&mut access.key, temp, replacement);
        }
        HirExpr::Unary(unary) => replace_temp_in_expr(&mut unary.expr, temp, replacement),
        HirExpr::Binary(binary) => {
            replace_temp_in_expr(&mut binary.lhs, temp, replacement);
            replace_temp_in_expr(&mut binary.rhs, temp, replacement);
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            replace_temp_in_expr(&mut logical.lhs, temp, replacement);
            replace_temp_in_expr(&mut logical.rhs, temp, replacement);
        }
        HirExpr::Decision(decision) => {
            for node in &mut decision.nodes {
                replace_temp_in_expr(&mut node.test, temp, replacement);
                replace_temp_in_decision_target(&mut node.truthy, temp, replacement);
                replace_temp_in_decision_target(&mut node.falsy, temp, replacement);
            }
        }
        HirExpr::Call(call) => replace_temp_in_call_expr(call, temp, replacement),
        HirExpr::TableConstructor(table) => {
            for field in &mut table.fields {
                match field {
                    HirTableField::Array(expr) => replace_temp_in_expr(expr, temp, replacement),
                    HirTableField::Record(field) => {
                        replace_temp_in_table_key(&mut field.key, temp, replacement);
                        replace_temp_in_expr(&mut field.value, temp, replacement);
                    }
                }
            }
            if let Some(expr) = &mut table.trailing_multivalue {
                replace_temp_in_expr(expr, temp, replacement);
            }
        }
        HirExpr::Closure(closure) => {
            for capture in &mut closure.captures {
                replace_temp_in_expr(&mut capture.value, temp, replacement);
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
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => {}
    }
}

fn temp_use_count_in_decision_target(
    target: &crate::hir::common::HirDecisionTarget,
    temp: TempId,
) -> usize {
    match target {
        crate::hir::common::HirDecisionTarget::Expr(expr) => temp_use_count_in_expr(expr, temp),
        crate::hir::common::HirDecisionTarget::Node(_)
        | crate::hir::common::HirDecisionTarget::CurrentValue => 0,
    }
}

fn replace_temp_in_decision_target(
    target: &mut crate::hir::common::HirDecisionTarget,
    temp: TempId,
    replacement: &HirExpr,
) {
    if let crate::hir::common::HirDecisionTarget::Expr(expr) = target {
        replace_temp_in_expr(expr, temp, replacement);
    }
}

fn temp_use_count_in_table_key(key: &crate::hir::common::HirTableKey, temp: TempId) -> usize {
    match key {
        crate::hir::common::HirTableKey::Name(_) => 0,
        crate::hir::common::HirTableKey::Expr(expr) => temp_use_count_in_expr(expr, temp),
    }
}

fn replace_temp_in_table_key(
    key: &mut crate::hir::common::HirTableKey,
    temp: TempId,
    replacement: &HirExpr,
) {
    if let crate::hir::common::HirTableKey::Expr(expr) = key {
        replace_temp_in_expr(expr, temp, replacement);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::common::{
        HirAssign, HirCallStmt, HirGlobalRef, HirModule, HirProtoRef, HirReturn,
    };

    #[test]
    fn removes_immediate_temp_forwarding_chain() {
        let mut proto = dummy_proto(HirBlock {
            stmts: vec![
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(0))],
                    values: vec![HirExpr::Integer(41)],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(1))],
                    values: vec![HirExpr::TempRef(TempId(0))],
                })),
                HirStmt::CallStmt(Box::new(HirCallStmt {
                    call: HirCallExpr {
                        callee: HirExpr::GlobalRef(HirGlobalRef {
                            name: "print".to_owned(),
                        }),
                        args: vec![HirExpr::TempRef(TempId(1))],
                        multiret: false,
                        method: false,
                    },
                })),
                HirStmt::Return(Box::new(HirReturn {
                    values: vec![HirExpr::TempRef(TempId(0))],
                })),
            ],
        });

        assert!(inline_temps_in_proto(&mut proto));
        assert_eq!(proto.body.stmts.len(), 3);
        assert!(matches!(
            &proto.body.stmts[1],
            HirStmt::CallStmt(call_stmt)
                if matches!(call_stmt.call.args.as_slice(), [HirExpr::TempRef(TempId(0))])
        ));
    }

    #[test]
    fn does_not_inline_across_control_barrier() {
        let mut proto = dummy_proto(HirBlock {
            stmts: vec![
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(0))],
                    values: vec![HirExpr::Integer(1)],
                })),
                HirStmt::Label(Box::new(crate::hir::common::HirLabel {
                    id: crate::hir::common::HirLabelId(0),
                })),
                HirStmt::Return(Box::new(HirReturn {
                    values: vec![HirExpr::TempRef(TempId(0))],
                })),
            ],
        });

        assert!(!inline_temps_in_proto(&mut proto));
        assert_eq!(proto.body.stmts.len(), 3);
    }

    fn dummy_proto(body: HirBlock) -> HirProto {
        HirProto {
            id: HirProtoRef(0),
            source: None,
            line_range: crate::parser::ProtoLineRange {
                defined_start: 0,
                defined_end: 0,
            },
            signature: crate::parser::ProtoSignature {
                num_params: 0,
                is_vararg: false,
            },
            params: Vec::new(),
            locals: Vec::new(),
            upvalues: Vec::new(),
            temps: vec![TempId(0), TempId(1)],
            body,
            children: Vec::new(),
        }
    }

    #[test]
    fn simplify_module_runs_until_fixed_point() {
        let mut module = HirModule {
            entry: HirProtoRef(0),
            protos: vec![dummy_proto(HirBlock {
                stmts: vec![
                    HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Temp(TempId(0))],
                        values: vec![HirExpr::Integer(7)],
                    })),
                    HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Temp(TempId(1))],
                        values: vec![HirExpr::TempRef(TempId(0))],
                    })),
                    HirStmt::Return(Box::new(HirReturn {
                        values: vec![HirExpr::TempRef(TempId(1))],
                    })),
                ],
            })],
        };

        super::super::simplify_hir(&mut module);

        assert!(matches!(
            &module.protos[0].body.stmts.as_slice(),
            [HirStmt::Return(ret)] if matches!(ret.values.as_slice(), [HirExpr::Integer(7)])
        ));
    }
}
