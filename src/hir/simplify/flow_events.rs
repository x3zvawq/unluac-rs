//! 当前 HIR 语句头中已经发生的共享执行事件。
//!
//! 这里仅发布 target-neutral 的 value escape 位置，不解释 GC root、closure effect 或
//! physical home。结构化子 block 不属于父语句头，不能由 visitor 递归混入同一个线性事件；
//! generic-for 的每轮隐式调用由 `lexical_cfg` 的 typed protocol 节点表达，也不在这里从
//! iterator 文本形状反推。

use std::collections::BTreeSet;

use crate::hir::common::{
    HirCallExpr, HirDecisionTarget, HirExpr, HirLValue, HirStmt, HirTableField, HirValuePack,
    TempId,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum HirEscapeEventKind {
    ExternalStore,
    CallCallee,
    CallArgument,
    Return,
}

#[derive(Clone, Copy)]
pub(super) struct HirEscapeEvent<'a> {
    pub(super) kind: HirEscapeEventKind,
    pub(super) value: &'a HirExpr,
}

pub(super) fn visit_stmt_header_escape_events<'a>(
    stmt: &'a HirStmt,
    emit: &mut impl FnMut(HirEscapeEvent<'a>),
) {
    match stmt {
        HirStmt::LocalDecl(decl) => visit_pack_calls(&decl.values, emit),
        HirStmt::GlobalDecl(decl) => {
            for index in 0..decl.names.len() {
                if let Some(value) = adjusted_value(&decl.values, index) {
                    emit_escape(HirEscapeEventKind::ExternalStore, value, emit);
                }
            }
            visit_pack_calls(&decl.values, emit);
        }
        HirStmt::Assign(assign) => {
            for (index, target) in assign.targets.iter().enumerate() {
                match target {
                    HirLValue::Global(_) | HirLValue::Upvalue(_) => {
                        if let Some(value) = adjusted_value(&assign.values, index) {
                            emit_escape(HirEscapeEventKind::ExternalStore, value, emit);
                        }
                    }
                    HirLValue::TableAccess(access) => {
                        emit_escape(HirEscapeEventKind::ExternalStore, &access.key, emit);
                        visit_expr_calls(&access.base, emit);
                        visit_expr_calls(&access.key, emit);
                        if let Some(value) = adjusted_value(&assign.values, index) {
                            emit_escape(HirEscapeEventKind::ExternalStore, value, emit);
                        }
                    }
                    HirLValue::Param(_) | HirLValue::Temp(_) | HirLValue::Local(_) => {}
                }
            }
            visit_pack_calls(&assign.values, emit);
        }
        HirStmt::TableSetList(set) => {
            visit_expr_calls(&set.base, emit);
            for value in &set.values {
                emit_escape(HirEscapeEventKind::ExternalStore, value, emit);
            }
            visit_pack_calls(&set.values, emit);
        }
        HirStmt::ErrNil(err) => visit_expr_calls(&err.value, emit),
        HirStmt::ToBeClosed(tbc) => visit_expr_calls(&tbc.value, emit),
        HirStmt::CallStmt(call) => visit_call(&call.call, emit),
        HirStmt::Return(ret) => {
            for value in &ret.values {
                emit_escape(HirEscapeEventKind::Return, value, emit);
            }
            visit_pack_calls(&ret.values, emit);
        }
        HirStmt::If(if_stmt) => visit_expr_calls(&if_stmt.cond, emit),
        HirStmt::While(while_stmt) => visit_expr_calls(&while_stmt.cond, emit),
        HirStmt::NumericFor(for_stmt) => {
            visit_expr_calls(&for_stmt.start, emit);
            visit_expr_calls(&for_stmt.limit, emit);
            visit_expr_calls(&for_stmt.step, emit);
        }
        HirStmt::GenericFor(for_stmt) => visit_pack_calls(&for_stmt.iterator, emit),
        HirStmt::Repeat(_)
        | HirStmt::Close(_)
        | HirStmt::Block(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => {}
    }
}

pub(super) fn escaping_identity_temps_in_stmt_header(stmt: &HirStmt) -> BTreeSet<TempId> {
    let mut temps = BTreeSet::new();
    visit_stmt_header_escape_events(stmt, &mut |event| {
        let _kind = event.kind;
        collect_identity_temps(event.value, &mut temps);
    });
    temps
}

fn adjusted_value(values: &HirValuePack, index: usize) -> Option<&HirExpr> {
    if let Some(value) = values.fixed.get(index) {
        return Some(value);
    }
    let tail = values.tail.as_ref()?;
    let tail_index = index - values.fixed.len();
    tail.exact_width()
        .is_none_or(|width| tail_index < width)
        .then(|| tail.as_expr())
}

fn emit_escape<'a>(
    kind: HirEscapeEventKind,
    value: &'a HirExpr,
    emit: &mut impl FnMut(HirEscapeEvent<'a>),
) {
    emit(HirEscapeEvent { kind, value });
}

fn visit_pack_calls<'a>(pack: &'a HirValuePack, emit: &mut impl FnMut(HirEscapeEvent<'a>)) {
    for value in pack {
        visit_expr_calls(value, emit);
    }
}

fn visit_call<'a>(call: &'a HirCallExpr, emit: &mut impl FnMut(HirEscapeEvent<'a>)) {
    emit_escape(HirEscapeEventKind::CallCallee, &call.callee, emit);
    visit_expr_calls(&call.callee, emit);
    for argument in &call.args {
        emit_escape(HirEscapeEventKind::CallArgument, argument, emit);
        visit_expr_calls(argument, emit);
    }
}

fn visit_expr_calls<'a>(expr: &'a HirExpr, emit: &mut impl FnMut(HirEscapeEvent<'a>)) {
    match expr {
        HirExpr::Call(call) => visit_call(call, emit),
        HirExpr::TableAccess(access) => {
            visit_expr_calls(&access.base, emit);
            visit_expr_calls(&access.key, emit);
        }
        HirExpr::Unary(unary) => visit_expr_calls(&unary.expr, emit),
        HirExpr::Binary(binary) => {
            visit_expr_calls(&binary.lhs, emit);
            visit_expr_calls(&binary.rhs, emit);
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            visit_expr_calls(&logical.lhs, emit);
            visit_expr_calls(&logical.rhs, emit);
        }
        HirExpr::Decision(decision) => {
            for node in &decision.nodes {
                visit_expr_calls(&node.test, emit);
                if let HirDecisionTarget::Expr(value) = &node.truthy {
                    visit_expr_calls(value, emit);
                }
                if let HirDecisionTarget::Expr(value) = &node.falsy {
                    visit_expr_calls(value, emit);
                }
            }
        }
        HirExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    HirTableField::Array(value) => visit_expr_calls(value, emit),
                    HirTableField::Record(record) => {
                        visit_expr_calls(&record.key, emit);
                        visit_expr_calls(&record.value, emit);
                    }
                }
            }
            if let Some(tail) = &table.trailing_multivalue {
                visit_expr_calls(tail.as_expr(), emit);
            }
        }
        HirExpr::Closure(closure) => {
            for capture in &closure.captures {
                visit_expr_calls(&capture.value, emit);
            }
        }
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
        | HirExpr::Vector(_)
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => {}
    }
}

fn collect_identity_temps(expr: &HirExpr, temps: &mut BTreeSet<TempId>) {
    match expr {
        HirExpr::TempRef(temp) => {
            temps.insert(*temp);
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            collect_identity_temps(&logical.lhs, temps);
            collect_identity_temps(&logical.rhs, temps);
        }
        HirExpr::Decision(decision) => {
            for node in &decision.nodes {
                if let HirDecisionTarget::Expr(value) = &node.truthy {
                    collect_identity_temps(value, temps);
                }
                if let HirDecisionTarget::Expr(value) = &node.falsy {
                    collect_identity_temps(value, temps);
                }
            }
        }
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
        | HirExpr::Vector(_)
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Unary(_)
        | HirExpr::Binary(_)
        | HirExpr::Call(_)
        | HirExpr::VarArg
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::common::{HirAssign, HirCallStmt, HirLogicalExpr, HirTableAccess};

    #[test]
    fn parallel_table_store_escapes_only_its_adjusted_value_and_key() {
        let local_value = TempId(0);
        let stored_value = TempId(1);
        let key = TempId(2);
        let stmt = HirStmt::Assign(Box::new(HirAssign {
            targets: vec![
                HirLValue::Local(crate::hir::common::LocalId(0)),
                HirLValue::TableAccess(Box::new(HirTableAccess {
                    base: HirExpr::GlobalRef(crate::hir::common::HirGlobalRef {
                        key: "sink".into(),
                    }),
                    key: HirExpr::TempRef(key),
                    method_setup_protocol: None,
                })),
            ],
            values: HirValuePack::fixed(vec![
                HirExpr::TempRef(local_value),
                HirExpr::TempRef(stored_value),
            ]),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        }));

        assert_eq!(
            escaping_identity_temps_in_stmt_header(&stmt),
            BTreeSet::from([stored_value, key])
        );
    }

    #[test]
    fn call_argument_tracks_identity_through_logical_value() {
        let lhs = TempId(0);
        let rhs = TempId(1);
        let stmt = HirStmt::CallStmt(Box::new(HirCallStmt {
            call: HirCallExpr {
                callee: HirExpr::GlobalRef(crate::hir::common::HirGlobalRef {
                    key: "publish".into(),
                }),
                args: HirValuePack::fixed(vec![HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                    lhs: HirExpr::TempRef(lhs),
                    rhs: HirExpr::TempRef(rhs),
                }))]),
                method: false,
                fastcall: None,
                method_key: None,
                callee_root_handoff: None,
                method_rewrite_transaction: None,
            },
        }));

        assert_eq!(
            escaping_identity_temps_in_stmt_header(&stmt),
            BTreeSet::from([lhs, rhs])
        );
    }

    #[test]
    fn structured_body_is_not_folded_into_the_parent_header_event() {
        let body_only = TempId(0);
        let stmt = HirStmt::While(Box::new(crate::hir::common::HirWhile {
            cond: HirExpr::Boolean(false),
            body: crate::hir::common::HirBlock {
                stmts: vec![HirStmt::CallStmt(Box::new(HirCallStmt {
                    call: HirCallExpr {
                        callee: HirExpr::TableConstructor(Box::default()),
                        args: HirValuePack::fixed(vec![HirExpr::TempRef(body_only)]),
                        method: false,
                        fastcall: None,
                        method_key: None,
                        callee_root_handoff: None,
                        method_rewrite_transaction: None,
                    },
                }))],
            },
        }));

        assert!(escaping_identity_temps_in_stmt_header(&stmt).is_empty());
    }
}
