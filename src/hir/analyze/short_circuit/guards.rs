//! 这个子模块负责短路恢复前的安全守卫。
//!
//! 它依赖 StructureFacts 的短路块集合和当前 lowering 已分配的 temp 身份，只回答“这个候选
//! 会不会引用超出允许范围的临时值”，不会在这里重写表达式。
//! 例如：若某个候选需要读到 stop-boundary 之外的 temp，这里会先把它拦下。

use super::*;

pub(crate) fn decision_references_forbidden_candidate_temps(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    decision: &HirDecisionExpr,
    allowed_blocks: &BTreeSet<BlockRef>,
) -> bool {
    let forbidden = forbidden_candidate_temps(lowering, short, allowed_blocks);

    decision.nodes.iter().any(|node| {
        expr_references_any_temp(&node.test, &forbidden)
            || decision_target_references_any_temp(&node.truthy, &forbidden)
            || decision_target_references_any_temp(&node.falsy, &forbidden)
    })
}

pub(crate) fn expr_references_forbidden_candidate_temps(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    expr: &HirExpr,
    allowed_blocks: &BTreeSet<BlockRef>,
) -> bool {
    let forbidden = forbidden_candidate_temps(lowering, short, allowed_blocks);
    expr_references_any_temp(expr, &forbidden)
}

fn forbidden_candidate_temps(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    allowed_blocks: &BTreeSet<BlockRef>,
) -> BTreeSet<TempId> {
    short
        .blocks
        .iter()
        .copied()
        .filter(|block| !allowed_blocks.contains(block))
        .flat_map(|block| {
            let range = lowering.cfg.blocks[block.index()].instrs;
            (range.start.index()..range.end())
                .flat_map(|instr_index| lowering.dataflow.instr_defs[instr_index].iter().copied())
                .map(|def_id| lowering.bindings.fixed_temps[def_id.index()])
                .collect::<Vec<_>>()
        })
        .collect()
}

fn decision_target_references_any_temp(
    target: &HirDecisionTarget,
    forbidden: &BTreeSet<TempId>,
) -> bool {
    match target {
        HirDecisionTarget::Expr(expr) => expr_references_any_temp(expr, forbidden),
        HirDecisionTarget::Node(_) | HirDecisionTarget::CurrentValue => false,
    }
}

pub(super) fn expr_references_any_temp(expr: &HirExpr, forbidden: &BTreeSet<TempId>) -> bool {
    match expr {
        HirExpr::TempRef(temp) => forbidden.contains(temp),
        HirExpr::TableAccess(access) => {
            expr_references_any_temp(&access.base, forbidden)
                || expr_references_any_temp(&access.key, forbidden)
        }
        HirExpr::Unary(unary) => expr_references_any_temp(&unary.expr, forbidden),
        HirExpr::Binary(binary) => {
            expr_references_any_temp(&binary.lhs, forbidden)
                || expr_references_any_temp(&binary.rhs, forbidden)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_references_any_temp(&logical.lhs, forbidden)
                || expr_references_any_temp(&logical.rhs, forbidden)
        }
        HirExpr::Decision(decision) => decision.nodes.iter().any(|node| {
            expr_references_any_temp(&node.test, forbidden)
                || decision_target_references_any_temp(&node.truthy, forbidden)
                || decision_target_references_any_temp(&node.falsy, forbidden)
        }),
        HirExpr::Call(call) => {
            expr_references_any_temp(&call.callee, forbidden)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_references_any_temp(arg, forbidden))
        }
        HirExpr::TableConstructor(table) => {
            table.fields.iter().any(|field| match field {
                crate::hir::common::HirTableField::Array(expr) => {
                    expr_references_any_temp(expr, forbidden)
                }
                crate::hir::common::HirTableField::Record(field) => {
                    matches!(
                        &field.key,
                        crate::hir::common::HirTableKey::Expr(expr)
                            if expr_references_any_temp(expr, forbidden)
                    ) || expr_references_any_temp(&field.value, forbidden)
                }
            }) || table
                .trailing_multivalue
                .as_ref()
                .is_some_and(|expr| expr_references_any_temp(expr, forbidden))
        }
        HirExpr::Closure(closure) => closure
            .captures
            .iter()
            .any(|capture| expr_references_any_temp(&capture.value, forbidden)),
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => false,
    }
}
