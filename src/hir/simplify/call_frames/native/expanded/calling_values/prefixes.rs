//! 在未发布草稿中恢复原有条件写入，保持调用方绑定的写入性质。
//! 只消费冻结分支的同一结果版本、原叶写与当前条件；不以伪造赋值影响编译器内联。

use super::*;
use crate::hir::common::{HirAssign, HirIf, HirInlineRetentionReason, HirLogicalExpr};
use crate::hir::simplify::mention::expr_mentions_local;

fn predicates(
    expr: &HirExpr,
    output: &mut Vec<crate::hir::HirSourceSite>,
    budget: &mut usize,
) -> Option<()> {
    *budget = budget.checked_sub(1)?;
    match expr {
        HirExpr::Binary(binary)
            if matches!(
                binary.op,
                HirBinaryOpKind::Eq
                    | HirBinaryOpKind::Lt
                    | HirBinaryOpKind::Le
                    | HirBinaryOpKind::Gt
                    | HirBinaryOpKind::Ge
            ) =>
        {
            output.push(binary.source_site?);
            Some(())
        }
        HirExpr::LogicalAnd(and) | HirExpr::LogicalOr(and) => {
            predicates(&and.lhs, output, budget)?;
            predicates(&and.rhs, output, budget)
        }
        HirExpr::Unary(unary)
            if unary.op == crate::hir::HirUnaryOpKind::Not && unary.source_site.is_none() =>
        {
            predicates(&unary.expr, output, budget)
        }
        _ => None,
    }
}

fn assignment(target: LocalId, value: HirExpr) -> HirStmt {
    HirStmt::Assign(Box::new(HirAssign {
        luau_function_declaration: false,
        luau_compound_global: false,
        upvalue_write_source: None,
        is_phi_transfer: false,
        parallel_nil_frame: None,
        targets: vec![HirLValue::Local(target)],
        values: vec![value].into(),
        initializer_merge_transaction: None,
        generic_for_initializer_producer: None,
        root_release: None,
        method_rewrite_transaction: None,
    }))
}

fn branch(condition: HirExpr, target: LocalId, value: HirExpr) -> HirStmt {
    HirStmt::If(Box::new(HirIf {
        cond: condition,
        predicate_source: None,
        preserves_empty_test: false,
        preserves_arm_order: false,
        then_block: HirBlock {
            stmts: vec![assignment(target, value)],
        },
        else_block: None,
    }))
}

fn without_tail(expr: &HirExpr, target: LocalId, budget: &mut usize) -> Option<HirExpr> {
    *budget = budget.checked_sub(1)?;
    let HirExpr::LogicalOr(or) = expr else {
        return None;
    };
    if or.rhs == HirExpr::LocalRef(target) {
        return Some(or.lhs.clone());
    }
    Some(HirExpr::LogicalOr(Box::new(HirLogicalExpr {
        preserves_boolean_prewrite: or.preserves_boolean_prewrite,
        lhs: or.lhs.clone(),
        rhs: without_tail(&or.rhs, target, budget)?,
    })))
}

fn project(stmt: &HirStmt, facts: &ProtoPromotionFacts) -> Option<(LocalId, Vec<HirStmt>)> {
    let (target, expression) = scalar_local(stmt)?;
    let (condition, initial, changed) = match stmt {
        HirStmt::LocalDecl(decl) if decl.initializer_merge_transaction.is_none() => {
            let HirExpr::LogicalOr(or) = expression else {
                return None;
            };
            let HirExpr::LogicalAnd(and) = &or.lhs else {
                return None;
            };
            let (condition, inverted) = synthetic_not_subject(&and.lhs);
            let literal = Literal::from_expr(&and.rhs)?;
            if inverted % 2 != 1 || matches!(literal, Literal::Nil | Literal::Boolean(false)) {
                return None;
            }
            (condition.clone(), Some(and.rhs.clone()), or.rhs.clone())
        }
        HirStmt::Assign(assign)
            if !assign.is_phi_transfer
                && assign.initializer_merge_transaction.is_none()
                && assign.root_release.is_none()
                && assign.method_rewrite_transaction.is_none() =>
        {
            (
                without_tail(expression, target, &mut 16)?,
                None,
                HirExpr::Boolean(true),
            )
        }
        _ => return None,
    };
    if expr_mentions_local(&condition, target) || expr_mentions_local(&changed, target) {
        return None;
    }
    let mut sources = Vec::new();
    predicates(&condition, &mut sources, &mut 16)?;
    let first = *sources.first()?;
    let frame = facts.branch_value_frame_at(first)?;
    let [result] = frame.results.as_slice() else {
        return None;
    };
    let [left, right] = result.incoming.as_slice() else {
        return None;
    };
    if !frame
        .predicates
        .iter()
        .copied()
        .eq(sources.iter().map(|source| source.instr))
        || facts.promoted_local_for_temp(result.value) != Some(target)
        || sources.iter().any(|source| source.proto != first.proto)
    {
        return None;
    }
    let (kept, written) = if left.source? < first.instr {
        (left, right)
    } else {
        (right, left)
    };
    if kept.source? >= first.instr
        || !written.terminal_write
        || written.source? <= *frame.predicates.last()?
    {
        return None;
    }
    if let Some(initial) = &initial {
        if kept.literal != Literal::from_expr(initial) {
            return None;
        }
    } else if kept.copy.is_none() || written.literal != Some(Literal::Boolean(true)) {
        return None;
    }
    if let HirExpr::TableAccess(access) = &changed {
        let HirOperationSources::Single(source) = access.sources else {
            return None;
        };
        let layout = facts.native_table_read_layout(access)?;
        let HirExpr::LocalRef(base) = access.base else {
            return None;
        };
        let HirExpr::LocalRef(key) = access.key else {
            return None;
        };
        if written.source != Some(source.instr)
            || facts.operation_result_temp(source) != Some(written.value)
            || facts.trusted_local_home_slot(base) != Some(layout.base)
            || facts.trusted_local_home_slot(key) != layout.key
            || layout.base.slot() >= result.home.slot()
            || layout.key?.slot() >= result.home.slot()
        {
            return None;
        }
    } else if let HirExpr::LocalRef(source) = changed {
        let (HirBinding::Temp(input), home) = written.copy? else {
            return None;
        };
        if facts.promoted_local_for_temp(input) != Some(source)
            || facts.trusted_local_home_slot(source) != Some(home)
            || home.slot() >= result.home.slot()
        {
            return None;
        }
    } else {
        let literal = Literal::from_expr(&changed)?;
        if written.literal.as_ref() != Some(&literal) {
            return None;
        }
    }
    let mut replacement = Vec::new();
    if let Some(initial) = initial {
        let HirStmt::LocalDecl(decl) = stmt else {
            return None;
        };
        let mut decl = decl.clone();
        decl.values = vec![initial].into();
        replacement.push(HirStmt::LocalDecl(decl));
    }
    replacement.push(branch(condition, target, changed));
    Some((target, replacement))
}

pub(super) fn prepare(proto: &HirProto, facts: &ProtoPromotionFacts) -> HirProto {
    fn rewrite(
        block: &mut HirBlock,
        facts: &ProtoPromotionFacts,
        preserved: &mut BTreeSet<LocalId>,
    ) {
        let original = std::mem::take(&mut block.stmts);
        for mut stmt in original {
            crate::hir::simplify::walk::for_each_nested_block_mut(&mut stmt, &mut |child| {
                rewrite(child, facts, preserved)
            });
            if let Some((target, replacement)) = project(&stmt, facts) {
                preserved.insert(target);
                block.stmts.extend(replacement);
            } else {
                block.stmts.push(stmt);
            }
        }
    }
    let mut draft = proto.clone();
    let mut preserved = BTreeSet::new();
    rewrite(&mut draft.body, facts, &mut preserved);
    for target in preserved {
        draft
            .inline_dispositions
            .preserve_local(target, HirInlineRetentionReason::PhysicalFramePrefix);
    }
    draft
}
