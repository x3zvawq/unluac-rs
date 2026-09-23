//! 核对展开帧后仍保留的 Luau 数值循环及无 scratch 控制边界。
//!
//! 循环 binding 只作为直接实参使用时，不给 O2 展开带来常量折扣；成本下界与
//! 已恢复的原控制槽共同限制候选，最终源码仍由 Generate 再核对。
use super::*;

pub(super) fn leaf_unchanged(proto: &HirProto) -> bool {
    if proto.signature.is_vararg || !proto.children.is_empty() || !proto.upvalues.is_empty() {
        return false;
    }
    let [HirStmt::Return(ret)] = proto.body.stmts.as_slice() else {
        return false;
    };
    let ([HirExpr::Binary(binary)], None) = (ret.values.fixed.as_slice(), &ret.values.tail) else {
        return false;
    };
    binary.op == crate::hir::HirBinaryOpKind::Add
        && matches!(binary.lhs, HirExpr::ParamRef(_))
        && matches!(binary.rhs, HirExpr::Integer(_) | HirExpr::Number(_))
}

fn no_index(expr: &HirExpr, index: LocalId) -> bool {
    match expr {
        HirExpr::LocalRef(local) => *local != index,
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_) => true,
        HirExpr::Unary(unary) => {
            unary.op == crate::hir::HirUnaryOpKind::Not && no_index(&unary.expr, index)
        }
        HirExpr::Binary(binary) => {
            matches!(
                binary.op,
                crate::hir::HirBinaryOpKind::Eq
                    | crate::hir::HirBinaryOpKind::Lt
                    | crate::hir::HirBinaryOpKind::Le
                    | crate::hir::HirBinaryOpKind::Gt
                    | crate::hir::HirBinaryOpKind::Ge
            ) && no_index(&binary.lhs, index)
                && no_index(&binary.rhs, index)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            no_index(&logical.lhs, index) && no_index(&logical.rhs, index)
        }
        _ => false,
    }
}

pub(super) fn direct_condition(expr: &HirExpr, facts: &ProtoPromotionFacts) -> bool {
    let mut expr = expr;
    while let HirExpr::Unary(unary) = expr {
        if unary.source_site.is_some() || unary.op != crate::hir::HirUnaryOpKind::Not {
            return false;
        }
        expr = &unary.expr;
    }
    let HirExpr::Binary(binary) = expr else {
        return false;
    };
    let (HirExpr::LocalRef(local), HirExpr::Nil) = (&binary.lhs, &binary.rhs) else {
        return false;
    };
    binary.op == crate::hir::HirBinaryOpKind::Eq
        && facts.native_binary_layout(binary).is_some_and(|layout| {
            layout.lhs == facts.trusted_local_home_slot(*local)
                && layout.lhs.is_some()
                && layout.rhs.is_none()
        })
}

pub(super) fn loops_unchanged(proto: &HirProto, leaves: &[bool]) -> bool {
    proto.body.stmts.iter().all(|stmt| {
        let HirStmt::NumericFor(loop_) = stmt else {
            return true;
        };
        let (HirExpr::Integer(start), HirExpr::Integer(limit), HirExpr::Integer(step)) =
            (&loop_.start, &loop_.limit, &loop_.step)
        else {
            return false;
        };
        let mut written = BTreeSet::new();
        collect_writes(&loop_.body, &mut written);
        loop_cost(&loop_.body, loop_.binding, &written, leaves).is_some_and(|cost| {
            crate::hir::common::luau_loop_unroll_blocked(*start, *limit, *step, cost)
        })
    })
}

fn loop_cost(
    block: &HirBlock,
    index: LocalId,
    written: &BTreeSet<LocalId>,
    leaves: &[bool],
) -> Option<usize> {
    let mut cost = 0usize;
    for stmt in &block.stmts {
        cost = cost.saturating_add(match stmt {
            HirStmt::LocalDecl(decl) => {
                let ([local], [HirExpr::Closure(closure)], None) = (
                    decl.bindings.as_slice(),
                    decl.values.fixed.as_slice(),
                    &decl.values.tail,
                ) else {
                    return None;
                };
                if *local == index
                    || !closure.captures.is_empty()
                    || !leaves[closure.proto.index()]
                    || !matches!(
                        closure.creation,
                        Some(crate::hir::HirClosureCreation::MayReuse { .. })
                    )
                {
                    return None;
                }
                10
            }
            HirStmt::Assign(assign) => {
                let ([HirLValue::Local(target)], [HirExpr::LocalRef(source)], None) = (
                    assign.targets.as_slice(),
                    assign.values.fixed.as_slice(),
                    &assign.values.tail,
                ) else {
                    return None;
                };
                if *target == index || *source == index {
                    return None;
                }
                1
            }
            HirStmt::CallStmt(stmt) => {
                let call = &stmt.call;
                let HirExpr::GlobalRef(name) = &call.callee else {
                    return None;
                };
                let name = name.key.as_utf8()?;
                if !matches!(name, "assert" | "print")
                    || call.required_luau_inlining.is_some()
                    || call.args.tail.is_some()
                    || !call
                        .args
                        .fixed
                        .iter()
                        .all(|arg| *arg == HirExpr::LocalRef(index) || no_index(arg, index))
                {
                    return None;
                }
                if name == "assert" { 2 } else { 3 }
            }
            HirStmt::If(branch) => {
                let (condition, _) = synthetic_not_subject(&branch.cond);
                let HirExpr::Binary(binary) = condition else {
                    return None;
                };
                if !no_index(&branch.cond, index)
                    || !matches!(binary.lhs, HirExpr::LocalRef(local) if written.contains(&local))
                    || !matches!(binary.rhs, HirExpr::Nil)
                {
                    return None;
                }
                1 + usize::from(branch.else_block.is_some())
                    + loop_cost(&branch.then_block, index, written, leaves)?
                    + branch
                        .else_block
                        .as_ref()
                        .map_or(Some(0), |block| loop_cost(block, index, written, leaves))?
            }
            _ => return None,
        });
    }
    Some(cost)
}

fn collect_writes(block: &HirBlock, written: &mut BTreeSet<LocalId>) {
    for stmt in &block.stmts {
        match stmt {
            HirStmt::Assign(assign) => {
                for target in &assign.targets {
                    if let HirLValue::Local(local) = target {
                        written.insert(*local);
                    }
                }
            }
            HirStmt::If(branch) => {
                collect_writes(&branch.then_block, written);
                if let Some(block) = &branch.else_block {
                    collect_writes(block, written);
                }
            }
            _ => {}
        }
    }
}
