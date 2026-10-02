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
    fn check(expr: &HirExpr, facts: &ProtoPromotionFacts, remaining: &mut usize) -> bool {
        if *remaining == 0 {
            return false;
        }
        *remaining -= 1;
        let mut expr = expr;
        while let HirExpr::Unary(unary) = expr {
            if unary.source_site.is_some() || unary.op != crate::hir::HirUnaryOpKind::Not {
                return false;
            }
            expr = &unary.expr;
        }
        if let HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) = expr {
            return check(&logical.lhs, facts, remaining) && check(&logical.rhs, facts, remaining);
        }
        let HirExpr::Binary(binary) = expr else {
            return false;
        };
        let HirExpr::LocalRef(local) = &binary.lhs else {
            return false;
        };
        binary.op == crate::hir::HirBinaryOpKind::Eq
            && matches!(
                binary.rhs,
                HirExpr::Nil
                    | HirExpr::Boolean(_)
                    | HirExpr::Integer(_)
                    | HirExpr::Number(_)
                    | HirExpr::String(_)
            )
            && facts.native_binary_layout(binary).is_some_and(|layout| {
                layout.lhs == facts.trusted_local_home_slot(*local)
                    && layout.lhs.is_some()
                    && layout.rhs.is_none()
            })
    }
    check(expr, facts, &mut 32)
}

/// 真值 TEST 直接读取原绑定，不从当前 LocalRef 形状猜测被测槽。
pub(super) fn direct_test(branch: &crate::hir::HirIf, facts: &ProtoPromotionFacts) -> bool {
    if direct_condition(&branch.cond, facts) {
        return true;
    }
    // 合并后的短路条件没有单个 predicate_source。这里只保留已有控制树：
    // 所有叶都是具有稳定 home 的当前 binding，synthetic NOT 只交换分支，
    // 因而发射 TEST 不分配 scratch；声明的实际栈位置仍由整批 prefix 核对。
    if matches!(
        branch.cond,
        HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_) | HirExpr::Unary(_)
    ) && predicate_reads_below(&branch.cond, facts, usize::MAX)
    {
        return true;
    }
    let HirExpr::LocalRef(local) = &branch.cond else {
        return false;
    };
    branch
        .predicate_source
        .and_then(|source| facts.original_truthy_input(source))
        .is_some_and(|(value, home)| {
            facts.promoted_local_for_temp(value) == Some(*local)
                && facts.trusted_local_home_slot(*local) == Some(home)
        })
}

/// 原 ADD/ADDK 对现有 local 原位更新，没有额外输入或结果准备槽。
pub(super) fn direct_increment(
    assign: &crate::hir::HirAssign,
    facts: &ProtoPromotionFacts,
) -> bool {
    let ([HirLValue::Local(local)], [HirExpr::Binary(binary)], None) = (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) else {
        return false;
    };
    let Some(home) = facts.trusted_local_home_slot(*local) else {
        return false;
    };
    !assign.is_phi_transfer
        && assign.initializer_merge_transaction.is_none()
        && binary.op == crate::hir::HirBinaryOpKind::Add
        && binary.lhs == HirExpr::LocalRef(*local)
        && facts.native_binary_layout(binary).is_some_and(|layout| {
            layout.lhs == Some(home)
                && facts.direct_binary_operand_home(binary, 0) == Some(home)
                && match binary.rhs {
                    HirExpr::Integer(_) | HirExpr::Number(_) => layout.rhs.is_none(),
                    HirExpr::LocalRef(local) => {
                        facts.trusted_local_home_slot(local).is_some_and(|rhs| {
                            layout.rhs == Some(rhs)
                                && facts.direct_binary_operand_home(binary, 1) == Some(rhs)
                        })
                    }
                    _ => false,
                }
        })
        && binary
            .source_site
            .and_then(|source| facts.operation_writeback(source))
            // 原结果可能只进入后继 phi，因而没有独立 promoted local；
            // 当前原位目标与已验证输入同一 binding，仍须写回原 home。
            .is_some_and(|(_, written)| written == home)
}

/// 原比较只读低槽/RK，Boolean 叶仍写已有结果 home；不引入或退休准备槽。
pub(super) fn direct_boolean_write(
    assign: &crate::hir::HirAssign,
    facts: &ProtoPromotionFacts,
) -> bool {
    let ([HirLValue::Local(local)], [value], None) = (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) else {
        return false;
    };
    if assign.is_phi_transfer || assign.initializer_merge_transaction.is_some() {
        return false;
    }
    direct_boolean_result(*local, value, facts)
}

pub(super) fn direct_boolean_result(
    local: LocalId,
    value: &HirExpr,
    facts: &ProtoPromotionFacts,
) -> bool {
    if !direct_condition(value, facts) {
        return false;
    }
    let HirExpr::Binary(binary) = synthetic_not_subject(value).0 else {
        return false;
    };
    let Some(result) = facts.comparison_result_temp(binary) else {
        return false;
    };
    let Some(home) = facts.trusted_local_home_slot(local) else {
        return false;
    };
    facts.promoted_local_for_temp(result) == Some(local)
        && facts.trusted_temp_home_slot(result) == Some(home)
        && facts
            .complete_temp_definition_write_homes(result)
            .iter()
            .copied()
            .eq([home])
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
