//! 在最终源码核对数值循环的 O2 展开边界。
//!
//! 只认无循环变量常量折扣的函数声明、调用及可变状态分支；成本取下界，不能依靠
//! 已被 AST 消除的计算提高阈值。调用和子函数本身还须满足外围 O2 不变合同。
use super::*;

pub(super) fn unchanged(
    loop_: &AstNumericFor,
    callees: &BTreeMap<crate::hir::LocalId, crate::hir::HirProtoRef>,
) -> bool {
    if !plain_block(&loop_.body, callees) {
        return false;
    }
    let (AstExpr::Integer(start), AstExpr::Integer(limit), AstExpr::Integer(step)) =
        (&loop_.start, &loop_.limit, &loop_.step)
    else {
        return false;
    };
    let mut written = BTreeSet::new();
    collect_writes(&loop_.body, &mut written);
    // 候选拒绝[TargetConstraint]：循环展开必须被 pinned 编译器的成本或迭代次数规则排除。
    cost(&loop_.body, loop_.binding, &written)
        .is_some_and(|cost| crate::hir::luau_loop_unroll_blocked(*start, *limit, *step, cost))
}

fn collect_writes(block: &AstBlock, written: &mut BTreeSet<crate::hir::LocalId>) {
    for stmt in &block.stmts {
        match stmt {
            AstStmt::Assign(assign) => {
                for target in &assign.targets {
                    if let AstLValue::Name(AstNameRef::Local(local)) = target {
                        written.insert(*local);
                    }
                }
            }
            AstStmt::If(branch) => {
                collect_writes(&branch.then_block, written);
                if let Some(block) = &branch.else_block {
                    collect_writes(block, written);
                }
            }
            _ => {}
        }
    }
}

fn no_index(value: &AstExpr, index: AstBindingRef) -> bool {
    match value {
        AstExpr::Var(name) => *name != index.to_name_ref(),
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_) => true,
        AstExpr::Unary(unary) => unary.op == AstUnaryOpKind::Not && no_index(&unary.expr, index),
        AstExpr::Binary(binary) => {
            matches!(
                binary.op,
                AstBinaryOpKind::Eq
                    | AstBinaryOpKind::Lt
                    | AstBinaryOpKind::Le
                    | AstBinaryOpKind::Gt
                    | AstBinaryOpKind::Ge
            ) && no_index(&binary.lhs, index)
                && no_index(&binary.rhs, index)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            no_index(&logical.lhs, index) && no_index(&logical.rhs, index)
        }
        _ => false,
    }
}

fn cost(
    block: &AstBlock,
    index: AstBindingRef,
    written: &BTreeSet<crate::hir::LocalId>,
) -> Option<usize> {
    let mut total = 0usize;
    for stmt in &block.stmts {
        total = total.saturating_add(match stmt {
            AstStmt::LocalFunctionDecl(decl) if decl.name != index
                && matches!(decl.func.creation, Some(crate::hir::HirClosureCreation::MayReuse { .. }))
                && decl.func.captured_bindings.is_empty() && decl.func.captured_params.is_empty() => 10,
            AstStmt::Assign(assign) => {
                let ([AstLValue::Name(target)], [AstExpr::Var(source)]) = (assign.targets.as_slice(), assign.values.as_slice()) else { return None; };
                if *target == index.to_name_ref() || *source == index.to_name_ref() { return None; }
                1
            }
            AstStmt::CallStmt(stmt) => {
                let AstCallKind::Call(call) = &stmt.call else { return None; };
                let AstExpr::Var(AstNameRef::Global(name)) = &call.callee else { return None; };
                if !matches!(name.text.as_str(), "assert" | "print")
                    || !call.args.iter().all(|arg| *arg == AstExpr::Var(index.to_name_ref()) || no_index(arg, index)) { return None; }
                if name.text == "assert" { 2 } else { 3 }
            }
            AstStmt::If(branch) => {
                let mut condition = &branch.cond;
                while let AstExpr::Unary(unary) = condition {
                    if unary.op != AstUnaryOpKind::Not { return None; }
                    condition = &unary.expr;
                }
                let AstExpr::Binary(binary) = condition else { return None; };
                if !no_index(&branch.cond, index)
                    || !matches!(binary.lhs, AstExpr::Var(AstNameRef::Local(local)) if written.contains(&local))
                    || !matches!(binary.rhs, AstExpr::Nil) { return None; }
                1 + usize::from(branch.else_block.is_some()) + cost(&branch.then_block, index, written)?
                    + branch.else_block.as_ref().map_or(Some(0), |block| cost(block, index, written))?
            }
            _ => return None,
        });
    }
    Some(total)
}
