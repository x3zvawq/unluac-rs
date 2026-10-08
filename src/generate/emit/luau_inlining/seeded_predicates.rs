//! 核对字段谓词模板的最终 AST、Boolean 结果身份及无折扣内联成本。
//! 原读取顺序和返回 COPY 已由 HIR 整帧签证；这里不允许新捕获或额外求值形式。

use super::*;

pub(super) fn body(func: &AstFunctionExpr, template: usize) -> bool {
    if func.function.index() != template || func.params.len() != 1 {
        return false;
    }
    let Some(AstStmt::LocalDecl(decl)) = func.body.stmts.first() else {
        return false;
    };
    let ([binding], [AstExpr::Boolean(_)]) = (decl.bindings.as_slice(), decl.values.as_slice())
    else {
        return false;
    };
    if !matches!(func.body.stmts.last(), Some(AstStmt::Return(ret)) if ret.values.len() == 1) {
        return false;
    }
    let parameter = AstNameRef::Param(func.params[0]);
    let result = binding.id.to_name_ref();
    fn condition(expr: &AstExpr, parameter: &AstNameRef) -> Option<usize> {
        Some(match expr {
            AstExpr::FieldAccess(field) if field.base == AstExpr::Var(parameter.clone()) => 1,
            AstExpr::IndexAccess(index)
                if index.base == AstExpr::Var(parameter.clone())
                    && matches!(index.index, AstExpr::String(_)) =>
            {
                1
            }
            AstExpr::Unary(unary)
                if unary.op == AstUnaryOpKind::Not && !unary.original_operation =>
            {
                condition(&unary.expr, parameter)? + 1
            }
            AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
                condition(&logical.lhs, parameter)? + condition(&logical.rhs, parameter)? + 1
            }
            _ => return None,
        })
    }
    fn block(
        stmts: &[AstStmt],
        parameter: &AstNameRef,
        result: &AstNameRef,
        budget: &mut usize,
    ) -> Option<()> {
        for stmt in stmts {
            let cost = match stmt {
                AstStmt::Assign(assign)
                    if matches!((assign.targets.as_slice(),assign.values.as_slice()),
                    ([AstLValue::Name(target)], [AstExpr::Boolean(_)]) if target == result) =>
                {
                    1
                }
                AstStmt::Return(ret) if ret.values.as_slice() == [AstExpr::Var(result.clone())] => {
                    0
                }
                AstStmt::If(branch) => {
                    let else_jump = branch
                        .else_block
                        .as_ref()
                        .is_some_and(|other| !matches!(other.stmts.as_slice(), [AstStmt::If(_)]));
                    let cost = condition(&branch.cond, parameter)? + 1 + usize::from(else_jump);
                    block(&branch.then_block.stmts, parameter, result, budget)?;
                    if let Some(other) = &branch.else_block {
                        block(&other.stmts, parameter, result, budget)?;
                    }
                    cost
                }
                _ => return None,
            };
            *budget = budget.checked_sub(cost)?;
        }
        Some(())
    }
    // 候选拒绝[TargetConstraint]：含初始化的完整函数按基础阈值收费，不依赖实参常量折扣。
    block(&func.body.stmts[1..], &parameter, &result, &mut 24).is_some()
}

pub(super) fn arguments(args: &[AstExpr], written: &BTreeSet<crate::hir::LocalId>) -> bool {
    let [value] = args else {
        return false;
    };
    let value = match value {
        AstExpr::SingleValue(value) => value.as_ref(),
        value => value,
    };
    matches!(value, AstExpr::Var(AstNameRef::Local(local)) if !written.contains(local))
        || matches!(value, AstExpr::TableConstructor(_))
        || matches!(value, AstExpr::Call(call) if call.required_luau_inlining.is_none() && call.method_key.is_none())
}
