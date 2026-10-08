//! 核对封闭标量表达式模板的最终单返回值与无折扣成本。
//! 原输入、结果和内部控制区间由 HIR 签证；这里拒绝新增捕获、参数写入和未证明的表达式。

use super::*;

pub(super) fn body(func: &AstFunctionExpr, template: usize, parameters: usize) -> bool {
    if func.function.index() != template
        || func.params.len() != parameters
        || !(2..=4).contains(&parameters)
    {
        return false;
    }
    let [AstStmt::Return(ret)] = func.body.stmts.as_slice() else {
        return false;
    };
    let [value] = ret.values.as_slice() else {
        return false;
    };
    let mut budget = 25;
    fn check(value: &AstExpr, parameters: &[crate::hir::ParamId], budget: &mut usize) -> bool {
        if *budget == 0 {
            return false;
        }
        *budget -= 1;
        match value {
            AstExpr::Var(AstNameRef::Param(param)) => parameters.contains(param),
            AstExpr::Nil
            | AstExpr::Boolean(_)
            | AstExpr::Integer(_)
            | AstExpr::Number(_)
            | AstExpr::String(_) => true,
            AstExpr::Binary(binary) => {
                matches!(
                    binary.op,
                    AstBinaryOpKind::Eq | AstBinaryOpKind::Lt | AstBinaryOpKind::Le
                ) && check(&binary.lhs, parameters, budget)
                    && check(&binary.rhs, parameters, budget)
            }
            AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
                check(&logical.lhs, parameters, budget) && check(&logical.rhs, parameters, budget)
            }
            _ => false,
        }
    }
    check(value, &func.params, &mut budget)
}

pub(super) fn arguments(args: &[AstExpr], written: &BTreeSet<crate::hir::LocalId>) -> bool {
    args.iter().all(|arg| match arg {
        AstExpr::Var(AstNameRef::Local(local)) => !written.contains(local),
        // 参数准备必须保持求值；不准以常量实参触发模板内部折叠。
        AstExpr::Binary(binary) => {
            matches!(
                binary.op,
                AstBinaryOpKind::Eq | AstBinaryOpKind::Lt | AstBinaryOpKind::Le
            ) && matches!(binary.lhs, AstExpr::Var(_))
                && matches!(
                    binary.rhs,
                    AstExpr::Nil
                        | AstExpr::Boolean(_)
                        | AstExpr::Integer(_)
                        | AstExpr::Number(_)
                        | AstExpr::String(_)
                        | AstExpr::Var(_)
                )
        }
        _ => false,
    })
}
