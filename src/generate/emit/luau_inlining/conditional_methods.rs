//! 核对条件方法模板在最终 AST 上仍满足 Luau 内联成本与函数身份合同。

use super::*;

pub(super) fn body(func: &AstFunctionExpr, template: usize) -> bool {
    if func.function.index() != template
        || func.params.len() != 1
        || func.is_vararg
        || func.named_vararg.is_some()
        || !func.captured_bindings.is_empty()
        || !func.captured_params.is_empty()
        || !func.capture_write_names.is_empty()
    {
        return false;
    }
    let [
        AstStmt::LocalDecl(decl),
        AstStmt::If(branch),
        AstStmt::Return(ret),
    ] = func.body.stmts.as_slice()
    else {
        return false;
    };
    let ([binding], [initial @ AstExpr::FieldAccess(read)]) =
        (decl.bindings.as_slice(), decl.values.as_slice())
    else {
        return false;
    };
    let [returned @ AstExpr::FieldAccess(last)] = ret.values.as_slice() else {
        return false;
    };
    let [AstStmt::CallStmt(stmt)] = branch.then_block.stmts.as_slice() else {
        return false;
    };
    let AstCallKind::MethodCall(method) = &stmt.call else {
        return false;
    };
    let parameter = AstNameRef::Param(func.params[0]);
    let snapshot = binding.id.to_name_ref();
    if branch.else_block.is_some()
        || read.base != AstExpr::Var(parameter.clone())
        || last.base != read.base
        || method.receiver != read.base
        || method.args.len() > 16
        || !method.args.iter().all(|value| {
            matches!(
                value,
                AstExpr::Nil
                    | AstExpr::Boolean(_)
                    | AstExpr::Integer(_)
                    | AstExpr::Number(_)
                    | AstExpr::String(_)
            )
        })
    {
        return false;
    }
    let cost = || {
        Some(
            cost(initial, &parameter, &snapshot)?
                + cost(&branch.cond, &parameter, &snapshot)?
                + 1
                + 4
                + method.args.len()
                + cost(returned, &parameter, &snapshot)?,
        )
    };
    // 只使用基础阈值；源码可见的整个模板已计费，不依赖实参常量传播的折扣。
    cost().is_some_and(|cost| cost <= 25)
}

fn cost(expr: &AstExpr, parameter: &AstNameRef, snapshot: &AstNameRef) -> Option<usize> {
    Some(match expr {
        AstExpr::Var(name) if name == parameter || name == snapshot => 0,
        AstExpr::FieldAccess(field) => cost(&field.base, parameter, snapshot)? + 1,
        AstExpr::Unary(unary) if unary.op == AstUnaryOpKind::Not => {
            cost(&unary.expr, parameter, snapshot)? + 1
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            cost(&logical.lhs, parameter, snapshot)? + cost(&logical.rhs, parameter, snapshot)? + 1
        }
        _ => return None,
    })
}
