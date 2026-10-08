//! 核对参数比较写回的最终函数体。
//! 只接受已签证的参数身份、比较与两臂常量，不增加捕获或改变返回参数。

use super::*;

pub(super) fn body(func: &AstFunctionExpr, proto: &crate::hir::HirProto) -> bool {
    let Some((expected, values)) = crate::hir::luau_inlining::parameter_writeback_template(proto)
    else {
        return false;
    };
    if func.function != proto.id || func.params != proto.params {
        return false;
    }
    let Some((AstStmt::Return(ret), writes)) = func.body.stmts.split_last() else {
        return false;
    };
    let param = |index| AstExpr::Var(AstNameRef::Param(func.params[index]));
    if ret.values != [param(0)] || !writes.iter().all(|stmt| matches!(stmt, AstStmt::Assign(assign)
        if assign.targets == [AstLValue::Name(AstNameRef::Param(func.params[0]))] && assign.values.len() == 1)) { return false; }
    let select = |value: &AstExpr| match value {
        AstExpr::LogicalOr(or) => matches!(&or.lhs, AstExpr::LogicalAnd(and)
            if counter_repeat::integer(&and.rhs) == crate::hir::luau_inlining::small_integer(values[0])
                && counter_repeat::integer(&or.rhs) == crate::hir::luau_inlining::small_integer(values[1])),
        _ => false,
    };
    let compare = match writes {
        [AstStmt::Assign(assign)] if select(&assign.values[0]) => {
            let AstExpr::LogicalOr(or) = &assign.values[0] else {
                unreachable!()
            };
            let AstExpr::LogicalAnd(and) = &or.lhs else {
                unreachable!()
            };
            &and.lhs
        }
        [AstStmt::Assign(first), AstStmt::Assign(second)] if select(&second.values[0]) => {
            let AstExpr::LogicalOr(or) = &second.values[0] else {
                unreachable!()
            };
            let AstExpr::LogicalAnd(and) = &or.lhs else {
                unreachable!()
            };
            if and.lhs != param(0) {
                return false;
            }
            &first.values[0]
        }
        _ => return false,
    };
    let AstExpr::Binary(compare) = compare else {
        return false;
    };
    let op = match expected.op {
        crate::hir::HirBinaryOpKind::Eq => AstBinaryOpKind::Eq,
        crate::hir::HirBinaryOpKind::Lt => AstBinaryOpKind::Lt,
        crate::hir::HirBinaryOpKind::Le => AstBinaryOpKind::Le,
        _ => return false,
    };
    compare.op == op && compare.lhs == param(1) && compare.rhs == param(2)
}
