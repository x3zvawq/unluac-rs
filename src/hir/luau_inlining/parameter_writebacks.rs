//! 描述封闭函数中比较后重写同一参数的字面量选值。
//! 同一计算可保留两个写回或已树化为单个 RHS；原程序与调用帧另由 Promotion 证明。

use super::*;
use crate::hir::{HirBinaryExpr, HirBinaryOpKind, HirLValue};

pub(crate) fn parameter_writeback_template(
    proto: &HirProto,
) -> Option<(&HirBinaryExpr, [&HirExpr; 2])> {
    if proto.params.as_slice() != [ParamId(0), ParamId(1), ParamId(2)]
        || proto.signature.is_vararg
        || !proto.upvalues.is_empty()
        || !proto.children.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    let (HirStmt::Return(ret), writes) = proto.body.stmts.split_last()? else {
        return None;
    };
    if ret.values.tail.is_some()
        || ret.values.fixed != [HirExpr::ParamRef(ParamId(0))]
        || ret.pending_cleanup_source.is_some()
    {
        return None;
    }
    let write = |stmt: &HirStmt| {
        matches!(stmt, HirStmt::Assign(assign)
        if assign.targets == [HirLValue::Param(ParamId(0))] && assign.values.fixed.len() == 1
            && assign.values.tail.is_none() && !assign.is_phi_transfer
            && assign.initializer_merge_transaction.is_none())
    };
    if !writes.iter().all(write) {
        return None;
    }
    let (compare, values) = match writes {
        [HirStmt::Assign(value)] => {
            let (HirExpr::Binary(compare), values) = selection(&value.values.fixed[0])? else {
                return None;
            };
            (compare.as_ref(), values)
        }
        [HirStmt::Assign(first), HirStmt::Assign(second)] => {
            let HirExpr::Binary(compare) = &first.values.fixed[0] else {
                return None;
            };
            let (input, values) = selection(&second.values.fixed[0])?;
            if *input != HirExpr::ParamRef(ParamId(0)) {
                return None;
            }
            (compare.as_ref(), values)
        }
        _ => return None,
    };
    (matches!(
        compare.op,
        HirBinaryOpKind::Eq | HirBinaryOpKind::Lt | HirBinaryOpKind::Le
    ) && compare.lhs == HirExpr::ParamRef(ParamId(1))
        && compare.rhs == HirExpr::ParamRef(ParamId(2)))
    .then_some((compare, values))
}
