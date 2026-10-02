//! 描述按标签执行两次读取的封闭比较函数及其 trace 读取体。
//! 保留标签顺序、捕获角色和全部选值常量，供原操作匹配与最终源码验证共用。

use super::*;
use crate::hir::{HirBinaryOpKind, HirLValue};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct ObservedValueTemplate {
    pub tags: [LuaString; 2],
    pub inner: [i64; 2],
    pub outer: [i64; 2],
}

pub(crate) fn selection(value: &HirExpr) -> Option<(&HirExpr, [&HirExpr; 2])> {
    let HirExpr::LogicalOr(or) = value else {
        return None;
    };
    let HirExpr::LogicalAnd(and) = &or.lhs else {
        return None;
    };
    small_integer(&and.rhs)?;
    small_integer(&or.rhs)?;
    Some((&and.lhs, [&and.rhs, &or.rhs]))
}

pub(crate) fn observed_value_template(proto: &HirProto) -> Option<ObservedValueTemplate> {
    if proto.params.as_slice() != [ParamId(0), ParamId(1), ParamId(2)]
        || proto.signature.is_vararg
        || !proto.upvalues.is_empty()
        || !proto.children.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    let [HirStmt::Return(ret)] = proto.body.stmts.as_slice() else {
        return None;
    };
    let ([HirExpr::LogicalAnd(and)], None) = (ret.values.fixed.as_slice(), &ret.values.tail) else {
        return None;
    };
    let HirExpr::Binary(compare) = &and.rhs else {
        return None;
    };
    let (HirExpr::Binary(inner_compare), outer) = selection(&compare.rhs)? else {
        return None;
    };
    let (HirExpr::Call(left), inner) = selection(&inner_compare.lhs)? else {
        return None;
    };
    let (HirExpr::Call(right), other) = selection(&inner_compare.rhs)? else {
        return None;
    };
    if and.lhs != HirExpr::ParamRef(ParamId(0))
        || compare.op != HirBinaryOpKind::Eq
        || compare.lhs != HirExpr::ParamRef(ParamId(1))
        || inner_compare.op != HirBinaryOpKind::Eq
        || inner != other
        || ret.pending_cleanup_source.is_some()
    {
        return None;
    }
    let tag = |call: &crate::hir::HirCallExpr| -> Option<LuaString> {
        let [HirExpr::String(tag)] = call.args.fixed.as_slice() else {
            return None;
        };
        (call.callee == HirExpr::ParamRef(ParamId(2))
            && call.args.tail.is_none()
            && !call.is_method()
            && call.fastcall.is_none()
            && tag.as_bytes().len() <= 256)
            .then(|| tag.clone())
    };
    let tags = [tag(left)?, tag(right)?];
    if tags[0] == tags[1] {
        return None;
    }
    Some(ObservedValueTemplate {
        tags,
        inner: [small_integer(inner[0])?, small_integer(inner[1])?],
        outer: [small_integer(outer[0])?, small_integer(outer[1])?],
    })
}

#[derive(Clone)]
pub(crate) struct TracedReadTemplate {
    pub trace: UpvalueId,
    pub inputs: [UpvalueId; 2],
    pub tags: [LuaString; 2],
    pub values: [i64; 2],
}

pub(crate) fn traced_read_template(proto: &HirProto) -> Option<TracedReadTemplate> {
    if proto.params.as_slice() != [ParamId(0)]
        || proto.signature.is_vararg
        || proto.upvalues.len() != 3
        || !proto.children.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    let [HirStmt::Assign(update), HirStmt::Return(ret)] = proto.body.stmts.as_slice() else {
        return None;
    };
    let ([HirLValue::Upvalue(trace)], [HirExpr::Binary(concat)], None) = (
        update.targets.as_slice(),
        update.values.fixed.as_slice(),
        &update.values.tail,
    ) else {
        return None;
    };
    let ([HirExpr::LogicalOr(or)], None) = (ret.values.fixed.as_slice(), &ret.values.tail) else {
        return None;
    };
    if update.is_phi_transfer
        || update.initializer_merge_transaction.is_some()
        || concat.op != HirBinaryOpKind::Concat
        || concat.lhs != HirExpr::UpvalueRef(*trace)
        || concat.rhs != HirExpr::ParamRef(ParamId(0))
        || ret.pending_cleanup_source.is_some()
        || proto.mutable_upvalues.len() != 1
        || !proto.mutable_upvalues.contains(trace)
    {
        return None;
    }
    let arm = |value: &HirExpr| -> Option<(LuaString, UpvalueId, HirExpr)> {
        let HirExpr::LogicalAnd(and) = value else {
            return None;
        };
        let (HirExpr::Binary(key), HirExpr::Binary(compare)) = (&and.lhs, &and.rhs) else {
            return None;
        };
        let HirExpr::String(tag) = &key.rhs else {
            return None;
        };
        let HirExpr::UpvalueRef(input) = compare.lhs else {
            return None;
        };
        small_integer(&compare.rhs)?;
        (key.op == HirBinaryOpKind::Eq
            && key.lhs == HirExpr::ParamRef(ParamId(0))
            && compare.op == HirBinaryOpKind::Eq
            && tag.as_bytes().len() <= 256)
            .then(|| (tag.clone(), input, compare.rhs.clone()))
    };
    let left = arm(&or.lhs)?;
    let right = arm(&or.rhs)?;
    if left.0 == right.0
        || [*trace, left.1, right.1]
            .into_iter()
            .collect::<std::collections::BTreeSet<_>>()
            .len()
            != 3
    {
        return None;
    }
    Some(TracedReadTemplate {
        trace: *trace,
        inputs: [left.1, right.1],
        tags: [left.0, right.0],
        values: [small_integer(&left.2)?, small_integer(&right.2)?],
    })
}
