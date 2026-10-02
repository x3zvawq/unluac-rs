//! 描述通过函数参数读取捕获状态的完整短路函数体。
//! HIR 原槽验证和最终 AST 验证共享角色与字面量，操作来源仍由 Promotion 核对。

use super::*;
use crate::hir::{HirBinaryOpKind, HirBlock, HirLValue, LocalId};

fn literal(expr: &HirExpr) -> bool {
    matches!(
        expr,
        HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
    )
}

pub(crate) fn calling_value_fallback(proto: &HirProto) -> Option<&HirExpr> {
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
    let HirExpr::LogicalOr(or) = &compare.rhs else {
        return None;
    };
    let HirExpr::Call(call) = &or.lhs else {
        return None;
    };
    (and.lhs == HirExpr::ParamRef(ParamId(0))
        && compare.op == HirBinaryOpKind::Eq
        && compare.lhs == HirExpr::ParamRef(ParamId(1))
        && call.callee == HirExpr::ParamRef(ParamId(2))
        && call.args.is_empty()
        && !call.is_method()
        && call.fastcall.is_none()
        && ret.pending_cleanup_source.is_none()
        && literal(&or.rhs))
    .then_some(&or.rhs)
}

/// 读取结果具有独立源码身份，随后既参与比较又作为第二个返回值。
pub(crate) fn calling_read_pair(proto: &HirProto) -> Option<(LocalId, &HirExpr)> {
    if proto.params.as_slice() != [ParamId(0), ParamId(1), ParamId(2), ParamId(3)]
        || proto.signature.is_vararg
        || !proto.upvalues.is_empty()
        || !proto.children.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    let [HirStmt::LocalDecl(decl), HirStmt::Return(ret)] = proto.body.stmts.as_slice() else {
        return None;
    };
    let ([item], [HirExpr::Call(call)], None) = (
        decl.bindings.as_slice(),
        decl.values.fixed.as_slice(),
        &decl.values.tail,
    ) else {
        return None;
    };
    let ([HirExpr::LogicalAnd(and), second], None) =
        (ret.values.fixed.as_slice(), &ret.values.tail)
    else {
        return None;
    };
    let HirExpr::Binary(compare) = &and.rhs else {
        return None;
    };
    let HirExpr::LogicalOr(or) = &compare.rhs else {
        return None;
    };
    let HirExpr::LogicalAnd(pick) = &or.lhs else {
        return None;
    };
    (decl.initializer_merge_transaction.is_none()
        && decl.generic_for_initializer_producer.is_none()
        && call.callee == HirExpr::ParamRef(ParamId(2))
        && call.args.is_empty()
        && !call.is_method()
        && call.fastcall.is_none()
        && and.lhs == HirExpr::ParamRef(ParamId(0))
        && compare.op == HirBinaryOpKind::Eq
        && compare.lhs == HirExpr::ParamRef(ParamId(1))
        && pick.lhs == HirExpr::ParamRef(ParamId(3))
        && pick.rhs == HirExpr::LocalRef(*item)
        && *second == HirExpr::LocalRef(*item)
        && ret.pending_cleanup_source.is_none()
        && literal(&or.rhs))
    .then_some((*item, &or.rhs))
}

pub(crate) struct SharedReadTemplate<'a> {
    pub item: LocalId,
    pub tag: &'a LuaString,
    pub hit: &'a HirExpr,
    pub fallback: &'a HirExpr,
}

/// 一次急切读取同时参与选值和最终比较；参数短路不能消除这次读取。
pub(crate) fn calling_shared_value(proto: &HirProto) -> Option<SharedReadTemplate<'_>> {
    if proto.params.as_slice() != [ParamId(0), ParamId(1), ParamId(2)]
        || proto.signature.is_vararg
        || !proto.upvalues.is_empty()
        || !proto.children.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    let [HirStmt::LocalDecl(decl), HirStmt::Return(ret)] = proto.body.stmts.as_slice() else {
        return None;
    };
    let ([item], [HirExpr::Call(call)], None) = (
        decl.bindings.as_slice(),
        decl.values.fixed.as_slice(),
        &decl.values.tail,
    ) else {
        return None;
    };
    let ([HirExpr::LogicalAnd(final_)], None) = (ret.values.fixed.as_slice(), &ret.values.tail)
    else {
        return None;
    };
    let HirExpr::LogicalAnd(guard) = &final_.lhs else {
        return None;
    };
    let HirExpr::Binary(compare) = &guard.rhs else {
        return None;
    };
    let HirExpr::Binary(check) = &final_.rhs else {
        return None;
    };
    let HirExpr::LogicalOr(or) = &compare.rhs else {
        return None;
    };
    let HirExpr::LogicalAnd(pick) = &or.lhs else {
        return None;
    };
    let [HirExpr::String(tag)] = call.args.fixed.as_slice() else {
        return None;
    };
    (decl.initializer_merge_transaction.is_none()
        && decl.generic_for_initializer_producer.is_none()
        && call.callee == HirExpr::ParamRef(ParamId(2))
        && call.args.tail.is_none()
        && !call.is_method()
        && call.fastcall.is_none()
        && guard.lhs == HirExpr::ParamRef(ParamId(0))
        && compare.op == HirBinaryOpKind::Eq
        && compare.lhs == HirExpr::ParamRef(ParamId(1))
        && pick.lhs == HirExpr::LocalRef(*item)
        && check.op == HirBinaryOpKind::Eq
        && check.lhs == HirExpr::LocalRef(*item)
        && check.rhs == HirExpr::ParamRef(ParamId(1))
        && literal(&pick.rhs)
        && literal(&or.rhs)
        && ret.pending_cleanup_source.is_none())
    .then_some(SharedReadTemplate {
        item: *item,
        tag,
        hit: &pick.rhs,
        fallback: &or.rhs,
    })
}

#[derive(Debug, Clone)]
pub(crate) struct CapturedReadTemplate {
    pub counter: UpvalueId,
    pub index: UpvalueId,
    pub table: UpvalueId,
    pub increment: i64,
    pub key: i64,
    pub hit: HirExpr,
}

fn returned(block: &HirBlock) -> Option<&HirExpr> {
    let [HirStmt::Return(ret)] = block.stmts.as_slice() else {
        return None;
    };
    let ([value], None) = (ret.values.fixed.as_slice(), &ret.values.tail) else {
        return None;
    };
    ret.pending_cleanup_source.is_none().then_some(value)
}

pub(crate) fn captured_read_template(proto: &HirProto) -> Option<CapturedReadTemplate> {
    if !proto.params.is_empty()
        || proto.signature.is_vararg
        || proto.upvalues.len() != 3
        || !proto.children.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    let [HirStmt::Assign(update), HirStmt::If(branch)] = proto.body.stmts.as_slice() else {
        return None;
    };
    let ([HirLValue::Upvalue(counter)], [HirExpr::Binary(add)], None) = (
        update.targets.as_slice(),
        update.values.fixed.as_slice(),
        &update.values.tail,
    ) else {
        return None;
    };
    let mut condition = &branch.cond;
    let mut inverted = false;
    while let HirExpr::Unary(unary) = condition {
        if unary.source_site.is_some() || unary.op != HirUnaryOpKind::Not {
            return None;
        }
        inverted = !inverted;
        condition = &unary.expr;
    }
    let HirExpr::Binary(compare) = condition else {
        return None;
    };
    let HirExpr::UpvalueRef(index) = compare.lhs else {
        return None;
    };
    let left = returned(&branch.then_block)?;
    let right = returned(branch.else_block.as_ref()?)?;
    let (hit, lookup) = if inverted {
        (right, left)
    } else {
        (left, right)
    };
    let HirExpr::TableAccess(lookup) = lookup else {
        return None;
    };
    let HirExpr::UpvalueRef(table) = lookup.base else {
        return None;
    };
    if update.is_phi_transfer
        || update.initializer_merge_transaction.is_some()
        || add.op != HirBinaryOpKind::Add
        || add.lhs != HirExpr::UpvalueRef(*counter)
        || compare.op != HirBinaryOpKind::Eq
        || lookup.key != HirExpr::UpvalueRef(index)
        || !literal(hit)
        || [*counter, index, table]
            .into_iter()
            .collect::<std::collections::BTreeSet<_>>()
            .len()
            != 3
        || proto.mutable_upvalues.len() != 1
        || !proto.mutable_upvalues.contains(counter)
    {
        return None;
    }
    Some(CapturedReadTemplate {
        counter: *counter,
        index,
        table,
        increment: small_integer(&add.rhs)?,
        key: small_integer(&compare.rhs)?,
        hit: hit.clone(),
    })
}
