//! 嵌套数值遍历中按二维索引命中并更新结果的完整函数体合同。
//! HIR 与 Generate 共用状态、索引编码和展开成本；调用方另证各次读取及返回 COPY。

use super::*;
use crate::hir::{HirBinaryOpKind, HirLValue, LocalId};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct NestedSearchTemplate {
    pub initial: i64,
    pub scale: i64,
    pub needle: LuaString,
}

impl NestedSearchTemplate {
    pub fn value(&self, row: i64, column: i64) -> Option<i64> {
        row.checked_mul(self.scale)?.checked_add(column)
    }
}

/// pinned CostModel 对动态循环以三轮计费；正向 if 与反向 continue 两种源码形态
/// 都必须允许内联和双层展开，最终 AST 改写条件极性后仍消费同一合同。
pub(crate) fn nested_search_count(limit: i64) -> Option<usize> {
    use crate::hir::luau_loop_cost::{Cost, trips};
    let count = trips(1, limit, 1)?;
    if count == 0 || count > 25 {
        return None;
    }
    let update = Cost::variable(true)
        .fold(Cost::literal(), false)?
        .fold(Cost::variable(false), false)?
        .argument();
    [false, true]
        .into_iter()
        .all(|continued| {
            // 两次索引、相等比较与条件分支；continue 形式另有一次跳转。
            let body = Cost::fixed(4 + usize::from(continued)).add(update);
            let upper_body = Cost::fixed(6 + usize::from(continued));
            let outer = body.add(Cost::fixed(1)).multiply(count);
            let function = |iterations| {
                Cost::fixed(1).add(
                    upper_body
                        .add(Cost::fixed(1))
                        .multiply(iterations)
                        .add(Cost::fixed(1))
                        .multiply(iterations),
                )
            };
            !upper_body.blocks_unroll(1, limit, 1)
                && !outer.blocks_unroll(1, limit, 1)
                && function(count).permits_inline(function(3))
        })
        .then_some(count)
}

pub(crate) fn nested_search_template(proto: &HirProto) -> Option<NestedSearchTemplate> {
    if proto.params.as_slice() != [ParamId(0), ParamId(1)]
        || proto.signature.is_vararg
        || !proto.upvalues.is_empty()
        || !proto.children.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    let [
        HirStmt::LocalDecl(initial),
        HirStmt::NumericFor(outer),
        HirStmt::Return(ret),
    ] = proto.body.stmts.as_slice()
    else {
        return None;
    };
    let ([state], [value], None) = (
        initial.bindings.as_slice(),
        initial.values.fixed.as_slice(),
        &initial.values.tail,
    ) else {
        return None;
    };
    let [HirStmt::NumericFor(inner)] = outer.body.stmts.as_slice() else {
        return None;
    };
    for loop_ in [outer, inner] {
        if small_integer(&loop_.start) != Some(1)
            || small_integer(&loop_.step) != Some(1)
            || loop_.limit != HirExpr::ParamRef(ParamId(1))
        {
            return None;
        }
    }
    let (condition, update) = match inner.body.stmts.as_slice() {
        [HirStmt::If(branch)]
            if branch
                .else_block
                .as_ref()
                .is_none_or(|other| other.stmts.is_empty()) =>
        {
            let [HirStmt::Assign(update)] = branch.then_block.stmts.as_slice() else {
                return None;
            };
            (&branch.cond, update)
        }
        [HirStmt::If(branch), HirStmt::Assign(update)]
            if matches!(branch.then_block.stmts.as_slice(), [HirStmt::Continue])
                && branch
                    .else_block
                    .as_ref()
                    .is_none_or(|other| other.stmts.is_empty()) =>
        {
            let HirExpr::Unary(not) = &branch.cond else {
                return None;
            };
            if not.op != HirUnaryOpKind::Not {
                return None;
            }
            (&not.expr, update)
        }
        _ => return None,
    };
    let HirExpr::Binary(compare) = condition else {
        return None;
    };
    let (HirExpr::TableAccess(column), HirExpr::String(needle)) = (&compare.lhs, &compare.rhs)
    else {
        return None;
    };
    let HirExpr::TableAccess(row) = &column.base else {
        return None;
    };
    let [HirExpr::Binary(add)] = update.values.fixed.as_slice() else {
        return None;
    };
    let HirExpr::Binary(multiply) = &add.lhs else {
        return None;
    };
    if compare.op != HirBinaryOpKind::Eq
        || row.base != HirExpr::ParamRef(ParamId(0))
        || row.key != HirExpr::LocalRef(outer.binding)
        || column.key != HirExpr::LocalRef(inner.binding)
        || update.targets.as_slice() != [HirLValue::Local(*state)]
        || update.values.tail.is_some()
        || update.initializer_merge_transaction.is_some()
        || update.generic_for_initializer_producer.is_some()
        || update.root_release.is_some()
        || update.method_rewrite_transaction.is_some()
        || update.parallel_nil_frame.is_some()
        || add.op != HirBinaryOpKind::Add
        || add.rhs != HirExpr::LocalRef(inner.binding)
        || !(-32768..=32767).contains(&small_integer(&multiply.rhs)?)
        || multiply.op != HirBinaryOpKind::Mul
        || multiply.lhs != HirExpr::LocalRef(outer.binding)
        || [*state, outer.binding, inner.binding]
            .into_iter()
            .collect::<std::collections::BTreeSet<LocalId>>()
            .len()
            != 3
        || ret.values.fixed.as_slice() != [HirExpr::LocalRef(*state)]
        || ret.values.tail.is_some()
        || ret.pending_cleanup_source.is_some()
    {
        return None;
    }
    Some(NestedSearchTemplate {
        initial: small_integer(value)?,
        scale: small_integer(&multiply.rhs)?,
        needle: needle.clone(),
    })
}
