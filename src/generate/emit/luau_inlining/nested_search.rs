//! 核对二维数值查找的最终函数体、只读输入及有界展开成本。
//! 完整双循环及条件更新与 HIR 模板配对，不能只凭函数名或返回值接受调用恢复。

use super::counter_repeat::integer;
use super::*;
use crate::hir::luau_inlining::{
    NestedSearchTemplate, nested_search_count, nested_search_template,
};

fn shape(func: &AstFunctionExpr) -> Option<NestedSearchTemplate> {
    let [
        AstStmt::LocalDecl(initial),
        AstStmt::NumericFor(outer),
        AstStmt::Return(ret),
    ] = func.body.stmts.as_slice()
    else {
        return None;
    };
    let ([state], [value]) = (initial.bindings.as_slice(), initial.values.as_slice()) else {
        return None;
    };
    let [AstStmt::NumericFor(inner)] = outer.body.stmts.as_slice() else {
        return None;
    };
    let param = |index| AstExpr::Var(AstNameRef::Param(func.params[index]));
    for loop_ in [outer, inner] {
        if integer(&loop_.start) != Some(1)
            || integer(&loop_.step) != Some(1)
            || loop_.limit != param(1)
        {
            return None;
        }
    }
    let (condition, update, continued) = match inner.body.stmts.as_slice() {
        [AstStmt::If(branch)]
            if branch
                .else_block
                .as_ref()
                .is_none_or(|other| other.stmts.is_empty()) =>
        {
            let [AstStmt::Assign(update)] = branch.then_block.stmts.as_slice() else {
                return None;
            };
            (&branch.cond, update, false)
        }
        [AstStmt::If(branch), AstStmt::Assign(update)]
            if matches!(branch.then_block.stmts.as_slice(), [AstStmt::Continue])
                && branch
                    .else_block
                    .as_ref()
                    .is_none_or(|other| other.stmts.is_empty()) =>
        {
            (&branch.cond, update, true)
        }
        _ => return None,
    };
    let condition = if continued {
        let AstExpr::Unary(not) = condition else {
            return None;
        };
        if not.op != AstUnaryOpKind::Not {
            return None;
        }
        &not.expr
    } else {
        condition
    };
    let AstExpr::Binary(compare) = condition else {
        return None;
    };
    let (AstExpr::IndexAccess(column), AstExpr::String(needle)) = (&compare.lhs, &compare.rhs)
    else {
        return None;
    };
    let AstExpr::IndexAccess(row) = &column.base else {
        return None;
    };
    let [AstExpr::Binary(add)] = update.values.as_slice() else {
        return None;
    };
    let AstExpr::Binary(multiply) = &add.lhs else {
        return None;
    };
    if compare.op != AstBinaryOpKind::Eq
        || !compare.original_operation
        || !add.original_operation
        || !multiply.original_operation
        || row.base != param(0)
        || row.index != AstExpr::Var(outer.binding.to_name_ref())
        || column.index != AstExpr::Var(inner.binding.to_name_ref())
        || update.targets.as_slice() != [AstLValue::Name(state.id.to_name_ref())]
        || add.op != AstBinaryOpKind::Add
        || add.rhs != AstExpr::Var(inner.binding.to_name_ref())
        || multiply.op != AstBinaryOpKind::Mul
        || multiply.lhs != AstExpr::Var(outer.binding.to_name_ref())
        || [state.id, outer.binding, inner.binding]
            .into_iter()
            .collect::<BTreeSet<_>>()
            .len()
            != 3
        || ret.values.as_slice() != [AstExpr::Var(state.id.to_name_ref())]
    {
        return None;
    }
    Some(NestedSearchTemplate {
        initial: integer(value)?,
        scale: integer(&multiply.rhs)?,
        needle: needle.clone(),
    })
}

pub(super) fn body(func: &AstFunctionExpr, proto: &crate::hir::HirProto) -> bool {
    func.function == proto.id
        && func.params.len() == 2
        && !func.is_vararg
        && func.named_vararg.is_none()
        && func.captured_bindings.is_empty()
        && func.captured_params.is_empty()
        && func.capture_write_names.is_empty()
        && nested_search_template(proto)
            .is_some_and(|expected| shape(func).as_ref() == Some(&expected))
}

pub(super) fn arguments(args: &[AstExpr], written: &BTreeSet<crate::hir::LocalId>) -> bool {
    matches!(args, [AstExpr::Var(AstNameRef::Local(input)), limit]
        if !written.contains(input) && integer(limit).is_some_and(|limit| nested_search_count(limit).is_some()))
}
