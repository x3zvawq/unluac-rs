//! 索引嵌套函数的内联合同作用域，并证明其外围调用不会被额外内联。

use super::*;
use crate::ast::traverse::{
    traverse_call_children, traverse_expr_children, traverse_lvalue_children,
    traverse_stmt_children,
};

pub(super) fn functions(
    body: &AstBlock,
) -> BTreeMap<crate::hir::HirProtoRef, Vec<&AstFunctionExpr>> {
    enum Node<'a> {
        Block(&'a AstBlock),
        Expr(&'a AstExpr),
        Function(&'a AstFunctionExpr),
        Lvalue(&'a AstLValue),
        Call(&'a AstCallKind),
    }
    let mut pending = vec![Node::Block(body)];
    let mut result = BTreeMap::<_, Vec<_>>::new();
    while let Some(node) = pending.pop() {
        match node {
            Node::Block(block) => {
                for stmt in &block.stmts {
                    traverse_stmt_children!(stmt, iter=iter, opt=as_ref, borrow=[&],
                    expr(expr) => {pending.push(Node::Expr(expr));},
                    lvalue(value) => {pending.push(Node::Lvalue(value));},
                    block(block) => {pending.push(Node::Block(block));},
                    function(function) => {pending.push(Node::Function(function));},
                    condition(expr) => {pending.push(Node::Expr(expr));},
                    call(call) => {pending.push(Node::Call(call));});
                }
            }
            Node::Function(function) => {
                result.entry(function.function).or_default().push(function);
                pending.push(Node::Block(&function.body));
            }
            Node::Expr(value) => {
                traverse_expr_children!(value, iter=iter, borrow=[&],
                expr(expr) => {pending.push(Node::Expr(expr));},
                function(function) => {pending.push(Node::Function(function));});
            }
            Node::Lvalue(value) => {
                traverse_lvalue_children!(value, borrow=[&], expr(expr) => {pending.push(Node::Expr(expr));});
            }
            Node::Call(call) => {
                traverse_call_children!(call, iter=iter, borrow=[&], expr(expr) => {pending.push(Node::Expr(expr));});
            }
        }
    }
    result
}

pub(super) fn increment_identity(
    func: &AstFunctionExpr,
    capture: Option<crate::hir::LocalId>,
    increment: i64,
) -> bool {
    let Some(capture) = capture else { return false };
    if func.params.len() != 1
        || func.is_vararg
        || func.named_vararg.is_some()
        || func.captured_bindings != BTreeSet::from([AstBindingRef::Local(capture)])
        || !func.captured_params.is_empty()
        || func.capture_write_names != BTreeSet::from([AstNameRef::Local(capture)])
    {
        return false;
    }
    let [AstStmt::Assign(assign), AstStmt::Return(ret)] = func.body.stmts.as_slice() else {
        return false;
    };
    let [AstExpr::Binary(add)] = assign.values.as_slice() else {
        return false;
    };
    assign.targets.as_slice()
        == [AstLValue::Name(AstNameRef::Upvalue(crate::hir::UpvalueId(
            0,
        )))]
        && add.op == AstBinaryOpKind::Add
        && add.lhs == AstExpr::Var(AstNameRef::Upvalue(crate::hir::UpvalueId(0)))
        && (add.rhs == AstExpr::Integer(increment) || add.rhs == AstExpr::Number(increment as f64))
        && ret.values.as_slice() == [AstExpr::Var(AstNameRef::Param(func.params[0]))]
}

// 共享成本分析覆盖表、索引和调用；结构化模板另可用确定的成本下界证明。
// 下界中函数创建为 10，已签证的普通 local CALL 至少为 3；
// repeat 的 body 和 condition 在 pinned CostModel 中均按 3 倍计。无参数函数
// 没有实参常量折扣；成本至少 28 时已超过 25 * (cost + 3) / cost 的阈值。
pub(super) fn costly(func: &AstFunctionExpr) -> bool {
    fn expr(value: &AstExpr) -> u32 {
        let mut cost = if matches!(value, AstExpr::Call(call) if call.required_luau_inlining.is_some())
        {
            3u32
        } else {
            0
        };
        traverse_expr_children!(value, iter=iter, borrow=[&],
            expr(child) => { cost = cost.saturating_add(expr(child)); },
            function(_function) => {});
        cost.min(127)
    }
    fn block(body: &AstBlock) -> u32 {
        let mut cost = 0u32;
        for stmt in &body.stmts {
            cost = cost
                .saturating_add(match stmt {
                    AstStmt::LocalFunctionDecl(_) => 10,
                    AstStmt::Repeat(loop_) => 3 * (block(&loop_.body) + expr(&loop_.cond)),
                    AstStmt::If(branch) => {
                        let test = expr(&branch.cond);
                        // 只有包含不可常量折叠的签证调用时，成本模型才保证遍历两臂。
                        if test == 0 {
                            0
                        } else {
                            test + block(&branch.then_block)
                                + branch.else_block.as_ref().map_or(0, block)
                        }
                    }
                    AstStmt::DoBlock(body) => block(body),
                    AstStmt::Return(_) => break,
                    _ => 0,
                })
                .min(127);
        }
        cost
    }
    func.params.is_empty()
        && (constant_control::CostAnalysis::new(func)
            .cost(None)
            .is_some_and(|cost| !cost.permits_inline(cost))
            || block(&func.body) >= 28)
}

/// Boolean 实参预留结果槽后，按顺序准备 getter 的原 COPY；低槽引用和右侧
/// 内嵌常量不占准备区。只签发此只读模板，其余比较继续由既有 owner 核对。
pub(super) fn captured_value_slots(
    call: &AstCallExpr,
    active: usize,
    occurrences: &BTreeMap<crate::hir::HirSourceSite, crate::hir::LocalId>,
    bodies: &BTreeMap<crate::hir::LocalId, HirLuauInliningBody>,
    slots: &BTreeMap<crate::hir::HirSourceSite, crate::hir::HirLuauResultFrame>,
    seen: &mut BTreeSet<crate::hir::HirSourceSite>,
) -> bool {
    let getter = |value: &AstExpr| {
        let AstExpr::Call(call) = value else {
            return None;
        };
        let site = call.required_luau_inlining?;
        (occurrences.get(&site).and_then(|local| bodies.get(local))
            == Some(&HirLuauInliningBody::CapturedValue))
        .then_some(site)
    };
    for (argument, value) in call.args.iter().enumerate() {
        let mut pending = vec![value];
        while let Some(value) = pending.pop() {
            match value {
                AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
                    pending.extend([&logical.rhs, &logical.lhs]);
                }
                AstExpr::SingleValue(value) => pending.push(value),
                AstExpr::Unary(unary)
                    if unary.op == AstUnaryOpKind::Not && !unary.original_operation =>
                {
                    pending.push(&unary.expr);
                }
                AstExpr::Binary(binary)
                    if getter(&binary.lhs).is_some() || getter(&binary.rhs).is_some() =>
                {
                    if binary.op != AstBinaryOpKind::Eq {
                        return false;
                    }
                    let mut next = active + argument + 2;
                    for (side, value) in [&binary.lhs, &binary.rhs].into_iter().enumerate() {
                        if let Some(site) = getter(value) {
                            if slots.get(&site).map(|frame| frame.base) != Some(next)
                                || !seen.insert(site)
                            {
                                return false;
                            }
                            next += 1;
                        } else if !matches!(
                            value,
                            AstExpr::Var(AstNameRef::Local(_) | AstNameRef::Param(_))
                        ) && !(side == 1
                            && matches!(
                                value,
                                AstExpr::Nil
                                    | AstExpr::Boolean(_)
                                    | AstExpr::Integer(_)
                                    | AstExpr::Number(_)
                                    | AstExpr::String(_)
                            ))
                        {
                            return false;
                        }
                    }
                }
                _ => {}
            }
        }
    }
    true
}
