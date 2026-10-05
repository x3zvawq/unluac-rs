//! 在最终 AST 验证表达式调用外围的循环成本和参数常量折扣。
//! 与 HIR 共用 pinned 成本运算；声明、调用和原结果槽仍由主验证器逐项检查。

use super::*;
use crate::ast::traverse::traverse_stmt_children;
use crate::hir::luau_loop_cost::{Cost, trips};

pub(super) fn bindings(body: &AstBlock) -> BTreeSet<crate::hir::LocalId> {
    let mut pending = vec![body];
    let mut bindings = BTreeSet::new();
    while let Some(block) = pending.pop() {
        for stmt in &block.stmts {
            match stmt {
                AstStmt::LocalFunctionDecl(decl)
                    if matches!(decl.name, AstBindingRef::Local(_)) =>
                {
                    let AstBindingRef::Local(local) = decl.name else {
                        unreachable!()
                    };
                    bindings.insert(local);
                }
                AstStmt::LocalDecl(decl) => {
                    if let ([binding], [value]) = (decl.bindings.as_slice(), decl.values.as_slice())
                        && let AstBindingRef::Local(local) = binding.id
                        && (matches!(
                            value,
                            AstExpr::TableConstructor(_) | AstExpr::FunctionExpr(_)
                        ) || matches!(value, AstExpr::IndexAccess(access) if matches!(access.index, AstExpr::Var(AstNameRef::Local(_)))))
                    {
                        bindings.insert(local);
                    }
                }
                // 泛型循环没有常量展开，绑定由每轮 iterator dispatch 产生。
                AstStmt::GenericFor(loop_) => {
                    bindings.extend(loop_.bindings.iter().filter_map(|binding| match binding {
                        AstBindingRef::Local(local) => Some(*local),
                        _ => None,
                    }));
                }
                _ => {}
            }
            if let AstStmt::NumericFor(loop_) = stmt
                && let AstBindingRef::Local(local) = loop_.binding
            {
                bindings.insert(local);
            }
            traverse_stmt_children!(stmt, iter=iter, opt=as_ref, borrow=[&],
                expr(_expr) => {}, lvalue(_lvalue) => {}, block(block) => { pending.push(block); },
                function(_function) => {}, condition(_condition) => {}, call(_call) => {});
        }
    }
    bindings
}

struct Environment<'a> {
    bindings: &'a BTreeSet<crate::hir::LocalId>,
    index: crate::hir::LocalId,
    locals: BTreeMap<crate::hir::LocalId, Cost>,
}

fn expression(value: &AstExpr, locals: &Environment<'_>) -> Option<Cost> {
    match value {
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_) => Some(Cost::literal()),
        AstExpr::Var(AstNameRef::Local(local)) => locals.locals.get(local).copied().or_else(|| {
            locals
                .bindings
                .contains(local)
                .then(|| Cost::variable(*local == locals.index))
        }),
        AstExpr::Binary(binary)
            if matches!(
                binary.op,
                AstBinaryOpKind::Eq
                    | AstBinaryOpKind::Lt
                    | AstBinaryOpKind::Le
                    | AstBinaryOpKind::Gt
                    | AstBinaryOpKind::Ge
            ) =>
        {
            expression(&binary.lhs, locals)?.fold(expression(&binary.rhs, locals)?, false)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            expression(&logical.lhs, locals)?.fold(expression(&logical.rhs, locals)?, true)
        }
        AstExpr::Call(call) => invocation(call, locals),
        AstExpr::SingleValue(value) => expression(value, locals),
        AstExpr::IndexAccess(access)
            if matches!(access.base, AstExpr::Var(AstNameRef::Local(_)))
                && matches!(access.index, AstExpr::Var(AstNameRef::Local(_))) =>
        {
            Some(expression(&access.index, locals)?.add(Cost::fixed(1)))
        }
        AstExpr::TableConstructor(table) => {
            table
                .fields
                .iter()
                .try_fold(Cost::fixed(10), |cost, field| {
                    let value = match field {
                        AstTableField::Array(value) => expression(value, locals)?,
                        AstTableField::Record(record) => {
                            let key = match &record.key {
                                AstTableKey::Name(_) => Cost::literal(),
                                AstTableKey::Expr(key) => expression(key, locals)?,
                            };
                            key.add(expression(&record.value, locals)?)
                        }
                    };
                    Some(cost.add(value).add(Cost::fixed(1)))
                })
        }
        AstExpr::FunctionExpr(_) => Some(Cost::fixed(10)),
        _ => None,
    }
}

fn invocation(call: &AstCallExpr, locals: &Environment<'_>) -> Option<Cost> {
    if call.method_key.is_some() {
        return None;
    }
    let (base, copies) = match &call.callee {
        AstExpr::Var(AstNameRef::Local(_)) if expression(&call.callee, locals).is_some() => {
            (3, true)
        }
        AstExpr::Var(AstNameRef::Global(name))
            if matches!(
                name.text.as_str(),
                "assert" | "rawequal" | "type" | "setmetatable"
            ) && call.args.len() <= 2 =>
        {
            (2, false)
        }
        AstExpr::Var(AstNameRef::Global(name)) if name.text == "print" => (4, true),
        AstExpr::Var(AstNameRef::Global(name))
            if name.text == "select"
                && matches!(call.args.as_slice(), [AstExpr::String(marker), value] if marker.as_utf8() == Some("#") && !matches!(value, AstExpr::VarArg)) =>
        {
            (4, true)
        }
        _ => return None,
    };
    let mut cost = Cost::fixed(base);
    for argument in &call.args {
        let value = expression(argument, locals)?;
        cost = cost.add(if copies { value.argument() } else { value });
    }
    Some(cost)
}

fn bounds(loop_: &AstNumericFor) -> Option<(i64, i64, i64)> {
    match (&loop_.start, &loop_.limit, &loop_.step) {
        (AstExpr::Integer(start), AstExpr::Integer(limit), AstExpr::Integer(step)) => {
            Some((*start, *limit, *step))
        }
        _ => None,
    }
}

fn block_cost(block: &AstBlock, locals: &mut Environment<'_>, depth: usize) -> Option<Cost> {
    if depth > 128 {
        return None;
    }
    let mut saved = Vec::new();
    let result = (|| {
        let mut total = Cost::fixed(0);
        for stmt in &block.stmts {
            total = total.add(match stmt {
                AstStmt::LocalFunctionDecl(decl) => {
                    let AstBindingRef::Local(local) = decl.name else {
                        return None;
                    };
                    saved.push((local, locals.locals.insert(local, Cost::variable(false))));
                    Cost::fixed(10)
                }
                AstStmt::LocalDecl(decl) => {
                    if let [AstExpr::Call(call)] = decl.values.as_slice()
                        && call.required_luau_inlining.is_some()
                        && decl.bindings.len() == 2
                    {
                        let cost = invocation(call, locals)?;
                        for binding in &decl.bindings {
                            let AstBindingRef::Local(local) = binding.id else {
                                return None;
                            };
                            saved.push((local, locals.locals.insert(local, Cost::variable(false))));
                        }
                        total = total.add(cost);
                        continue;
                    }
                    let ([binding], [value]) = (decl.bindings.as_slice(), decl.values.as_slice())
                    else {
                        return None;
                    };
                    let AstBindingRef::Local(local) = binding.id else {
                        return None;
                    };
                    let cost = expression(value, locals)?;
                    saved.push((local, locals.locals.insert(local, cost.local())));
                    cost
                }
                AstStmt::CallStmt(stmt) => {
                    let AstCallKind::Call(call) = &stmt.call else {
                        return None;
                    };
                    invocation(call, locals)?
                }
                AstStmt::Assign(assign) => {
                    if let (
                        [
                            AstLValue::Name(AstNameRef::Local(a)),
                            AstLValue::Name(AstNameRef::Local(b)),
                        ],
                        [AstExpr::Call(call)],
                    ) = (assign.targets.as_slice(), assign.values.as_slice())
                        && call.required_luau_inlining.is_some()
                    {
                        for local in [a, b] {
                            locals.locals.insert(*local, Cost::variable(false));
                        }
                        total = total.add(invocation(call, locals)?.add(Cost::fixed(1)));
                        continue;
                    }
                    let ([target], [value]) = (assign.targets.as_slice(), assign.values.as_slice())
                    else {
                        return None;
                    };
                    match target {
                        AstLValue::Name(AstNameRef::Local(local)) => {
                            locals.locals.insert(*local, Cost::variable(false));
                            expression(value, locals)?.argument()
                        }
                        AstLValue::IndexAccess(access)
                            if matches!(access.base, AstExpr::Var(AstNameRef::Local(_)))
                                && matches!(access.index, AstExpr::Var(AstNameRef::Local(_))) =>
                        {
                            expression(&access.base, locals)?
                                .add(expression(&access.index, locals)?)
                                .add(Cost::fixed(1))
                                .add(expression(value, locals)?)
                        }
                        _ => return None,
                    }
                }
                AstStmt::If(branch) => {
                    let condition = expression(&branch.cond, locals)?;
                    if condition.is_constant() {
                        return None;
                    }
                    let else_jump = branch
                        .else_block
                        .as_ref()
                        .is_some_and(|other| !matches!(other.stmts.as_slice(), [AstStmt::If(_)]));
                    let mut cost = condition
                        .add(Cost::fixed(1 + usize::from(else_jump)))
                        .add(block_cost(&branch.then_block, locals, depth + 1)?);
                    if let Some(other) = &branch.else_block {
                        cost = cost.add(block_cost(other, locals, depth + 1)?);
                    }
                    cost
                }
                AstStmt::NumericFor(loop_) => {
                    let (start, limit, step) = bounds(loop_)?;
                    block_cost(&loop_.body, locals, depth + 1)?
                        .add(Cost::fixed(1))
                        .multiply(trips(start, limit, step)?)
                }
                AstStmt::DoBlock(block) => block_cost(block, locals, depth + 1)?,
                _ => return None,
            });
        }
        Some(total)
    })();
    for (local, previous) in saved.into_iter().rev() {
        if let Some(previous) = previous {
            locals.locals.insert(local, previous);
        } else {
            locals.locals.remove(&local);
        }
    }
    result
}

pub(super) fn unchanged(
    loop_: &AstNumericFor,
    bindings: &BTreeSet<crate::hir::LocalId>,
    mandatory: Option<Cost>,
) -> bool {
    let Some((start, limit, step)) = bounds(loop_) else {
        return false;
    };
    let Some(count) = trips(start, limit, step) else {
        return false;
    };
    if count > 25 {
        return true;
    }
    if mandatory.is_some_and(|cost| cost.blocks_unroll_at_max_profit(count)) {
        return true;
    }
    if let Some(AstStmt::NumericFor(inner)) = loop_.body.stmts.first()
        && let Some((from, to, step)) = bounds(inner)
        && let Some(inner_count) = trips(from, to, step)
        && crate::hir::luau_loop_cost::mandatory_inner_loop_blocks_unroll(count, inner_count)
    {
        return true;
    }
    let AstBindingRef::Local(index) = loop_.binding else {
        return false;
    };
    let mut locals = Environment {
        bindings,
        index,
        locals: BTreeMap::new(),
    };
    block_cost(&loop_.body, &mut locals, 0)
        .is_some_and(|cost| cost.blocks_unroll(start, limit, step))
}

/// 与 HIR 一样只计不可常量求值的必经分配和观察；在最终 AST 重算，
/// 不沿用表达式改写之前的下界。所有嵌套循环通过一次后序遍历共享结果。
pub(super) fn mandatory_costs(body: &AstBlock) -> BTreeMap<crate::hir::LocalId, Cost> {
    fn functions(body: &AstBlock, known: &mut BTreeSet<crate::hir::LocalId>) {
        for stmt in &body.stmts {
            if let AstStmt::LocalFunctionDecl(decl) = stmt
                && let AstBindingRef::Local(local) = decl.name
            {
                known.insert(local);
            }
            traverse_stmt_children!(stmt, iter=iter, opt=as_ref, borrow=[&],
                expr(_expr) => {}, lvalue(_lvalue) => {}, block(block) => { functions(block, known); },
                function(_function) => {}, condition(_condition) => {}, call(_call) => {});
        }
    }
    fn expr(value: &AstExpr, functions: &BTreeSet<crate::hir::LocalId>) -> Cost {
        match value {
            AstExpr::FunctionExpr(_) => Cost::fixed(10),
            AstExpr::TableConstructor(table) => {
                table.fields.iter().fold(Cost::fixed(10), |cost, field| {
                    cost.add(match field {
                        AstTableField::Array(value) => expr(value, functions),
                        AstTableField::Record(record) => {
                            expr(&record.value, functions).add(match &record.key {
                                AstTableKey::Name(_) => Cost::fixed(0),
                                AstTableKey::Expr(key) => expr(key, functions),
                            })
                        }
                    })
                })
            }
            AstExpr::Call(call) => {
                let base = match &call.callee {
                    AstExpr::Var(AstNameRef::Local(local)) if functions.contains(local) => 3,
                    AstExpr::Var(AstNameRef::Global(name)) if name.text == "print" => 4,
                    AstExpr::Var(AstNameRef::Global(name))
                        if matches!(name.text.as_str(), "assert" | "setmetatable") =>
                    {
                        2
                    }
                    _ => 0,
                };
                call.args.iter().fold(Cost::fixed(base), |cost, value| {
                    cost.add(expr(value, functions))
                })
            }
            AstExpr::Binary(binary) => {
                expr(&binary.lhs, functions).add(expr(&binary.rhs, functions))
            }
            AstExpr::Unary(unary) => expr(&unary.expr, functions),
            AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
                expr(&logical.lhs, functions)
            }
            AstExpr::SingleValue(value) => expr(value, functions),
            _ => Cost::fixed(0),
        }
    }
    fn block(
        body: &AstBlock,
        functions: &BTreeSet<crate::hir::LocalId>,
        loops: &mut BTreeMap<crate::hir::LocalId, Cost>,
    ) -> (Cost, bool) {
        let mut cost = Cost::fixed(0);
        let mut exits = false;
        for stmt in &body.stmts {
            let (item, stops) = match stmt {
                AstStmt::NumericFor(loop_) => {
                    let (body, _) = block(&loop_.body, functions, loops);
                    if let AstBindingRef::Local(local) = loop_.binding {
                        loops.insert(local, body);
                    }
                    (
                        bounds(loop_)
                            .and_then(|(a, b, c)| trips(a, b, c))
                            .map_or(Cost::fixed(0), |count| {
                                body.add(Cost::fixed(1)).multiply(count)
                            }),
                        false,
                    )
                }
                AstStmt::If(branch) => {
                    let (_, left) = block(&branch.then_block, functions, loops);
                    let right = branch
                        .else_block
                        .as_ref()
                        .is_some_and(|other| block(other, functions, loops).1);
                    (Cost::fixed(0), left || right)
                }
                AstStmt::DoBlock(child) => block(child, functions, loops),
                AstStmt::Break | AstStmt::Continue | AstStmt::Return(_) => (Cost::fixed(0), true),
                AstStmt::LocalDecl(decl) => (
                    decl.values.iter().fold(Cost::fixed(0), |cost, value| {
                        cost.add(expr(value, functions))
                    }),
                    false,
                ),
                AstStmt::Assign(assign) => (
                    assign.values.iter().fold(Cost::fixed(0), |cost, value| {
                        cost.add(expr(value, functions))
                    }),
                    false,
                ),
                AstStmt::CallStmt(call) => (
                    match &call.call {
                        AstCallKind::Call(call) => expr(&AstExpr::Call(call.clone()), functions),
                        _ => Cost::fixed(0),
                    },
                    false,
                ),
                _ => {
                    traverse_stmt_children!(stmt, iter=iter, opt=as_ref, borrow=[&],
                        expr(_expr) => {}, lvalue(_lvalue) => {}, block(child) => { block(child, functions, loops); },
                        function(_function) => {}, condition(_condition) => {}, call(_call) => {});
                    (Cost::fixed(0), true)
                }
            };
            if !exits {
                cost = cost.add(item);
            }
            exits |= stops;
        }
        (cost, exits)
    }
    let mut known = BTreeSet::new();
    functions(body, &mut known);
    let mut loops = BTreeMap::new();
    block(body, &known, &mut loops);
    loops
}
