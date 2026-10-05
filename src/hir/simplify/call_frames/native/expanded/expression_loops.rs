//! 核对表达式内联帧外围数值循环的参数常量折扣。
//! 只消费当前标量声明、完整观察调用及嵌套数值循环，不以被优化掉的代码抬高成本。

use super::*;
use crate::hir::luau_loop_cost::{Cost, trips};

struct Environment<'a> {
    bindings: &'a BTreeSet<LocalId>,
    index: LocalId,
    locals: BTreeMap<LocalId, Cost>,
}

fn expression(value: &HirExpr, locals: &Environment<'_>) -> Option<Cost> {
    match value {
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_) => Some(Cost::literal()),
        HirExpr::LocalRef(local) => locals.locals.get(local).copied().or_else(|| {
            locals
                .bindings
                .contains(local)
                .then(|| Cost::variable(*local == locals.index))
        }),
        HirExpr::Binary(binary)
            if matches!(
                binary.op,
                crate::hir::HirBinaryOpKind::Eq
                    | crate::hir::HirBinaryOpKind::Lt
                    | crate::hir::HirBinaryOpKind::Le
                    | crate::hir::HirBinaryOpKind::Gt
                    | crate::hir::HirBinaryOpKind::Ge
            ) =>
        {
            expression(&binary.lhs, locals)?.fold(expression(&binary.rhs, locals)?, false)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expression(&logical.lhs, locals)?.fold(expression(&logical.rhs, locals)?, true)
        }
        HirExpr::Call(call) => invocation(call, locals),
        HirExpr::TableAccess(access)
            if matches!(access.base, HirExpr::LocalRef(_))
                && matches!(access.key, HirExpr::LocalRef(_)) =>
        {
            Some(expression(&access.key, locals)?.add(Cost::fixed(1)))
        }
        HirExpr::TableConstructor(table) if table.trailing_multivalue.is_none() => table
            .fields
            .iter()
            .try_fold(Cost::fixed(10), |cost, field| {
                let value = match field {
                    crate::hir::HirTableField::Array(value) => expression(value, locals)?,
                    crate::hir::HirTableField::Record(record) => {
                        expression(&record.key, locals)?.add(expression(&record.value, locals)?)
                    }
                };
                Some(cost.add(value).add(Cost::fixed(1)))
            }),
        HirExpr::Closure(_) => Some(Cost::fixed(10)),
        _ => None,
    }
}

fn invocation(call: &HirCallExpr, locals: &Environment<'_>) -> Option<Cost> {
    if call.is_method() {
        return None;
    }
    let (base, copies) = match &call.callee {
        HirExpr::LocalRef(_) if expression(&call.callee, locals).is_some() => (3, true),
        HirExpr::GlobalRef(global)
            if matches!(
                global.key.as_utf8(),
                Some("assert" | "rawequal" | "type" | "setmetatable")
            ) && call.fastcall.is_some()
                && call.args.fixed.len() + usize::from(call.args.tail.is_some()) <= 2 =>
        {
            (2, false)
        }
        HirExpr::GlobalRef(global) if global.key.as_utf8() == Some("print") => (4, true),
        HirExpr::GlobalRef(global)
            if global.key.as_utf8() == Some("select")
                && call.fastcall.is_none()
                && match (call.args.fixed.as_slice(), &call.args.tail) {
                    ([HirExpr::String(marker), _], None) => marker.as_utf8() == Some("#"),
                    ([HirExpr::String(marker)], Some(tail)) => {
                        marker.as_utf8() == Some("#") && matches!(tail.as_expr(), HirExpr::Call(_))
                    }
                    _ => false,
                } =>
        {
            (4, true)
        }
        _ => return None,
    };
    let mut cost = Cost::fixed(base);
    // pinned CostModel 按源码实参表达式收费；尾调用只计算一次，不按运行时返回数量展开。
    for argument in call
        .args
        .fixed
        .iter()
        .chain(call.args.tail.iter().map(|tail| tail.as_expr()))
    {
        let value = expression(argument, locals)?;
        cost = cost.add(if copies { value.argument() } else { value });
    }
    Some(cost)
}

fn bounds(loop_: &crate::hir::HirNumericFor) -> Option<(i64, i64, i64)> {
    match (&loop_.start, &loop_.limit, &loop_.step) {
        (HirExpr::Integer(start), HirExpr::Integer(limit), HirExpr::Integer(step)) => {
            Some((*start, *limit, *step))
        }
        _ => None,
    }
}

fn block_cost(block: &HirBlock, locals: &mut Environment<'_>, depth: usize) -> Option<Cost> {
    // 候选拒绝[ResourceLimit]：有界嵌套避免为每个循环反复扫描无界祖先域；Luau VM 的控制槽上限更低。
    if depth > 128 {
        return None;
    }
    let mut saved = Vec::new();
    let result = (|| {
        let mut total = Cost::fixed(0);
        for stmt in &block.stmts {
            total = total.add(match stmt {
                HirStmt::LocalDecl(decl) => {
                    if let ([], Some(tail)) = (decl.values.fixed.as_slice(), &decl.values.tail)
                        && tail.exact_width() == Some(2) && decl.bindings.len() == 2
                        && matches!(tail.as_expr(), HirExpr::Call(call) if call.required_luau_inlining.is_some())
                    {
                        let cost = expression(tail.as_expr(), locals)?;
                        for local in &decl.bindings {
                            saved.push((*local, locals.locals.insert(*local, Cost::variable(false))));
                        }
                        total = total.add(cost);
                        continue;
                    }
                    let ([local], [value], None) = (
                        decl.bindings.as_slice(),
                        decl.values.fixed.as_slice(),
                        &decl.values.tail,
                    ) else {
                        return None;
                    };
                    let cost = expression(value, locals)?;
                    saved.push((*local, locals.locals.insert(*local, cost.local())));
                    cost
                }
                HirStmt::CallStmt(stmt) => invocation(&stmt.call, locals)?,
                HirStmt::Assign(assign) => {
                    if let ([HirLValue::Local(a), HirLValue::Local(b)], [], Some(tail)) =
                        (assign.targets.as_slice(), assign.values.fixed.as_slice(), &assign.values.tail)
                        && tail.exact_width() == Some(2)
                        && matches!(tail.as_expr(), HirExpr::Call(call) if call.required_luau_inlining.is_some())
                    {
                        for local in [a, b] { locals.locals.insert(*local, Cost::variable(false)); }
                        // CostModel 对没有独立 RHS 的第二项写回收取一次 local COPY。
                        total = total.add(expression(tail.as_expr(), locals)?.add(Cost::fixed(1)));
                        continue;
                    }
                    let ([target], [value], None) = (
                        assign.targets.as_slice(),
                        assign.values.fixed.as_slice(),
                        &assign.values.tail,
                    ) else {
                        return None;
                    };
                    match target {
                        HirLValue::Local(local) => {
                            locals.locals.insert(*local, Cost::variable(false));
                            expression(value, locals)?.argument()
                        }
                        HirLValue::TableAccess(access) if matches!(access.base, HirExpr::LocalRef(_)) && matches!(access.key, HirExpr::LocalRef(_)) => {
                            expression(&access.base, locals)?.add(expression(&access.key, locals)?)
                                .add(Cost::fixed(1)).add(expression(value, locals)?)
                        }
                        _ => return None,
                    }
                }
                HirStmt::If(branch) => {
                    let condition = expression(&branch.cond, locals)?;
                    // 常量条件可能让编译器丢弃整臂；不能按两个正文收费阻止循环展开。
                    if condition.is_constant() {
                        return None;
                    }
                    let else_jump = branch
                        .else_block
                        .as_ref()
                        .is_some_and(|other| !matches!(other.stmts.as_slice(), [HirStmt::If(_)]));
                    let mut cost = condition
                        .add(Cost::fixed(1 + usize::from(else_jump)))
                        .add(block_cost(&branch.then_block, locals, depth + 1)?);
                    if let Some(other) = &branch.else_block {
                        cost = cost.add(block_cost(other, locals, depth + 1)?);
                    }
                    cost
                }
                HirStmt::NumericFor(loop_) => {
                    let (start, limit, step) = bounds(loop_)?;
                    block_cost(&loop_.body, locals, depth + 1)?
                        .add(Cost::fixed(1))
                        .multiply(trips(start, limit, step)?)
                }
                HirStmt::Block(block) => block_cost(block, locals, depth + 1)?,
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

pub(super) fn unchanged(proto: &HirProto) -> bool {
    let mandatory = mandatory_costs(proto);
    let mut loops = Vec::new();
    let mut bindings = BTreeSet::new();
    prefix::coordinates::visit(&proto.body, &mut 0, &mut |_, kind, stmt| {
        if kind == PointKind::Statement
            && let Some((local, value)) = scalar_local(stmt)
            && matches!(stmt, HirStmt::LocalDecl(_))
            && (matches!(value, HirExpr::Closure(_) | HirExpr::TableConstructor(_))
                || matches!(value, HirExpr::TableAccess(access) if matches!(access.key, HirExpr::LocalRef(_))))
        {
            // pinned ConstantFolding 不求值动态索引、函数或表分配；域外读取也不取得常量折扣。
            bindings.insert(local);
        }
        if kind == PointKind::Statement
            && let HirStmt::NumericFor(loop_) = stmt
        {
            loops.push(loop_);
        }
    });
    bindings.extend(loops.iter().map(|loop_| loop_.binding));
    loops.into_iter().all(|loop_| {
        let Some((start, limit, step)) = bounds(loop_) else {
            return false;
        };
        // pinned Compiler 在成本分析之前拒绝超过 25 次的循环。
        let Some(count) = trips(start, limit, step) else {
            return false;
        };
        if count > 25 {
            return true;
        }
        if mandatory
            .get(&loop_.binding)
            .is_some_and(|cost| cost.blocks_unroll_at_max_profit(count))
        {
            return true;
        }
        if let Some(HirStmt::NumericFor(inner)) = loop_.body.stmts.first()
            && let Some((from, to, step)) = bounds(inner)
            && let Some(inner_count) = trips(from, to, step)
            && crate::hir::luau_loop_cost::mandatory_inner_loop_blocks_unroll(count, inner_count)
        {
            return true;
        }
        let mut locals = Environment {
            bindings: &bindings,
            index: loop_.binding,
            locals: BTreeMap::new(),
        };
        block_cost(&loop_.body, &mut locals, 0)
            .is_some_and(|cost| cost.blocks_unroll(start, limit, step))
    })
}

/// 只计算分配和不会被常量求值的调用。每棵子树自底向上一次归纳，
/// 条件臂不计入下界；可能退出当前块的控制语句截断其后的计费。
fn mandatory_costs(proto: &HirProto) -> BTreeMap<LocalId, Cost> {
    let mut functions = BTreeSet::new();
    for stmt in &proto.body.stmts {
        crate::hir::visit::visit_stmt_structure(stmt, &mut |stmt| {
            if let Some((local, HirExpr::Closure(_))) = scalar_local(stmt) {
                functions.insert(local);
            }
        });
    }
    fn expr(value: &HirExpr, functions: &BTreeSet<LocalId>) -> Cost {
        match value {
            HirExpr::Closure(_) => Cost::fixed(10),
            HirExpr::TableConstructor(table) => {
                let mut cost = Cost::fixed(10);
                for field in &table.fields {
                    cost = cost.add(match field {
                        crate::hir::HirTableField::Array(value) => expr(value, functions),
                        crate::hir::HirTableField::Record(record) => {
                            expr(&record.key, functions).add(expr(&record.value, functions))
                        }
                    });
                }
                if let Some(tail) = &table.trailing_multivalue {
                    cost = cost.add(expr(tail.as_expr(), functions));
                }
                cost
            }
            HirExpr::Call(call) => {
                let base = match &call.callee {
                    HirExpr::LocalRef(local) if functions.contains(local) => 3,
                    HirExpr::GlobalRef(global) if global.key.as_utf8() == Some("print") => 4,
                    HirExpr::GlobalRef(global)
                        if matches!(global.key.as_utf8(), Some("assert" | "setmetatable")) =>
                    {
                        2
                    }
                    _ => 0,
                };
                call.args
                    .fixed
                    .iter()
                    .chain(call.args.tail.iter().map(|tail| tail.as_expr()))
                    .fold(Cost::fixed(base), |cost, value| {
                        cost.add(expr(value, functions))
                    })
            }
            HirExpr::Binary(binary) => {
                expr(&binary.lhs, functions).add(expr(&binary.rhs, functions))
            }
            HirExpr::Unary(unary) => expr(&unary.expr, functions),
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                expr(&logical.lhs, functions)
            }
            _ => Cost::fixed(0),
        }
    }
    fn block(
        body: &HirBlock,
        functions: &BTreeSet<LocalId>,
        loops: &mut BTreeMap<LocalId, Cost>,
    ) -> (Cost, bool) {
        let mut cost = Cost::fixed(0);
        let mut exits = false;
        for stmt in &body.stmts {
            let (item, stops) = match stmt {
                HirStmt::NumericFor(loop_) => {
                    let (body, _) = block(&loop_.body, functions, loops);
                    loops.insert(loop_.binding, body);
                    (
                        bounds(loop_)
                            .and_then(|(a, b, c)| trips(a, b, c))
                            .map_or(Cost::fixed(0), |count| {
                                body.add(Cost::fixed(1)).multiply(count)
                            }),
                        false,
                    )
                }
                HirStmt::If(branch) => {
                    let (_, left) = block(&branch.then_block, functions, loops);
                    let right = branch
                        .else_block
                        .as_ref()
                        .is_some_and(|other| block(other, functions, loops).1);
                    (Cost::fixed(0), left || right)
                }
                HirStmt::Block(child) => block(child, functions, loops),
                HirStmt::Break | HirStmt::Continue | HirStmt::Return(_) => (Cost::fixed(0), true),
                HirStmt::LocalDecl(decl) => (
                    decl.values
                        .fixed
                        .iter()
                        .chain(decl.values.tail.iter().map(|tail| tail.as_expr()))
                        .fold(Cost::fixed(0), |cost, value| {
                            cost.add(expr(value, functions))
                        }),
                    false,
                ),
                HirStmt::Assign(assign) => (
                    assign
                        .values
                        .fixed
                        .iter()
                        .chain(assign.values.tail.iter().map(|tail| tail.as_expr()))
                        .fold(Cost::fixed(0), |cost, value| {
                            cost.add(expr(value, functions))
                        }),
                    false,
                ),
                HirStmt::CallStmt(call) => (
                    expr(&HirExpr::Call(Box::new(call.call.clone())), functions),
                    false,
                ),
                _ => {
                    crate::hir::visit::for_each_nested_block(stmt, &mut |child| {
                        block(child, functions, loops);
                    });
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
    let mut loops = BTreeMap::new();
    block(&proto.body, &functions, &mut loops);
    loops
}
