//! 核对外围不可内联函数及其捕获调用。
//!
//! Luau 不内联 vararg 函数；固定循环或分配也可证明成本超出阈值。捕获索引来自 HIR
//! 的有序 capture，最终 AST 仍逐项核对，不能凭一个上值调用的外形认定它不透明。

use super::*;
use crate::hir::{HirBinding, HirCaptureMode, HirClosureExpr, HirModule};

pub(super) struct Functions<'a> {
    pub(super) locals: BTreeSet<crate::hir::LocalId>,
    /// 只在完整动态实参下足够昂贵的函数，以及排除缺参 nil 专化所需的参数数目。
    pub(super) runtime: BTreeMap<crate::hir::LocalId, usize>,
    captures: BTreeMap<crate::hir::HirProtoRef, Option<&'a HirClosureExpr>>,
}

impl<'a> Functions<'a> {
    pub(super) fn new(
        statements: &[&AstStmt],
        hir: &'a HirModule,
        owner: crate::hir::HirProtoRef,
        validated: &BTreeSet<crate::hir::HirProtoRef>,
    ) -> Self {
        struct Captures<'a>(BTreeMap<crate::hir::HirProtoRef, Option<&'a HirClosureExpr>>);
        impl<'a> crate::hir::visit::HirVisitor<'a> for Captures<'a> {
            fn visit_closure(&mut self, closure: &'a HirClosureExpr) {
                self.0
                    .entry(closure.proto)
                    .and_modify(|known| {
                        if known.is_some_and(|previous| previous.captures != closure.captures) {
                            *known = None;
                        }
                    })
                    .or_insert(Some(closure));
            }
        }
        let mut captures = Captures(BTreeMap::new());
        // LocalId 仅在 caller 内有意义；同模板若有不同 capture，不能任选最后一次创建。
        crate::hir::visit::visit_stmts(&hir.protos[owner.index()].body.stmts, &mut captures);
        let locals: BTreeSet<_> = statements
            .iter()
            .filter_map(|stmt| {
                let AstStmt::LocalFunctionDecl(decl) = stmt else {
                    return None;
                };
                let AstBindingRef::Local(local) = decl.name else {
                    return None;
                };
                (validated.contains(&decl.func.function)
                    || decl.func.is_vararg
                    || costly_loop_function(&decl.func)
                    || costly_callback_return(&decl.func)
                    || costly_allocations(&decl.func))
                .then_some(local)
            })
            .collect();
        let runtime = statements
            .iter()
            .filter_map(|stmt| {
                let AstStmt::LocalFunctionDecl(decl) = stmt else {
                    return None;
                };
                let AstBindingRef::Local(local) = decl.name else {
                    return None;
                };
                if locals.contains(&local) {
                    return None;
                }
                let (cost, _) =
                    constant_control::CostAnalysis::new(&decl.func).runtime_summary()?;
                (!cost.permits_inline(cost)
                    && !decl.func.is_vararg
                    && decl.func.named_vararg.is_none())
                .then_some((local, decl.func.params.len()))
            })
            .collect();
        Self {
            runtime,
            locals,
            captures: captures.0,
        }
    }

    pub(super) fn capture_layout(
        &self,
        function: crate::hir::HirProtoRef,
    ) -> Option<&HirClosureExpr> {
        self.captures.get(&function).copied().flatten()
    }

    pub(super) fn validate(&self, func: &AstFunctionExpr) -> bool {
        if costly_callback_return(func) {
            return true;
        }
        let mut calls = BTreeSet::new();
        if let Some(Some(closure)) = self.captures.get(&func.function) {
            for (index, capture) in closure.captures.iter().enumerate() {
                if let HirBinding::Local(local) = capture.binding
                    && self.locals.contains(&local)
                    && capture.mode == HirCaptureMode::ByValue
                    && func
                        .captured_bindings
                        .contains(&AstBindingRef::Local(local))
                {
                    calls.insert(AstNameRef::Upvalue(crate::hir::UpvalueId(index)));
                }
            }
        }
        function_body(&func.body, &calls, func.is_vararg)
    }

    pub(super) fn opaque_capture(
        &self,
        func: &AstFunctionExpr,
        upvalue: crate::hir::UpvalueId,
    ) -> bool {
        self.captures.get(&func.function).copied().flatten()
            .and_then(|closure| closure.captures.get(upvalue.index()))
            .is_some_and(|capture| capture.mode == HirCaptureMode::ByValue
                && matches!(capture.binding, HirBinding::Local(local) if self.locals.contains(&local)
                    && func.captured_bindings.contains(&AstBindingRef::Local(local))))
    }
}

// 参数只作 CALL callee，所有实参为字面量：调用结果不参与常量折叠，参数专化也没有成本折扣。
// 每次普通 CALL 收费 3，每个字面量参数 COPY 收费 1，逻辑节点和 NOT 各收费 1。
fn costly_callback_return(func: &AstFunctionExpr) -> bool {
    if func.is_vararg || func.named_vararg.is_some() {
        return false;
    }
    let [AstStmt::Return(ret)] = func.body.stmts.as_slice() else {
        return false;
    };
    let [value] = ret.values.as_slice() else {
        return false;
    };
    let parameters = func.params.iter().copied().collect::<BTreeSet<_>>();
    let mut pending = vec![value];
    let mut cost = 0usize;
    while let Some(value) = pending.pop() {
        let current = match value {
            AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
                pending.extend([&logical.lhs, &logical.rhs]);
                1
            }
            AstExpr::Unary(unary) if unary.op == AstUnaryOpKind::Not => {
                pending.push(&unary.expr);
                1
            }
            AstExpr::SingleValue(value) => {
                pending.push(value);
                0
            }
            AstExpr::Call(call)
                if call.required_luau_inlining.is_none()
                    && call.method_key.is_none()
                    && matches!(call.callee, AstExpr::Var(AstNameRef::Param(parameter)) if parameters.contains(&parameter))
                    && call.args.iter().all(|arg| {
                        matches!(
                            arg,
                            AstExpr::Nil
                                | AstExpr::Boolean(_)
                                | AstExpr::Integer(_)
                                | AstExpr::Number(_)
                                | AstExpr::String(_)
                        )
                    }) =>
            {
                3 + call.args.len()
            }
            _ => return false,
        };
        cost = cost.saturating_add(current).min(127);
    }
    let profit = (100 * (cost + 3)).checked_div(cost).unwrap_or(300).min(300);
    cost > 25 * profit / 100
}

// 无参数函数没有实参常量折扣；三次表/闭包分配的成本下界为 30，
// 高于 pinned O2 的收益调整阈值 25 * (cost + 3) / cost。
fn costly_allocations(func: &AstFunctionExpr) -> bool {
    if !func.params.is_empty() || func.named_vararg.is_some() {
        return false;
    }
    let mut pending = Vec::new();
    for stmt in &func.body.stmts {
        match stmt {
            AstStmt::LocalDecl(decl) => pending.extend(decl.values.iter()),
            AstStmt::Assign(assign) => pending.extend(assign.values.iter()),
            AstStmt::Return(ret) => {
                pending.extend(ret.values.iter());
                break;
            }
            _ => break,
        }
    }
    let mut allocations = 0;
    while let Some(expr) = pending.pop() {
        match expr {
            AstExpr::FunctionExpr(_) => allocations += 1,
            AstExpr::TableConstructor(table) => {
                allocations += 1;
                for field in &table.fields {
                    match field {
                        AstTableField::Array(value) => pending.push(value),
                        AstTableField::Record(record) => {
                            if let AstTableKey::Expr(key) = &record.key {
                                pending.push(key);
                            }
                            pending.push(&record.value);
                        }
                    }
                }
            }
            AstExpr::Call(call) => {
                pending.push(&call.callee);
                pending.extend(&call.args);
            }
            AstExpr::SingleValue(value) => pending.push(value),
            _ => {}
        }
        if allocations >= 3 {
            return true;
        }
    }
    false
}

// 大循环或每条参数专化路径均超过最大成本阈值的嵌套循环，仍保留原 CALL。
fn costly_loop_function(func: &AstFunctionExpr) -> bool {
    (func.params.is_empty()
        && func.named_vararg.is_none()
        && matches!(func.body.stmts.as_slice(), [AstStmt::NumericFor(loop_)] if long_loop(loop_)))
        || loop_cost_floor(&func.body, 0, false).is_some_and(|cost| cost > 75)
}

/// 对参数常量专化取各路径成本下界。后缀从右向左传递，break/continue 不计其后
/// 语句；每个节点只访问一次。75 是 pinned O2 基础阈值 25 的最大三倍 boost。
fn loop_cost_floor(block: &AstBlock, mut suffix: usize, nested: bool) -> Option<usize> {
    for stmt in block.stmts.iter().rev() {
        suffix = match stmt {
            AstStmt::Return(_) if !nested => 0,
            AstStmt::Break | AstStmt::Continue => 1,
            AstStmt::CallStmt(stmt) => {
                let AstCallKind::Call(call) = &stmt.call else { return None; };
                if !matches!(&call.callee, AstExpr::Var(AstNameRef::Global(name)) if name.text == "print")
                    || call.method_key.is_some() || call.required_luau_inlining.is_some() { return None; }
                // 普通全局 CALL + GETIMPORT 为 4，每个实参至少需要一次求值或 COPY。
                suffix.saturating_add(4 + call.args.len())
            }
            AstStmt::If(branch) if matches!(branch.cond, AstExpr::Var(AstNameRef::Param(_))) => {
                let then_cost = loop_cost_floor(&branch.then_block, suffix, true)?;
                let else_cost = branch.else_block.as_ref().map_or(Some(suffix), |block| loop_cost_floor(block, suffix, true))?;
                then_cost.min(else_cost)
            }
            AstStmt::Repeat(loop_) if matches!(loop_.cond, AstExpr::Var(AstNameRef::Param(_))) => {
                suffix.saturating_add(loop_cost_floor(&loop_.body, 0, true)?.saturating_mul(3))
            }
            AstStmt::GenericFor(loop_) if matches!(loop_.iterator.as_slice(), [AstExpr::Var(AstNameRef::Param(_))]) => {
                suffix.saturating_add((loop_cost_floor(&loop_.body, 0, true)? + 1).saturating_mul(3))
            }
            AstStmt::NumericFor(loop_) => {
                let (AstExpr::Integer(start), AstExpr::Integer(limit), AstExpr::Integer(step)) = (&loop_.start, &loop_.limit, &loop_.step) else { return None; };
                if *step == 0 || [start, limit, step].iter().any(|value| i32::try_from(**value).is_err()) { return None; }
                let distance = if *step > 0 { i128::from(*limit) - i128::from(*start) } else { i128::from(*start) - i128::from(*limit) };
                let trips = if distance < 0 { 0 } else { (distance / i128::from(*step).abs() + 1).min(127) as usize };
                suffix.saturating_add((loop_cost_floor(&loop_.body, 0, true)? + 1).saturating_mul(trips))
            }
            _ => return None,
        }.min(127);
    }
    Some(suffix)
}

fn long_loop(loop_: &AstNumericFor) -> bool {
    let (AstExpr::Integer(start), AstExpr::Integer(limit), AstExpr::Integer(step)) =
        (&loop_.start, &loop_.limit, &loop_.step)
    else {
        return false;
    };
    if *step == 0
        || [start, limit, step]
            .iter()
            .any(|v| i32::try_from(**v).is_err())
    {
        return false;
    }
    let distance = if *step > 0 {
        i128::from(*limit) - i128::from(*start)
    } else {
        i128::from(*start) - i128::from(*limit)
    };
    distance >= 0 && distance / i128::from(*step).abs() + 1 >= 128
}

fn function_body(block: &AstBlock, calls: &BTreeSet<AstNameRef>, vararg: bool) -> bool {
    block.stmts.iter().all(|stmt| match stmt {
        AstStmt::LocalDecl(decl) => decl.values.iter().all(|v| expression(v, calls, vararg)),
        AstStmt::Assign(assign) => {
            assign.targets.iter().all(|target| match target {
                AstLValue::Name(_) => true,
                AstLValue::FieldAccess(field) => expression(&field.base, calls, vararg),
                AstLValue::IndexAccess(index) => {
                    expression(&index.base, calls, vararg)
                        && expression(&index.index, calls, vararg)
                }
            }) && assign.values.iter().all(|v| expression(v, calls, vararg))
        }
        AstStmt::Return(ret) => ret.values.iter().all(|v| expression(v, calls, vararg)),
        AstStmt::CallStmt(stmt) => matches!(&stmt.call, AstCallKind::Call(call)
            if ordinary_call(call, calls, vararg)),
        AstStmt::LocalFunctionDecl(decl) => {
            function_body(&decl.func.body, &BTreeSet::new(), decl.func.is_vararg)
        }
        AstStmt::NumericFor(loop_) => {
            (long_loop(loop_) || loops::unchanged(loop_, &BTreeMap::new()))
                && function_body(&loop_.body, calls, vararg)
        }
        AstStmt::Repeat(loop_) => {
            matches!(loop_.cond, AstExpr::Var(AstNameRef::Param(_)))
                && function_body(&loop_.body, calls, vararg)
        }
        AstStmt::GenericFor(loop_) => {
            matches!(
                loop_.iterator.as_slice(),
                [AstExpr::Var(AstNameRef::Param(_))]
            ) && function_body(&loop_.body, calls, vararg)
        }
        AstStmt::If(branch) => {
            matches!(branch.cond, AstExpr::Var(AstNameRef::Param(_)))
                && function_body(&branch.then_block, calls, vararg)
                && branch
                    .else_block
                    .as_ref()
                    .is_none_or(|block| function_body(block, calls, vararg))
        }
        AstStmt::Break | AstStmt::Continue => true,
        _ => false,
    })
}

fn ordinary_call(call: &AstCallExpr, calls: &BTreeSet<AstNameRef>, vararg: bool) -> bool {
    call.required_luau_inlining.is_none()
        && call.method_key.is_none()
        && matches!(&call.callee, AstExpr::Var(name) if calls.contains(name)
            || matches!(name, AstNameRef::Global(global) if matches!(global.text.as_str(), "assert" | "print")))
        && call.args.iter().all(|arg| expression(arg, calls, vararg))
}

fn expression(expr: &AstExpr, calls: &BTreeSet<AstNameRef>, vararg: bool) -> bool {
    match expr {
        AstExpr::VarArg => vararg,
        AstExpr::CaptureInitializer(crate::hir::HirCaptureInitializer::FirstVararg(_)) => vararg,
        AstExpr::Call(call) => {
            ordinary_call(call, calls, vararg)
                || PlainExpressions::new(&BTreeMap::new()).expr(expr)
                || matches!(&call.callee, AstExpr::Var(AstNameRef::Global(name)) if name.text == "setmetatable")
                    && call.required_luau_inlining.is_none()
                    && call.method_key.is_none()
                    && call.args.iter().all(|arg| expression(arg, calls, vararg))
        }
        AstExpr::FunctionExpr(func) => function_body(&func.body, &BTreeSet::new(), func.is_vararg),
        AstExpr::TableConstructor(table) => table.fields.iter().all(|field| match field {
            AstTableField::Array(value) => expression(value, calls, vararg),
            AstTableField::Record(record) => {
                (match &record.key {
                    AstTableKey::Name(_) => true,
                    AstTableKey::Expr(key) => expression(key, calls, vararg),
                }) && expression(&record.value, calls, vararg)
            }
        }),
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            expression(&logical.lhs, calls, vararg) && expression(&logical.rhs, calls, vararg)
        }
        AstExpr::SingleValue(value) => expression(value, calls, vararg),
        _ => PlainExpressions::new(&BTreeMap::new()).expr(expr),
    }
}
