//! 核对外围不可内联函数及其捕获调用。
//!
//! Luau 不内联 vararg 函数；固定循环或分配也可证明成本超出阈值。捕获索引来自 HIR
//! 的有序 capture，最终 AST 仍逐项核对，不能凭一个上值调用的外形认定它不透明。

use super::*;
use crate::hir::{HirBinding, HirCaptureMode, HirClosureExpr, HirModule};

pub(super) struct Functions<'a> {
    pub(super) locals: BTreeSet<crate::hir::LocalId>,
    captures: BTreeMap<crate::hir::HirProtoRef, Option<&'a HirClosureExpr>>,
}

impl<'a> Functions<'a> {
    pub(super) fn new(statements: &[&AstStmt], hir: &'a HirModule) -> Self {
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
        crate::hir::visit::visit_stmts(&hir.protos[hir.entry.index()].body.stmts, &mut captures);
        let locals = statements
            .iter()
            .filter_map(|stmt| {
                let AstStmt::LocalFunctionDecl(decl) = stmt else {
                    return None;
                };
                let AstBindingRef::Local(local) = decl.name else {
                    return None;
                };
                (decl.func.is_vararg
                    || costly_loop_function(&decl.func)
                    || costly_allocations(&decl.func))
                .then_some(local)
            })
            .collect();
        Self {
            locals,
            captures: captures.0,
        }
    }

    pub(super) fn validate(&self, func: &AstFunctionExpr) -> bool {
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

// 固定次数至少 128，单是循环迭代成本已饱和为 127；无参数常量折扣，超过 O2 内联阈值。
fn costly_loop_function(func: &AstFunctionExpr) -> bool {
    func.params.is_empty()
        && func.named_vararg.is_none()
        && matches!(func.body.stmts.as_slice(), [AstStmt::NumericFor(loop_)] if long_loop(loop_))
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
        AstStmt::NumericFor(loop_) => long_loop(loop_) && function_body(&loop_.body, calls, vararg),
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
                || plain_expr(expr, &BTreeMap::new())
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
        _ => plain_expr(expr, &BTreeMap::new()),
    }
}
