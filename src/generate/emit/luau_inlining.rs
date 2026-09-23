//! 在最终源码树上核对必须消失的 Luau 调用。
//!
//! 消费 HIR 对原展开帧及参数替换的证明，核对固定函数体、固定返回宽度和
//! caller 声明前缀。外围语法须不引起额外的 O2 改写；全部 occurrence 通过后才可
//! 发射所需 optimize pragma，该编译要求不能随展示注释一起关闭。

use crate::ast::*;
use crate::hir::HirLuauInliningBody;
use std::collections::{BTreeMap, BTreeSet};

mod conditional_methods;
mod loops;
mod opaque;
mod returned_calls;

// 只展开词法包装，不穿过控制流或函数边界；binding 身份仍属于同一个 caller。
fn scope_statements(block: &AstBlock) -> Vec<&AstStmt> {
    let mut pending = block.stmts.iter().rev().collect::<Vec<_>>();
    let mut statements = Vec::new();
    while let Some(stmt) = pending.pop() {
        if let AstStmt::DoBlock(block) = stmt {
            pending.extend(block.stmts.iter().rev());
        } else {
            statements.push(stmt);
        }
    }
    statements
}

pub(super) fn validate(module: &AstModule, hir: &crate::hir::HirModule) -> bool {
    let requirements = &hir.required_luau_inlining;
    let statements = scope_statements(&module.body);
    let opaque_functions = opaque::Functions::new(&statements, hir);
    let mut callees = BTreeMap::new();
    let mut occurrences = BTreeMap::new();
    let mut result_slots = BTreeMap::new();
    let published_globals = requirements
        .iter()
        .filter(|requirement| {
            matches!(
                requirement.body,
                HirLuauInliningBody::PublishedClosureFactory { .. }
            )
        })
        .filter_map(|requirement| requirement.field.as_utf8())
        .collect::<BTreeSet<_>>();
    let shared_factories = statements
        .iter()
        .filter_map(|stmt| {
            let AstStmt::LocalFunctionDecl(decl) = stmt else {
                return None;
            };
            let AstBindingRef::Local(local) = decl.name else {
                return None;
            };
            shared_closure_factory(&decl.func).then(|| {
                callees.insert(local, decl.func.function);
                local
            })
        })
        .collect::<BTreeSet<_>>();
    let bodies = requirements
        .iter()
        .map(|r| (r.callee, r.body))
        .collect::<BTreeMap<_, _>>();
    // Luau 对显式重写的 local 不进行函数解析；这些外围调用保持原 CALL。
    let mut opaque_locals = statements
        .iter()
        .filter_map(|stmt| {
            let AstStmt::Assign(assign) = stmt else {
                return None;
            };
            Some(assign.targets.iter().filter_map(|target| match target {
                AstLValue::Name(AstNameRef::Local(local)) => Some(*local),
                _ => None,
            }))
        })
        .flatten()
        .collect::<BTreeSet<_>>();
    opaque_locals.extend(opaque_functions.locals.iter().copied());
    if bodies
        .values()
        .any(|body| matches!(body, HirLuauInliningBody::ConditionalMethod { .. }))
    {
        // 编译器只会为只读实参复用原槽；后续写入和子闭包写入同样会触发参数 COPY。
        opaque_locals.extend(crate::ast::written_locals(&module.body));
    }
    for stmt in &statements {
        if let AstStmt::If(branch) = stmt {
            for arm in std::iter::once(&branch.then_block).chain(branch.else_block.iter()) {
                for stmt in &arm.stmts {
                    if let AstStmt::Assign(assign) = stmt {
                        opaque_locals.extend(assign.targets.iter().filter_map(
                            |target| match target {
                                AstLValue::Name(AstNameRef::Local(local)) => Some(*local),
                                _ => None,
                            },
                        ));
                    }
                }
            }
        }
    }
    for stmt in &statements {
        if let AstStmt::LocalDecl(decl) = stmt
            && let ([binding], [AstExpr::Var(AstNameRef::Global(name))]) =
                (decl.bindings.as_slice(), decl.values.as_slice())
            && name.text == "print"
            && let AstBindingRef::Local(local) = binding.id
        {
            opaque_locals.insert(local);
        }
    }
    // getFunctionExpr 不穿过函数调用结果；恢复工厂后，返回闭包的调用仍保留原 CALL。
    // 只认回已签证工厂的独立单结果声明，不能把工厂自身也当成不透明 callee。
    for stmt in &statements {
        if let AstStmt::LocalDecl(decl) = stmt
            && let ([binding], [AstExpr::Call(call)]) =
                (decl.bindings.as_slice(), decl.values.as_slice())
            && let AstBindingRef::Local(result) = binding.id
            && let AstExpr::Var(AstNameRef::Local(factory)) = call.callee
            && (opaque_locals.contains(&factory)
                || (shared_factories.contains(&factory) && call.args.is_empty())
                || (call.required_luau_inlining.is_some()
                    && matches!(
                        bodies.get(&factory),
                        Some(
                            HirLuauInliningBody::ValueClosureFactory { .. }
                                | HirLuauInliningBody::SnapshotClosureFactory { .. }
                                | HirLuauInliningBody::NestedValueClosureFactory { .. }
                                | HirLuauInliningBody::EventClosureFactory { .. }
                                | HirLuauInliningBody::PublishedClosureFactory { .. }
                        )
                    )))
        {
            opaque_locals.insert(result);
        }
    }
    // getFunctionExpr 沿 local alias 追到调用结果仍会停止；按声明顺序传播一次。
    for stmt in &statements {
        if let AstStmt::LocalDecl(decl) = stmt
            && let ([binding], [AstExpr::Var(AstNameRef::Local(source))]) =
                (decl.bindings.as_slice(), decl.values.as_slice())
            && opaque_locals.contains(source)
            && let AstBindingRef::Local(local) = binding.id
        {
            opaque_locals.insert(local);
        }
    }
    let scalar_callees = requirements
        .iter()
        .filter(|requirement| matches!(requirement.body, HirLuauInliningBody::ScalarNotCall { .. }))
        .map(|requirement| requirement.callee)
        .collect::<BTreeSet<_>>();
    let scalar_names = requirements
        .iter()
        .filter(|requirement| matches!(requirement.body, HirLuauInliningBody::ScalarNotCall { .. }))
        .filter_map(|requirement| requirement.field.as_utf8())
        .collect::<BTreeSet<_>>();
    let captured_callees = requirements
        .iter()
        .filter(|requirement| requirement.body == HirLuauInliningBody::CapturedConcatSum)
        .map(|requirement| requirement.callee)
        .collect::<BTreeSet<_>>();
    let fields = requirements
        .iter()
        .map(|requirement| {
            (
                requirement.callee,
                (requirement.body, &requirement.field, requirement.capture),
            )
        })
        .collect::<BTreeMap<_, _>>();
    for requirement in requirements {
        if matches!(
            requirement.body,
            HirLuauInliningBody::EventClosureFactory { .. }
                | HirLuauInliningBody::PublishedClosureFactory { .. }
                | HirLuauInliningBody::SnapshotClosureFactory { .. }
                | HirLuauInliningBody::CapturedCallablePair
                | HirLuauInliningBody::ConditionalMethod { .. }
        ) && (requirement.result_frame_slots.len() != requirement.occurrences.len()
            || requirement
                .occurrences
                .iter()
                .any(|site| !requirement.result_frame_slots.contains_key(site)))
        {
            return false;
        }
        result_slots.extend(
            requirement
                .result_frame_slots
                .iter()
                .map(|(&site, &slot)| (site, slot)),
        );
        if requirement.owner != module.entry_function
            || callees
                .insert(requirement.callee, requirement.child)
                .is_some()
        {
            return false;
        }
        for site in &requirement.occurrences {
            if site.proto != requirement.owner
                || occurrences.insert(*site, requirement.callee).is_some()
            {
                return false;
            }
        }
    }
    let mut declared = BTreeSet::new();
    let mut seen_occurrences = BTreeSet::new();
    let mut seen_result_slots = BTreeSet::new();
    let mut active = 0usize;
    let mut pending = module
        .body
        .stmts
        .iter()
        .rev()
        .map(|stmt| (Some(stmt), 0))
        .collect::<Vec<_>>();
    while let Some((stmt, restore)) = pending.pop() {
        let Some(stmt) = stmt else {
            active = restore;
            continue;
        };
        match stmt {
            AstStmt::LocalFunctionDecl(decl) => {
                let AstBindingRef::Local(local) = decl.name else {
                    return false;
                };
                let valid = if shared_factories.contains(&local) {
                    declared.insert(local) && shared_closure_factory(&decl.func)
                        && !decl.func.captured_bindings.iter().any(|binding| matches!(binding, AstBindingRef::Local(captured) if callees.contains_key(captured)))
                } else if let Some(child) = callees.get(&local) {
                    *child == decl.func.function
                        && declared.insert(local)
                        && if fields[&local].0 == HirLuauInliningBody::CapturedCallablePair {
                            returned_calls::body(&decl.func, fields[&local].1, &opaque_functions)
                        } else {
                            callee_body(
                                &decl.func,
                                fields[&local].0,
                                fields[&local].1,
                                fields[&local].2,
                            )
                        }
                } else {
                    if opaque_functions.locals.contains(&local) {
                        opaque_functions.validate(&decl.func)
                    } else {
                        plain_function(&decl.func, &callees)
                    }
                };
                if !valid {
                    return false;
                }
                active += 1;
            }
            AstStmt::LocalDecl(decl) => {
                // 整组 local 的 target 已预留；只允许一对一的 fixed-one 调用。
                if let [AstExpr::Call(call)] = decl.values.as_slice()
                    && let Some(site) = call.required_luau_inlining
                    && let Some(&slot) = result_slots.get(&site)
                {
                    // 宏必须作为原单结果声明发射；不允许移入参数树后复用一个估算的 top。
                    let width = if occurrences.get(&site).and_then(|local| bodies.get(local))
                        == Some(&HirLuauInliningBody::CapturedCallablePair)
                    {
                        2
                    } else {
                        1
                    };
                    if decl.bindings.len() != width
                        || active != slot
                        || !seen_result_slots.insert(site)
                    {
                        return false;
                    }
                }
                active += decl.bindings.len();
                let mut expression = InvocationExpressions {
                    shared_factories: &shared_factories,
                    published_globals: &published_globals,
                    bodies: &bodies,
                    opaque_locals: &opaque_locals,
                    scalar_callees: &scalar_callees,
                    captured_callees: &captured_callees,
                    callees: &callees,
                    occurrences: &occurrences,
                    declared: &declared,
                    seen: &mut seen_occurrences,
                };
                if decl.bindings.len() == 2
                    && decl.values.len() == 1
                    && expression.pair(&decl.values[0], active)
                {
                    continue;
                }
                if decl.values.iter().any(|value| {
                    !expression.check(
                        value,
                        active,
                        decl.bindings.len() == 1 && decl.values.len() == 1,
                    )
                }) {
                    return false;
                }
            }
            AstStmt::CallStmt(stmt) => {
                let AstCallKind::Call(call) = &stmt.call else {
                    return false;
                };
                if call.required_luau_inlining.is_some()
                    || !(matches!(&call.callee, AstExpr::Var(AstNameRef::Global(name))
                    if name.text == "assert" || name.text == "print")
                        || matches!(&call.callee, AstExpr::Var(AstNameRef::Local(local)) if opaque_locals.contains(local)))
                    || !call.args.iter().enumerate().all(|(index, arg)| {
                        InvocationExpressions {
                            shared_factories: &shared_factories,
                            published_globals: &published_globals,
                            bodies: &bodies,
                            opaque_locals: &opaque_locals,
                            scalar_callees: &scalar_callees,
                            captured_callees: &captured_callees,
                            callees: &callees,
                            occurrences: &occurrences,
                            declared: &declared,
                            seen: &mut seen_occurrences,
                        }
                        .check(
                            arg,
                            active + 1 + call.args.len(),
                            index + 1 < call.args.len(),
                        )
                    })
                {
                    return false;
                }
            }
            AstStmt::If(branch) => {
                let Some(other) = &branch.else_block else {
                    return false;
                };
                let ([AstStmt::Assign(truthy)], [AstStmt::Assign(falsy)]) =
                    (branch.then_block.stmts.as_slice(), other.stmts.as_slice())
                else {
                    return false;
                };
                let test = match &branch.cond {
                    AstExpr::Unary(unary) if unary.op == AstUnaryOpKind::Not => &unary.expr,
                    test => test,
                };
                if !branch.preserves_empty_test
                    || !matches!(test, AstExpr::Call(call)
                        if call.required_luau_inlining.is_some()
                            && matches!(&call.callee, AstExpr::Var(AstNameRef::Local(local))
                                if bodies.get(local) == Some(&HirLuauInliningBody::Identity))
                            && matches!(call.args.as_slice(), [AstExpr::Boolean(_)]))
                    || truthy.targets != falsy.targets
                    || !matches!(truthy.targets.as_slice(), [AstLValue::Name(AstNameRef::Local(local))] if !callees.contains_key(local))
                    || truthy.values.len() != 1
                    || falsy.values.len() != 1
                {
                    return false;
                }
                // 同一目标的两条值路径仍由原 TEST 分隔；恒等宏阻止 O2 在内联前删掉检查。
                let mut expressions = InvocationExpressions {
                    shared_factories: &shared_factories,
                    published_globals: &published_globals,
                    bodies: &bodies,
                    opaque_locals: &opaque_locals,
                    scalar_callees: &scalar_callees,
                    captured_callees: &captured_callees,
                    callees: &callees,
                    occurrences: &occurrences,
                    declared: &declared,
                    seen: &mut seen_occurrences,
                };
                if !expressions.check(&branch.cond, active + 1, true)
                    || !expressions.check(&truthy.values[0], active + 1, true)
                    || !expressions.check(&falsy.values[0], active + 1, true)
                {
                    return false;
                }
            }
            AstStmt::DoBlock(block) => {
                // 每个内部声明/调用仍逐项检查；出块后恢复外层 top，不能把已结束的
                // 前一组结果声明计入下一个 required 调用的寄存器压力。
                pending.push((None, active));
                pending.extend(block.stmts.iter().rev().map(|stmt| (Some(stmt), 0)));
            }
            AstStmt::NumericFor(loop_) if loops::unchanged(loop_, &callees) => {}
            // pinned Luau 只展开数值循环；迭代器和循环体仍逐项排除额外内联及常量折叠。
            AstStmt::GenericFor(loop_)
                if matches!(loop_.iterator.as_slice(), [AstExpr::Call(call)]
                    if matches!(&call.callee, AstExpr::Var(AstNameRef::Global(name)) if name.text == "ipairs")
                        && call.required_luau_inlining.is_none() && call.method_key.is_none()
                        && matches!(call.args.as_slice(), [AstExpr::Var(AstNameRef::Local(local))] if !callees.contains_key(local)))
                    && plain_block(&loop_.body, &callees) => {}
            AstStmt::FunctionDecl(decl) if plain_field_function(decl, &callees) => {}
            AstStmt::Return(ret) if ret.values.is_empty() => {}
            AstStmt::Assign(assign)
                if assign.targets.len() == 2
                    && assign.values.len() == 1
                    && assign
                        .targets
                        .iter()
                        .all(|target| matches!(target, AstLValue::Name(AstNameRef::Local(local)) if !callees.contains_key(local)))
                    && matches!(&assign.values[0], AstExpr::Call(call) if call.required_luau_inlining.is_some()) =>
            {
                let AstExpr::Call(call) = &assign.values[0] else {
                    return false;
                };
                let site = call.required_luau_inlining.unwrap();
                if result_slots.get(&site) != Some(&active)
                    || !seen_result_slots.insert(site)
                    || !(InvocationExpressions {
                        shared_factories: &shared_factories,
                        published_globals: &published_globals,
                        bodies: &bodies,
                        opaque_locals: &opaque_locals,
                        scalar_callees: &scalar_callees,
                        captured_callees: &captured_callees,
                        callees: &callees,
                        occurrences: &occurrences,
                        declared: &declared,
                        seen: &mut seen_occurrences,
                    })
                    .pair(&assign.values[0], active + 2)
                {
                    return false;
                }
            }
            AstStmt::Assign(assign) if plain_assign(assign, &callees) => {}
            AstStmt::Assign(assign) if matches!(assign.targets.as_slice(), [AstLValue::Name(AstNameRef::Local(local))] if opaque_locals.contains(local)) => {
                if assign.values.len() != 1
                    || !(InvocationExpressions {
                        shared_factories: &shared_factories,
                        published_globals: &published_globals,
                        bodies: &bodies,
                        opaque_locals: &opaque_locals,
                        scalar_callees: &scalar_callees,
                        captured_callees: &captured_callees,
                        callees: &callees,
                        occurrences: &occurrences,
                        declared: &declared,
                        seen: &mut seen_occurrences,
                    })
                    .check(&assign.values[0], active + 1, true)
                {
                    return false;
                }
            }
            AstStmt::Assign(assign)
                if matches!((assign.targets.as_slice(), assign.values.as_slice()),
                ([AstLValue::Name(AstNameRef::Global(target))], [AstExpr::Var(AstNameRef::Global(value))])
                if matches!(value.text.as_str(), "type" | "tostring")
                    && scalar_names.contains(target.text.as_str())) => {}
            _ => return false,
        }
    }
    seen_occurrences.len() == occurrences.len()
        && declared.len() == callees.len()
        && seen_result_slots.len() == result_slots.len()
}

struct InvocationExpressions<'a> {
    published_globals: &'a BTreeSet<&'a str>,
    shared_factories: &'a BTreeSet<crate::hir::LocalId>,
    bodies: &'a BTreeMap<crate::hir::LocalId, HirLuauInliningBody>,
    opaque_locals: &'a BTreeSet<crate::hir::LocalId>,
    scalar_callees: &'a BTreeSet<crate::hir::LocalId>,
    captured_callees: &'a BTreeSet<crate::hir::LocalId>,
    callees: &'a BTreeMap<crate::hir::LocalId, crate::hir::HirProtoRef>,
    occurrences: &'a BTreeMap<crate::hir::HirSourceSite, crate::hir::LocalId>,
    declared: &'a BTreeSet<crate::hir::LocalId>,
    seen: &'a mut BTreeSet<crate::hir::HirSourceSite>,
}

impl InvocationExpressions<'_> {
    // 固定两项返回仍走 Luau targetCount 内联协议；开放返回不会获得此许可。
    fn pair(&mut self, expr: &AstExpr, top: usize) -> bool {
        let AstExpr::Call(call) = expr else {
            return false;
        };
        let Some(site) = call.required_luau_inlining else {
            return false;
        };
        let Some(callee) = self.occurrences.get(&site) else {
            return false;
        };
        self.bodies.get(callee) == Some(&HirLuauInliningBody::CapturedCallablePair)
            && top <= 128
            && self.declared.contains(callee)
            && call.callee == AstExpr::Var(AstNameRef::Local(*callee))
            && call.method_key.is_none()
            && call.args.is_empty()
            && self.seen.insert(site)
    }

    /// 比较与逻辑操作数均为 fixed-one；保守计入表达式的预留结果及 operand 槽，
    /// 仍沿用寄存器上限。末尾实参的裸调用可能是 open，不能仅因函数返回一个值放行。
    fn check(&mut self, expr: &AstExpr, top: usize, fixed_one: bool) -> bool {
        match expr {
            AstExpr::Call(call) if call.required_luau_inlining.is_some() => {
                let site = call.required_luau_inlining.unwrap();
                let Some(callee) = self.occurrences.get(&site) else {
                    return false;
                };
                fixed_one
                    && top <= 128
                    && self.declared.contains(callee)
                    && call.callee == AstExpr::Var(AstNameRef::Local(*callee))
                    && call.method_key.is_none()
                    && call.args.len()
                        == if self.captured_callees.contains(callee) {
                            3
                        } else if matches!(
                            self.bodies[callee],
                            HirLuauInliningBody::TableFactory { .. }
                                | HirLuauInliningBody::PublishedTableFactory { .. }
                                | HirLuauInliningBody::ClosureFactory { .. }
                                | HirLuauInliningBody::PublishedClosureFactory { .. }
                        ) {
                            0
                        } else {
                            1
                        }
                    && (!self.scalar_callees.contains(callee)
                        || matches!(call.args[0], AstExpr::Boolean(_)))
                    && (!matches!(
                        self.bodies[callee],
                        HirLuauInliningBody::ValueClosureFactory { .. }
                            | HirLuauInliningBody::SnapshotClosureFactory { .. }
                            | HirLuauInliningBody::NestedValueClosureFactory { .. }
                    ) || matches!(call.args.as_slice(), [AstExpr::Integer(value)] if (-32768..=32767).contains(value)))
                    && (!matches!(
                        self.bodies[callee],
                        HirLuauInliningBody::EventClosureFactory { .. }
                    ) || matches!(call.args.as_slice(), [AstExpr::String(_)]))
                    && (!matches!(
                        self.bodies[callee],
                        HirLuauInliningBody::ConditionalMethod { .. }
                    ) || matches!(call.args.as_slice(), [AstExpr::Var(AstNameRef::Local(local))] if !self.opaque_locals.contains(local)))
                    && (self.bodies[callee] != HirLuauInliningBody::Identity
                        || matches!(call.args.as_slice(), [AstExpr::Number(value)] if value.is_nan())
                        || matches!(call.args.as_slice(), [AstExpr::Integer(value)] if (-32768..=32767).contains(value))
                        || matches!(call.args.as_slice(), [AstExpr::Boolean(_)]))
                    && call.args.iter().all(|arg| plain_expr(arg, self.callees))
                    && self.seen.insert(site)
            }
            AstExpr::Var(AstNameRef::Global(name))
                if self.published_globals.contains(name.text.as_str()) =>
            {
                true
            }
            AstExpr::Call(call) if matches!(&call.callee, AstExpr::Var(AstNameRef::Global(name)) if self.published_globals.contains(name.text.as_str())) => {
                call.required_luau_inlining.is_none()
                    && call.method_key.is_none()
                    && call.args.is_empty()
            }
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
                // 原显式比较不能被启用 O2 的常量折叠吞掉；identity 调用在折叠后展开。
                let literal = |value: &AstExpr| {
                    matches!(
                        value,
                        AstExpr::Nil
                            | AstExpr::Boolean(_)
                            | AstExpr::Integer(_)
                            | AstExpr::Number(_)
                            | AstExpr::String(_)
                    )
                };
                !(literal(&binary.lhs) && literal(&binary.rhs))
                    && self.check(&binary.lhs, top + 3, true)
                    && self.check(&binary.rhs, top + 3, true)
            }
            AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
                self.check(&logical.lhs, top + 1, true) && self.check(&logical.rhs, top + 1, true)
            }
            AstExpr::Unary(unary)
                if matches!(unary.op, AstUnaryOpKind::Length | AstUnaryOpKind::Not) =>
            {
                self.check(&unary.expr, top + 1, true)
            }
            AstExpr::SingleValue(value) => self.check(value, top, true),
            AstExpr::Call(call) if matches!(call.callee, AstExpr::Var(AstNameRef::Local(local)) if self.shared_factories.contains(&local) && self.declared.contains(&local)) => {
                fixed_one && top <= 128 && call.method_key.is_none() && call.args.is_empty()
            }
            AstExpr::Call(call) if matches!(call.callee, AstExpr::Var(AstNameRef::Local(local)) if self.opaque_locals.contains(&local)) => {
                call.method_key.is_none()
                    && call.args.iter().enumerate().all(|(index, arg)| {
                        self.check(arg, top + 1 + call.args.len(), index + 1 < call.args.len())
                    })
            }
            AstExpr::MethodCall(call) => {
                plain_expr(&call.receiver, self.callees)
                    && call.args.iter().enumerate().all(|(index, arg)| {
                        self.check(arg, top + 2 + call.args.len(), index + 1 < call.args.len())
                    })
            }
            _ => plain_expr(expr, self.callees) && (fixed_one || open_tail_unchanged(expr)),
        }
    }
}

fn callee_body(
    func: &AstFunctionExpr,
    body: HirLuauInliningBody,
    expected_field: &crate::LuaString,
    capture: Option<crate::hir::LocalId>,
) -> bool {
    if let HirLuauInliningBody::ConditionalMethod { template } = body {
        return conditional_methods::body(func, template);
    }
    if let HirLuauInliningBody::SnapshotClosureFactory { template } = body {
        return snapshot_closure_factory(func, template);
    }
    if let HirLuauInliningBody::PublishedTableFactory { key } = body {
        return published_table_factory(func, key, capture);
    }
    if let HirLuauInliningBody::PublishedClosureFactory {
        intermediate,
        leaf,
        result,
    } = body
    {
        return published_closure_factory(func, expected_field, intermediate, leaf, result);
    }
    if let HirLuauInliningBody::EventClosureFactory {
        intermediate,
        result,
    } = body
    {
        return event_closure_factory(func, expected_field, intermediate, result);
    }
    if let HirLuauInliningBody::ValueClosureFactory { template } = body {
        return value_closure_factory_body(func, template);
    }
    if let HirLuauInliningBody::NestedValueClosureFactory {
        intermediate,
        result,
    } = body
    {
        return nested_value_closure_factory_body(func, intermediate, result);
    }
    if body == HirLuauInliningBody::CapturedAddIdentity {
        return captured_identity_body(func, capture);
    }
    if let HirLuauInliningBody::TableFactory { shared } = body {
        return table_factory_body(func, shared, expected_field);
    }
    if let HirLuauInliningBody::ClosureFactory { shared } = body {
        return closure_factory_body(func, shared, capture);
    }
    if body == HirLuauInliningBody::CapturedConcatSum {
        return captured_concat_body(func, expected_field, capture);
    }
    // pinned Luau 中 UnpackedTable 的 cost=25、stack=4，FrozenTableIndex 的
    // cost=23、stack=5；基础阈值 25 经收益调整均为 28。两种 body 无递归和
    // 可内联子调用，调用点的固定单结果与 regTop 上限由 validate 核对。
    if func.params.len() != 1
        || func.is_vararg
        || func.named_vararg.is_some()
        || !func.captured_bindings.is_empty()
        || !func.captured_params.is_empty()
        || !func.capture_write_names.is_empty()
    {
        return false;
    }
    if let HirLuauInliningBody::ScalarNotCall {
        prefix,
        suffix,
        fastcall,
    } = body
    {
        return scalar_not_body(func, expected_field, prefix, suffix, fastcall);
    }
    let [AstStmt::Return(ret)] = func.body.stmts.as_slice() else {
        return false;
    };
    if body == HirLuauInliningBody::Identity {
        return ret.values == [AstExpr::Var(AstNameRef::Param(func.params[0]))];
    }
    let call = match (body, ret.values.as_slice()) {
        (HirLuauInliningBody::UnpackedTable, [AstExpr::TableConstructor(table)]) => {
            let [AstTableField::Array(AstExpr::Call(call))] = table.fields.as_slice() else {
                return false;
            };
            if !table_callee(call, "unpack") {
                return false;
            }
            call
        }
        (HirLuauInliningBody::FrozenTableIndex, [AstExpr::IndexAccess(index)]) => {
            if !matches!(index.index, AstExpr::Integer(1)) {
                return false;
            }
            let AstExpr::Call(pack) = &index.base else {
                return false;
            };
            let [AstExpr::Call(freeze)] = pack.args.as_slice() else {
                return false;
            };
            if !table_callee(pack, "pack") || !table_callee(freeze, "freeze") {
                return false;
            }
            freeze
        }
        _ => return false,
    };
    let [AstExpr::LogicalOr(logical)] = call.args.as_slice() else {
        return false;
    };
    matches!((&logical.lhs, &logical.rhs),
        (AstExpr::FieldAccess(field), AstExpr::TableConstructor(empty))
        if field.base == AstExpr::Var(AstNameRef::Param(func.params[0]))
            && Some(field.field.as_str()) == expected_field.as_utf8()
            && empty.fields.is_empty())
}

fn published_table_factory(
    func: &AstFunctionExpr,
    key: i64,
    capture: Option<crate::hir::LocalId>,
) -> bool {
    let Some(capture) = capture else {
        return false;
    };
    if func.is_vararg
        || !func.params.is_empty()
        || func.named_vararg.is_some()
        || func.captured_bindings != BTreeSet::from([AstBindingRef::Local(capture)])
        || !func.captured_params.is_empty()
        || !func.capture_write_names.is_empty()
    {
        return false;
    }
    let [
        AstStmt::LocalDecl(decl),
        AstStmt::Assign(assign),
        AstStmt::Return(ret),
    ] = func.body.stmts.as_slice()
    else {
        return false;
    };
    let ([binding], [AstExpr::TableConstructor(table)]) =
        (decl.bindings.as_slice(), decl.values.as_slice())
    else {
        return false;
    };
    let [AstLValue::IndexAccess(access)] = assign.targets.as_slice() else {
        return false;
    };
    // 无参数、无嵌套函数且只有分配/发布/返回；固定小整数键保持 SETTABLEN。
    // 捕获不重绑定，Luau 可以把它投影为 caller 的同一低槽表。
    (1..=256).contains(&key)
        && table.fields.is_empty()
        && access.base == AstExpr::Var(AstNameRef::Upvalue(crate::hir::UpvalueId(0)))
        && access.index == AstExpr::Integer(key)
        && assign.values == [AstExpr::Var(binding.id.to_name_ref())]
        && ret.values == assign.values
}

// pinned CostModel 对返回闭包计 cost=10；子函数体不计入工厂，不会越过内联阈值。
fn value_closure_factory_body(func: &AstFunctionExpr, template: usize) -> bool {
    if func.params.len() != 1
        || func.is_vararg
        || func.named_vararg.is_some()
        || !func.captured_bindings.is_empty()
        || !func.captured_params.is_empty()
        || !func.capture_write_names.is_empty()
    {
        return false;
    }
    let [AstStmt::Return(ret)] = func.body.stmts.as_slice() else {
        return false;
    };
    let [AstExpr::FunctionExpr(child)] = ret.values.as_slice() else {
        return false;
    };
    child.creation == Some(crate::hir::HirClosureCreation::Fresh { template })
        && child.captured_bindings.is_empty()
        && child.captured_params == BTreeSet::from([func.params[0]])
        && child.capture_write_names.is_empty()
        && !child.is_vararg
        && child.named_vararg.is_none()
        && matches!(child.body.stmts.as_slice(), [AstStmt::Return(ret)]
            if matches!(ret.values.as_slice(), [value] if value_capture_result(value)))
}

// 两层工厂各创建一个闭包；CostModel 对外层计闭包 10 加调用 4，内层计 10。
// 固定单返回避免 multRet 阻止内联，返回闭包内部的运行表达式不参与常量替换。
fn nested_value_closure_factory_body(
    func: &AstFunctionExpr,
    intermediate: usize,
    result: usize,
) -> bool {
    if func.params.len() != 1
        || func.is_vararg
        || func.named_vararg.is_some()
        || !func.captured_bindings.is_empty()
        || !func.captured_params.is_empty()
        || !func.capture_write_names.is_empty()
    {
        return false;
    }
    let [AstStmt::LocalFunctionDecl(inner), AstStmt::Return(ret)] = func.body.stmts.as_slice()
    else {
        return false;
    };
    // 候选拒绝[TargetConstraint]：Luau 不内联 multRet 调用，返回树必须保留 fixed-one 包装。
    let [AstExpr::SingleValue(value)] = ret.values.as_slice() else {
        return false;
    };
    let AstExpr::Call(call) = value.as_ref() else {
        return false;
    };
    let child = &inner.func;
    // 候选拒绝[TargetConstraint]：内层函数须保持已签证的固定工厂体，才能保证两次调用都在 O2 消失。
    if call.callee != AstExpr::Var(inner.name.to_name_ref())
        || call.method_key.is_some()
        || call.required_luau_inlining.is_some()
        || call.args != [AstExpr::Var(AstNameRef::Param(func.params[0]))]
        || child.creation
            != Some(crate::hir::HirClosureCreation::Fresh {
                template: intermediate,
            })
        || child.params.len() != 1
        || child.is_vararg
        || child.named_vararg.is_some()
        || !child.captured_bindings.is_empty()
        || child.captured_params != BTreeSet::from([func.params[0]])
        || !child.capture_write_names.is_empty()
    {
        return false;
    }
    let [AstStmt::Return(ret)] = child.body.stmts.as_slice() else {
        return false;
    };
    let [AstExpr::FunctionExpr(leaf)] = ret.values.as_slice() else {
        return false;
    };
    leaf.creation == Some(crate::hir::HirClosureCreation::Fresh { template: result })
        && leaf.captured_bindings.is_empty()
        && leaf.captured_params == BTreeSet::from([child.params[0]])
        && leaf.capture_write_names.is_empty()
        && !leaf.is_vararg
        && leaf.named_vararg.is_none()
        && matches!(leaf.body.stmts.as_slice(), [AstStmt::Return(ret)]
            if matches!(ret.values.as_slice(), [value] if value_capture_result(value)))
}

fn value_capture_result(value: &AstExpr) -> bool {
    match value {
        AstExpr::Var(AstNameRef::Param(_) | AstNameRef::Upvalue(_)) => true,
        AstExpr::Unary(unary) => value_capture_result(&unary.expr),
        AstExpr::Binary(binary) => {
            value_capture_result(&binary.lhs) && value_capture_result(&binary.rhs)
        }
        _ => false,
    }
}

fn captured_identity_body(func: &AstFunctionExpr, capture: Option<crate::hir::LocalId>) -> bool {
    let Some(capture) = capture else {
        return false;
    };
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
    let ([AstLValue::Name(AstNameRef::Upvalue(upvalue))], [AstExpr::Binary(add)]) =
        (assign.targets.as_slice(), assign.values.as_slice())
    else {
        return false;
    };
    let parameter = AstExpr::Var(AstNameRef::Param(func.params[0]));
    *upvalue == crate::hir::UpvalueId(0)
        && add.op == AstBinaryOpKind::Add
        && add.lhs == AstExpr::Var(AstNameRef::Upvalue(*upvalue))
        && add.rhs == parameter
        && ret.values == [parameter]
}

fn table_factory_body(func: &AstFunctionExpr, shared: usize, method: &crate::LuaString) -> bool {
    if !func.params.is_empty()
        || func.is_vararg
        || func.named_vararg.is_some()
        || !func.captured_bindings.is_empty()
        || !func.captured_params.is_empty()
        || !func.capture_write_names.is_empty()
    {
        return false;
    }
    let [
        AstStmt::LocalDecl(decl),
        AstStmt::FunctionDecl(install),
        AstStmt::Return(ret),
    ] = func.body.stmts.as_slice()
    else {
        return false;
    };
    let ([binding], [AstExpr::TableConstructor(table)]) =
        (decl.bindings.as_slice(), decl.values.as_slice())
    else {
        return false;
    };
    let AstFunctionName::Method(path, name) = &install.target else {
        return false;
    };
    // pinned CostModel 对建表、字面量字段和方法安装至多计 21 + 字段数，
    // 四个字段以内不超过基础阈值 25；子方法体不会计入工厂的执行成本。
    table.fields.len() <= 4 && table.fields.iter().all(|field| matches!(field,
        AstTableField::Record(record) if matches!(record.key, AstTableKey::Name(_))
            && matches!(record.value, AstExpr::Nil | AstExpr::Boolean(_) | AstExpr::Integer(_) | AstExpr::Number(_) | AstExpr::String(_))))
        && path.root == binding.id.to_name_ref() && path.fields.is_empty() && method.as_utf8() == Some(name)
        && ret.values == [AstExpr::Var(binding.id.to_name_ref())]
        && install.func.creation == Some(crate::hir::HirClosureCreation::MayReuse { template: shared })
        && install.func.captured_bindings.is_empty() && install.func.captured_params.is_empty()
        && method_body(&install.func)
}

// 对安装的方法保留字段 ADD；参数不是常量，O2 不会折叠此读改写，也没有子调用。
fn method_body(func: &AstFunctionExpr) -> bool {
    if func.is_vararg || func.named_vararg.is_some() || func.params.len() != 2 {
        return false;
    }
    let [AstStmt::Assign(assign), AstStmt::Return(ret)] = func.body.stmts.as_slice() else {
        return false;
    };
    let ([AstLValue::FieldAccess(target)], [AstExpr::Binary(add)]) =
        (assign.targets.as_slice(), assign.values.as_slice())
    else {
        return false;
    };
    let receiver = AstExpr::Var(AstNameRef::Param(func.params[0]));
    target.base == receiver
        && add.op == AstBinaryOpKind::Add
        && add.lhs == AstExpr::FieldAccess(target.clone())
        && add.rhs == AstExpr::Var(AstNameRef::Param(func.params[1]))
        && ret.values == [receiver]
}

fn closure_factory_body(
    func: &AstFunctionExpr,
    shared: usize,
    capture: Option<crate::hir::LocalId>,
) -> bool {
    let Some(capture) = capture else {
        return false;
    };
    if !func.params.is_empty()
        || func.is_vararg
        || func.named_vararg.is_some()
        || func.captured_bindings != BTreeSet::from([AstBindingRef::Local(capture)])
        || !func.captured_params.is_empty()
        || !func.capture_write_names.is_empty()
    {
        return false;
    }
    let [AstStmt::Return(ret)] = func.body.stmts.as_slice() else {
        return false;
    };
    let [AstExpr::FunctionExpr(child)] = ret.values.as_slice() else {
        return false;
    };
    if child.creation != Some(crate::hir::HirClosureCreation::MayReuse { template: shared })
        || child.is_vararg
        || child.named_vararg.is_some()
        || !child.captured_params.is_empty()
        || !child.captured_bindings.is_empty()
        || !child.capture_write_names.is_empty()
    {
        return false;
    }
    let Some((AstStmt::Return(ret), prefix)) = child.body.stmts.split_last() else {
        return false;
    };
    // child 在父工厂编译完成前编译；对父函数的尾调用不能被递归内联。
    let [AstExpr::Call(call)] = ret.values.as_slice() else {
        return false;
    };
    call.required_luau_inlining.is_none() && call.method_key.is_none() && call.args.is_empty()
        && call.callee==AstExpr::Var(AstNameRef::Upvalue(crate::hir::UpvalueId(0)))
        && prefix.iter().all(|stmt| matches!(stmt, AstStmt::CallStmt(stmt)
            if matches!(&stmt.call, AstCallKind::Call(call)
                if matches!(&call.callee, AstExpr::Var(AstNameRef::Global(name)) if name.text=="assert")
                && call.required_luau_inlining.is_none() && call.method_key.is_none()
                && plain_values(&call.args, &BTreeMap::new(), false))))
}

fn captured_concat_body(
    func: &AstFunctionExpr,
    suffix: &crate::LuaString,
    capture: Option<crate::hir::LocalId>,
) -> bool {
    let Some(capture) = capture else {
        return false;
    };
    // 三个不改写的形参，单次 CONCAT/SETUPVAL 与两次 ADD；无子调用、递归或分支。
    // pinned Luau 的 cost 低于基础内联阈值，stack=6；调用语境另核对固定单结果。
    if func.params.len() != 3
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
    let (
        [AstLValue::Name(AstNameRef::Upvalue(upvalue))],
        [AstExpr::Binary(concat)],
        [AstExpr::Binary(sum)],
    ) = (
        assign.targets.as_slice(),
        assign.values.as_slice(),
        ret.values.as_slice(),
    )
    else {
        return false;
    };
    let AstExpr::Binary(first) = &sum.lhs else {
        return false;
    };
    *upvalue == crate::hir::UpvalueId(0)
        && concat.op == AstBinaryOpKind::Concat
        && concat.lhs == AstExpr::Var(AstNameRef::Upvalue(*upvalue))
        && concat.rhs == AstExpr::String(suffix.clone())
        && first.op == AstBinaryOpKind::Add
        && sum.op == AstBinaryOpKind::Add
        && first.lhs == AstExpr::Var(AstNameRef::Param(func.params[0]))
        && first.rhs == AstExpr::Var(AstNameRef::Param(func.params[1]))
        && sum.rhs == AstExpr::Var(AstNameRef::Param(func.params[2]))
}

fn scalar_not_body(
    func: &AstFunctionExpr,
    callee: &crate::LuaString,
    prefix: usize,
    suffix: usize,
    fastcall: bool,
) -> bool {
    // pinned CostModel 中普通全局 CALL 至多 cost=4+NOT 数；这里不依赖收益 boost。
    // prefix local 必须被逐次改写，阻止常量实参把整条 NOT 树折成一个 LOADBOOL。
    if prefix < 2 || suffix == 0 || prefix + suffix > 21 || func.body.stmts.len() != prefix + 1 {
        return false;
    }
    let AstStmt::LocalDecl(decl) = &func.body.stmts[0] else {
        return false;
    };
    let ([binding], [AstExpr::Unary(initial)]) = (decl.bindings.as_slice(), decl.values.as_slice())
    else {
        return false;
    };
    if initial.op != AstUnaryOpKind::Not
        || initial.expr != AstExpr::Var(AstNameRef::Param(func.params[0]))
    {
        return false;
    }
    let local = binding.id.to_name_ref();
    if !func.body.stmts[1..prefix].iter().all(|stmt| matches!(stmt,
        AstStmt::Assign(assign) if matches!((assign.targets.as_slice(), assign.values.as_slice()),
            ([AstLValue::Name(target)], [AstExpr::Unary(unary)])
                if *target == local && unary.op == AstUnaryOpKind::Not && unary.expr == AstExpr::Var(local.clone()))))
    {
        return false;
    }
    let AstStmt::Return(ret) = &func.body.stmts[prefix] else {
        return false;
    };
    let call = match ret.values.as_slice() {
        [AstExpr::SingleValue(value)] => match value.as_ref() {
            AstExpr::Call(call) => call,
            _ => return false,
        },
        [AstExpr::Call(call)] if fastcall => call,
        _ => return false,
    };
    if (fastcall && !matches!(callee.as_utf8(), Some("type" | "tostring")))
        || call.required_luau_inlining.is_some()
        || call.method_key.is_some()
        || !matches!(&call.callee, AstExpr::Var(AstNameRef::Global(name)) if callee.as_utf8() == Some(name.text.as_str()))
    {
        return false;
    }
    let [arg] = call.args.as_slice() else {
        return false;
    };
    let mut arg = arg;
    for _ in 0..suffix {
        let AstExpr::Unary(unary) = arg else {
            return false;
        };
        if unary.op != AstUnaryOpKind::Not {
            return false;
        }
        arg = &unary.expr;
    }
    *arg == AstExpr::Var(local)
}

fn table_callee(call: &AstCallExpr, expected: &str) -> bool {
    call.required_luau_inlining.is_none()
        && matches!(&call.callee, AstExpr::FieldAccess(field)
        if field.field == expected && matches!(&field.base,
            AstExpr::Var(AstNameRef::Global(name)) if name.text == "table"))
}

/// 外围调用不解析 local 函数，避免 O2 额外内联；global 仅作为已核对的 callee，
/// 同时排除 math 常量折叠与 getfenv/setfenv 对整个模块编译模式的影响。
fn plain_expr(
    expr: &AstExpr,
    callees: &BTreeMap<crate::hir::LocalId, crate::hir::HirProtoRef>,
) -> bool {
    match expr {
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_) => true,
        AstExpr::Var(AstNameRef::Global(name)) if name.text == "print" => true,
        AstExpr::Var(AstNameRef::Local(local)) => !callees.contains_key(local),
        AstExpr::Var(AstNameRef::Param(_) | AstNameRef::Upvalue(_)) => true,
        AstExpr::Call(call) => {
            // pcall 不参与 getFunctionExpr；作为其首实参传递的函数值不会额外内联。
            if matches!(&call.callee, AstExpr::Var(AstNameRef::Global(name)) if name.text == "pcall")
            {
                return call.required_luau_inlining.is_none()
                    && call.method_key.is_none()
                    && matches!(call.args.first(), Some(AstExpr::Var(AstNameRef::Local(_))))
                    && plain_values(&call.args[1..], callees, false);
            }
            call.required_luau_inlining.is_none()
                && call.method_key.is_none()
                && (opaque_callee(call)
                    || matches!(&call.callee, AstExpr::Var(AstNameRef::Global(name))
                        if matches!(name.text.as_str(), "getmetatable" | "setmetatable" | "type" | "tostring"))
                    // max 只在所有参数均为数值常量时折叠；不透明索引调用排除此条件。
                    || (matches!(&call.callee, AstExpr::FieldAccess(field)
                        if field.field == "max" && matches!(&field.base,
                            AstExpr::Var(AstNameRef::Global(name)) if name.text == "math"))
                        && call.args.iter().any(|arg| matches!(arg, AstExpr::Call(inner)
                            if matches!(inner.callee, AstExpr::IndexAccess(_))))))
                && (!matches!(call.callee, AstExpr::IndexAccess(_))
                    || plain_expr(&call.callee, callees))
                && plain_values(&call.args, callees, false)
        }
        AstExpr::FunctionExpr(function) => plain_function(function, callees),
        AstExpr::SingleValue(value) => plain_expr(value, callees),
        AstExpr::FieldAccess(field) => plain_expr(&field.base, callees),
        AstExpr::IndexAccess(index) => {
            plain_expr(&index.base, callees) && plain_expr(&index.index, callees)
        }
        AstExpr::Unary(unary) => {
            matches!(unary.op, AstUnaryOpKind::Length | AstUnaryOpKind::Not)
                && plain_expr(&unary.expr, callees)
        }
        AstExpr::Binary(binary) => {
            (matches!(
                binary.op,
                AstBinaryOpKind::Eq
                    | AstBinaryOpKind::Lt
                    | AstBinaryOpKind::Le
                    | AstBinaryOpKind::Gt
                    | AstBinaryOpKind::Ge
                    | AstBinaryOpKind::Concat
            ) || (binary.op == AstBinaryOpKind::Add
                && matches!(binary.rhs, AstExpr::Integer(_) | AstExpr::Number(_))))
                && plain_expr(&binary.lhs, callees)
                && plain_expr(&binary.rhs, callees)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            plain_expr(&logical.lhs, callees) && plain_expr(&logical.rhs, callees)
        }
        AstExpr::TableConstructor(table) => {
            table
                .fields
                .iter()
                .enumerate()
                .all(|(index, field)| match field {
                    AstTableField::Array(value) => {
                        plain_expr(value, callees)
                            && (index + 1 < table.fields.len() || open_tail_unchanged(value))
                    }
                    AstTableField::Record(record) => {
                        (match &record.key {
                            AstTableKey::Name(_) => true,
                            AstTableKey::Expr(key) => plain_expr(key, callees),
                        }) && plain_expr(&record.value, callees)
                    }
                })
        }
        _ => false,
    }
}

fn opaque_callee(call: &AstCallExpr) -> bool {
    // pinned Luau 不把这几个库调用识别为 builtin；索引调用也不参与 getFunctionExpr。
    ["pack", "freeze", "isfrozen", "concat"]
        .iter()
        .any(|name| table_callee(call, name))
        || matches!(&call.callee, AstExpr::Var(AstNameRef::Global(name)) if matches!(name.text.as_str(), "next" | "collectgarbage" | "pcall"))
        || matches!(&call.callee, AstExpr::IndexAccess(_))
}

fn open_tail_unchanged(expr: &AstExpr) -> bool {
    // O2 的已知单返回 builtin 会把 open 尾部压为一个值；外围不能借 pragma 改变它。
    !matches!(expr, AstExpr::Call(call) if !opaque_callee(call))
}

fn plain_values(
    values: &[AstExpr],
    callees: &BTreeMap<crate::hir::LocalId, crate::hir::HirProtoRef>,
    fixed_one: bool,
) -> bool {
    values.iter().enumerate().all(|(index, value)| {
        plain_expr(value, callees)
            && (fixed_one || index + 1 < values.len() || open_tail_unchanged(value))
    })
}

fn plain_assign(
    assign: &AstAssign,
    callees: &BTreeMap<crate::hir::LocalId, crate::hir::HirProtoRef>,
) -> bool {
    assign.targets.iter().all(|target| match target {
        AstLValue::Name(name) => plain_expr(&AstExpr::Var(name.clone()), callees),
        AstLValue::FieldAccess(field) => plain_expr(&field.base, callees),
        AstLValue::IndexAccess(index) => {
            plain_expr(&index.base, callees) && plain_expr(&index.index, callees)
        }
    }) && plain_values(
        &assign.values,
        callees,
        assign.targets.len() == assign.values.len(),
    )
}

fn plain_function(
    function: &AstFunctionExpr,
    callees: &BTreeMap<crate::hir::LocalId, crate::hir::HirProtoRef>,
) -> bool {
    if function.is_vararg
        || function.named_vararg.is_some()
        || function.captured_bindings.iter().any(
            |binding| matches!(binding, AstBindingRef::Local(local) if callees.contains_key(local)),
        )
    {
        return false;
    }
    // LocalId 属于 child 自身；进入函数前已排除 required callee 的跨层捕获。
    let locals = BTreeMap::new();
    plain_block(&function.body, &locals)
}

fn plain_field_function(
    decl: &AstFunctionDecl,
    callees: &BTreeMap<crate::hir::LocalId, crate::hir::HirProtoRef>,
) -> bool {
    let path = match &decl.target {
        AstFunctionName::Plain(path) if !path.fields.is_empty() => path,
        AstFunctionName::Method(path, _) => path,
        _ => return false,
    };
    plain_expr(&AstExpr::Var(path.root.clone()), callees) && plain_function(&decl.func, callees)
}

fn plain_block(
    block: &AstBlock,
    locals: &BTreeMap<crate::hir::LocalId, crate::hir::HirProtoRef>,
) -> bool {
    block.stmts.iter().all(|stmt| match stmt {
        AstStmt::LocalDecl(decl) => plain_values(
            &decl.values,
            locals,
            decl.bindings.len() == decl.values.len(),
        ),
        AstStmt::Assign(assign) => plain_assign(assign, locals),
        AstStmt::Return(ret) => plain_values(&ret.values, locals, false),
        AstStmt::CallStmt(stmt) => matches!(&stmt.call, AstCallKind::Call(call)
            if call.required_luau_inlining.is_none() && call.method_key.is_none()
                && (opaque_callee(call) || matches!(&call.callee, AstExpr::Var(AstNameRef::Global(name))
                    if name.text == "assert" || name.text == "print"))
                && plain_values(&call.args, locals, false)),
        AstStmt::LocalFunctionDecl(decl) => plain_function(&decl.func, locals),
        AstStmt::FunctionDecl(decl) => plain_field_function(decl, locals),
        AstStmt::If(branch) => plain_expr(&branch.cond, locals)
            && plain_block(&branch.then_block, locals)
            && branch.else_block.as_ref().is_none_or(|block| plain_block(block, locals)),
        _ => false,
    })
}

// 合成工厂只创建一个 reusable closure 或两层依赖；对应 CostModel 为 10/20。
// 依赖函数为 vararg 时，返回闭包中的调用不会被 O2 内联。
fn shared_closure_factory(func: &AstFunctionExpr) -> bool {
    if func.creation.is_some()
        || !func.params.is_empty()
        || func.is_vararg
        || func.named_vararg.is_some()
        || !func.capture_write_names.is_empty()
    {
        return false;
    }
    shared_closure_body(&func.body.stmts)
}

fn shared_closure_body(stmts: &[AstStmt]) -> bool {
    let leaf = |child: &AstFunctionExpr| {
        matches!(
            child.creation,
            Some(crate::hir::HirClosureCreation::MayReuse { .. })
        ) && child.capture_write_names.is_empty()
            && child.params.is_empty()
            && child.named_vararg.is_none()
    };
    let body = match stmts {
        [AstStmt::LocalDecl(decl), rest @ ..]
            if matches!(
                (decl.bindings.as_slice(), decl.values.as_slice()),
                ([_], [AstExpr::Integer(_)])
            ) =>
        {
            rest
        }
        stmts => stmts,
    };
    match body {
        [AstStmt::Return(ret)] => {
            let [AstExpr::FunctionExpr(child)] = ret.values.as_slice() else {
                return false;
            };
            matches!(
                child.creation,
                Some(crate::hir::HirClosureCreation::MayReuse { .. })
            ) && child.capture_write_names.is_empty()
                && plain_function(child, &BTreeMap::new())
        }
        [AstStmt::LocalFunctionDecl(owner), AstStmt::Return(ret)] => {
            let [AstExpr::FunctionExpr(child)] = ret.values.as_slice() else {
                return false;
            };
            let [AstStmt::Return(owner_ret)] = owner.func.body.stmts.as_slice() else {
                return false;
            };
            let [AstStmt::Return(child_ret)] = child.body.stmts.as_slice() else {
                return false;
            };
            let [AstExpr::Call(call)] = child_ret.values.as_slice() else {
                return false;
            };
            leaf(&owner.func)
                && owner.func.is_vararg
                && leaf(child)
                && !child.is_vararg
                && matches!(
                    owner_ret.values.as_slice(),
                    [AstExpr::Var(AstNameRef::Upvalue(_)) | AstExpr::Integer(_)]
                )
                && child.captured_bindings == BTreeSet::from([owner.name])
                && child.captured_params.is_empty()
                && call.callee == AstExpr::Var(AstNameRef::Upvalue(crate::hir::UpvalueId(0)))
                && call.args.is_empty()
                && call.method_key.is_none()
                && call.required_luau_inlining.is_none()
        }
        _ => false,
    }
}

/// 对直线工厂给出 pinned CostModel 的保守上界；只有整份 body 在基础阈值内才签证。
/// 外围要求固定单结果与小整数实参，body 不含递归、控制流或可内联的 local 调用。
fn snapshot_closure_factory(func: &AstFunctionExpr, template: usize) -> bool {
    if func.params.len() != 1
        || func.is_vararg
        || func.named_vararg.is_some()
        || !func.captured_bindings.is_empty()
        || !func.captured_params.is_empty()
        || !func.capture_write_names.is_empty()
    {
        return false;
    }
    fn operand(value: &AstExpr, depth: usize) -> Option<usize> {
        if depth > 4 {
            return None;
        }
        match value {
            AstExpr::Integer(_)
            | AstExpr::String(_)
            | AstExpr::Nil
            | AstExpr::Var(AstNameRef::Local(_) | AstNameRef::Param(_)) => Some(0),
            AstExpr::Number(value)
                if value.to_bits() != (-0.0f64).to_bits()
                    && *value >= f64::from(i32::MIN)
                    && *value <= f64::from(i32::MAX)
                    && value.fract() == 0.0 =>
            {
                Some(0)
            }
            AstExpr::Binary(binary)
                if matches!(
                    binary.op,
                    AstBinaryOpKind::Add | AstBinaryOpKind::Sub | AstBinaryOpKind::Mul
                ) =>
            {
                Some(1 + operand(&binary.lhs, depth + 1)? + operand(&binary.rhs, depth + 1)?)
            }
            _ => None,
        }
    }
    fn call_cost(call: &AstCallExpr) -> Option<usize> {
        let AstExpr::Var(AstNameRef::Global(name)) = &call.callee else {
            return None;
        };
        if call.required_luau_inlining.is_some() || call.method_key.is_some() || call.args.len() > 4
        {
            return None;
        }
        // 这些 builtin 不因数值实参常量折叠；print 保持普通 CALL。
        let builtin = matches!(name.text.as_str(), "tostring" | "type");
        if !builtin && name.text != "print" {
            return None;
        }
        let mut cost = if builtin { 2 } else { 4 };
        for value in &call.args {
            let value = operand(value, 0)?;
            cost += if builtin && call.args.len() <= 2 {
                value
            } else {
                value.max(1)
            };
        }
        Some(cost)
    }
    let leaf = |child: &AstFunctionExpr| {
        child.creation == Some(crate::hir::HirClosureCreation::Fresh { template })
            && child.params.is_empty()
            && !child.is_vararg
            && child.named_vararg.is_none()
            && child.captured_params.is_empty()
            && child.capture_write_names.is_empty()
            && matches!(child.body.stmts.as_slice(), [AstStmt::Return(ret)]
                if matches!(ret.values.as_slice(), [AstExpr::Var(AstNameRef::Upvalue(_))]))
    };
    let flat = scope_statements(&func.body);
    let Some((AstStmt::Return(ret), prefix)) =
        flat.split_last().map(|(last, prefix)| (*last, prefix))
    else {
        return false;
    };
    let mut cost = 0;
    let mut locals = 1;
    let mut result = None;
    for stmt in prefix {
        match stmt {
            AstStmt::LocalDecl(decl) => {
                let ([binding], [value]) = (decl.bindings.as_slice(), decl.values.as_slice())
                else {
                    return false;
                };
                locals += 1;
                match value {
                    AstExpr::Nil => {}
                    AstExpr::Call(call) => {
                        let Some(value) = call_cost(call) else {
                            return false;
                        };
                        cost += value;
                    }
                    AstExpr::FunctionExpr(child) if leaf(child) && result.is_none() => {
                        result = Some(binding.id.to_name_ref());
                        cost += 10;
                    }
                    _ => return false,
                }
            }
            AstStmt::FunctionDecl(decl) if leaf(&decl.func) && result.is_none() => {
                let AstFunctionName::Plain(path) = &decl.target else {
                    return false;
                };
                if !path.fields.is_empty() || !matches!(path.root, AstNameRef::Local(_)) {
                    return false;
                }
                result = Some(path.root.clone());
                cost += 10;
            }
            AstStmt::LocalFunctionDecl(decl) if leaf(&decl.func) && result.is_none() => {
                result = Some(decl.name.to_name_ref());
                cost += 10;
                locals += 1;
            }
            AstStmt::Assign(assign) => {
                let (
                    [AstLValue::Name(target @ AstNameRef::Local(_))],
                    [AstExpr::FunctionExpr(child)],
                ) = (assign.targets.as_slice(), assign.values.as_slice())
                else {
                    return false;
                };
                if !leaf(child) || result.is_some() {
                    return false;
                }
                result = Some(target.clone());
                cost += 10;
            }
            AstStmt::CallStmt(stmt) => {
                let AstCallKind::Call(call) = &stmt.call else {
                    return false;
                };
                let Some(value) = call_cost(call) else {
                    return false;
                };
                cost += value;
            }
            _ => return false,
        }
    }
    // locals 与 operand/callee scratch 的上界共同低于 stackSize=32；字面量实参的
    // cost 折扣只会降低成本，不依赖阈值收益放大或额外递归内联。
    cost <= 25 && locals <= 16 && result.is_some_and(|result| ret.values == [AstExpr::Var(result)])
}

fn event_closure_factory(
    func: &AstFunctionExpr,
    label: &crate::LuaString,
    intermediate: usize,
    result: usize,
) -> bool {
    // 事件 CALL cost=6，加两层 closure cost=20；字符串实参直接写入原参数槽。
    if func.creation.is_some()
        || func.params.len() != 1
        || func.is_vararg
        || func.named_vararg.is_some()
        || !func.capture_write_names.is_empty()
    {
        return false;
    }
    let [
        AstStmt::CallStmt(event),
        AstStmt::LocalFunctionDecl(owner),
        AstStmt::Return(ret),
    ] = func.body.stmts.as_slice()
    else {
        return false;
    };
    let AstCallKind::Call(call) = &event.call else {
        return false;
    };
    let [AstExpr::FunctionExpr(child)] = ret.values.as_slice() else {
        return false;
    };
    call.required_luau_inlining.is_none()
        && call.method_key.is_none()
        && matches!(&call.callee, AstExpr::Var(AstNameRef::Global(name)) if name.text == "print")
        && call.args
            == vec![
                AstExpr::String(label.clone()),
                AstExpr::Var(AstNameRef::Param(func.params[0])),
            ]
        && owner.func.creation
            == Some(crate::hir::HirClosureCreation::MayReuse {
                template: intermediate,
            })
        && child.creation == Some(crate::hir::HirClosureCreation::MayReuse { template: result })
        && owner.func.captured_params.is_empty()
        && shared_closure_body(&func.body.stmts[1..])
}

fn published_closure_factory(
    func: &AstFunctionExpr,
    field: &crate::LuaString,
    intermediate: usize,
    leaf: usize,
    result: usize,
) -> bool {
    // pinned CostModel: outer=24、inner=10，均低于基础阈值；调用深度最多二层。
    if func.creation.is_some()
        || !func.params.is_empty()
        || func.is_vararg
        || func.named_vararg.is_some()
        || !func.capture_write_names.is_empty()
    {
        return false;
    }
    let [
        AstStmt::LocalFunctionDecl(inner),
        AstStmt::Assign(publish),
        AstStmt::Return(ret),
    ] = func.body.stmts.as_slice()
    else {
        return false;
    };
    let (
        [AstLValue::Name(AstNameRef::Global(target))],
        [AstExpr::Call(call)],
        [AstExpr::FunctionExpr(output)],
    ) = (
        publish.targets.as_slice(),
        publish.values.as_slice(),
        ret.values.as_slice(),
    )
    else {
        return false;
    };
    let [AstStmt::Return(inner_return)] = inner.func.body.stmts.as_slice() else {
        return false;
    };
    let [AstExpr::FunctionExpr(published)] = inner_return.values.as_slice() else {
        return false;
    };
    let readonly_leaf = |child: &AstFunctionExpr, template| {
        child.creation == Some(crate::hir::HirClosureCreation::MayReuse { template })
            && child.params.is_empty()
            && !child.is_vararg
            && child.named_vararg.is_none()
            && child.captured_params.is_empty()
            && child.capture_write_names.is_empty()
            && matches!(child.body.stmts.as_slice(), [AstStmt::Return(ret)]
                if ret.values == [AstExpr::Var(AstNameRef::Upvalue(crate::hir::UpvalueId(0)))])
    };
    field.as_utf8() == Some(target.text.as_str())
        && call.callee == AstExpr::Var(inner.name.to_name_ref())
        && call.args.is_empty()
        && call.method_key.is_none()
        && call.required_luau_inlining.is_none()
        && inner.func.creation
            == Some(crate::hir::HirClosureCreation::MayReuse {
                template: intermediate,
            })
        && inner.func.params.is_empty()
        && !inner.func.is_vararg
        && inner.func.named_vararg.is_none()
        && inner.func.captured_params.is_empty()
        && inner.func.capture_write_names.is_empty()
        && readonly_leaf(published, leaf)
        && readonly_leaf(output, result)
        && published.captured_bindings.is_empty()
        && output.captured_bindings == BTreeSet::from([inner.name])
}
