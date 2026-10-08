//! 在最终源码树上核对必须消失的 Luau 调用。
//!
//! 消费 HIR 对原展开帧及参数替换的证明，核对固定函数体、固定返回宽度和
//! caller 声明前缀。外围语法须不引起额外的 O2 改写；全部 occurrence 通过后才可
//! 发射所需 optimize pragma，该编译要求不能随展示注释一起关闭。

use crate::ast::*;
use crate::hir::HirLuauInliningBody;
use std::collections::{BTreeMap, BTreeSet};

mod array_fold;
mod calling_values;
mod captured_transfers;
mod checked_reads;
mod conditional_methods;
mod constant_control;
mod counter_repeat;
mod counter_while;
mod expression_loops;
mod generic_break;
mod generic_counter;
mod generic_lookup;
mod guarded_counter;
mod literal_choices;
mod loops;
mod nested_search;
mod numeric_exit;
mod numeric_repeat;
mod observed_values;
mod opaque;
mod plain;
mod reset_counter;
use plain::PlainExpressions;
mod parameter_writebacks;
mod repeat_lookup;
mod repeat_prefix;
mod returned_calls;
mod scopes;
mod seeded_predicates;
mod stateful_generic;
mod value_expressions;

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
    let mut by_owner = BTreeMap::<_, Vec<_>>::new();
    for requirement in &hir.required_luau_inlining {
        by_owner
            .entry(requirement.owner)
            .or_default()
            .push(requirement);
    }
    let functions = scopes::functions(&module.body);
    let mut validated = BTreeSet::new();
    for (&owner, requirements) in by_owner.iter().rev() {
        if owner == module.entry_function {
            continue;
        }
        let Some(instances) = functions.get(&owner) else {
            return false;
        };
        let [function] = instances.as_slice() else {
            return false;
        };
        if !function.params.is_empty()
            || function.is_vararg
            || !validate_scope(owner, &function.body, requirements, hir, &validated)
            || !scopes::costly(function)
        {
            return false;
        }
        validated.insert(owner);
    }
    // 子函数的成本已证明它保留独立调用帧；入口没有自己的签证时，
    // 不对无关兄弟函数体重复建立内联合同。
    by_owner
        .get(&module.entry_function)
        .is_none_or(|requirements| {
            validate_scope(
                module.entry_function,
                &module.body,
                requirements,
                hir,
                &validated,
            )
        })
}

fn validate_scope(
    owner: crate::hir::HirProtoRef,
    body: &AstBlock,
    requirements: &[&crate::hir::HirRequiredLuauInlining],
    hir: &crate::hir::HirModule,
    validated: &BTreeSet<crate::hir::HirProtoRef>,
) -> bool {
    let statements = scope_statements(body);
    let Some(mut callable_arguments) = calling_values::Dependencies::new(requirements, hir) else {
        return false;
    };
    let opaque_functions = opaque::Functions::new(&statements, hir, owner, validated);
    let mut callees = BTreeMap::new();
    let mut occurrences = BTreeMap::new();
    let mut result_frames = BTreeMap::new();
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
    let expression_loops = bodies.values().any(|body| {
        matches!(
            body,
            HirLuauInliningBody::ValueExpression { .. }
                | HirLuauInliningBody::ParameterWriteback { .. }
                | HirLuauInliningBody::SeededPredicate { .. }
                | HirLuauInliningBody::ConstantControl { .. }
                | HirLuauInliningBody::NumericRepeat { .. }
                | HirLuauInliningBody::GuardedCounter { .. }
                | HirLuauInliningBody::ResetCounter { .. }
                | HirLuauInliningBody::ArrayFold { .. }
                | HirLuauInliningBody::NestedSearch { .. }
                | HirLuauInliningBody::CallingValue { .. }
                | HirLuauInliningBody::CallingSharedValue { .. }
                | HirLuauInliningBody::CallingObservedValue { .. }
                | HirLuauInliningBody::CallingReadPair { .. }
        )
    });
    let numeric_bindings = if expression_loops {
        expression_loops::bindings(body)
    } else {
        BTreeSet::new()
    };
    let mandatory_loops = if expression_loops {
        expression_loops::mandatory_costs(body)
    } else {
        BTreeMap::new()
    };
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
    let written_locals = crate::ast::written_locals(body);
    let mut nonconstant_locals = written_locals
        .union(&numeric_bindings)
        .copied()
        .collect::<BTreeSet<_>>();
    let Some(constant_controls) = constant_control::Models::new(&statements, &bodies, hir) else {
        return false;
    };
    if bodies.values().any(|body| {
        matches!(
            body,
            HirLuauInliningBody::ConstantControl { .. }
                | HirLuauInliningBody::NumericRepeat { .. }
                | HirLuauInliningBody::GuardedCounter { .. }
                | HirLuauInliningBody::ResetCounter { .. }
                | HirLuauInliningBody::ArrayFold { .. }
                | HirLuauInliningBody::NestedSearch { .. }
        )
    }) {
        constant_control::extend_runtime_values(body, &mut nonconstant_locals);
    }
    if bodies
        .values()
        .any(|body| matches!(body, HirLuauInliningBody::ConditionalMethod { .. }))
    {
        // 编译器只会为只读实参复用原槽；后续写入和子闭包写入同样会触发参数 COPY。
        opaque_locals.extend(written_locals.iter().copied());
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
    // getFunctionExpr 追踪 local 初始化但不解析索引结果；只读别名仍保持原 CALL。
    for stmt in &statements {
        if let AstStmt::LocalDecl(decl) = stmt
            && let ([binding], [AstExpr::IndexAccess(_)]) =
                (decl.bindings.as_slice(), decl.values.as_slice())
            && let AstBindingRef::Local(local) = binding.id
            && !written_locals.contains(&local)
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
    let scalar_names = requirements
        .iter()
        .filter(|requirement| matches!(requirement.body, HirLuauInliningBody::ScalarNotCall { .. }))
        .filter_map(|requirement| requirement.field.as_utf8())
        .collect::<BTreeSet<_>>();
    let contracts = requirements
        .iter()
        .map(|r| (r.callee, *r))
        .collect::<BTreeMap<_, _>>();
    for requirement in requirements {
        if matches!(
            requirement.body,
            HirLuauInliningBody::CapturedValue
                | HirLuauInliningBody::CapturedAppendTransfer { .. }
                | HirLuauInliningBody::EventClosureFactory { .. }
                | HirLuauInliningBody::PublishedClosureFactory { .. }
                | HirLuauInliningBody::SnapshotClosureFactory { .. }
                | HirLuauInliningBody::CapturedCallablePair
                | HirLuauInliningBody::ConditionalMethod { .. }
                | HirLuauInliningBody::ValueExpression { .. }
                | HirLuauInliningBody::ParameterWriteback { .. }
                | HirLuauInliningBody::SeededPredicate { .. }
                | HirLuauInliningBody::ConstantControl { .. }
                | HirLuauInliningBody::NumericRepeat { .. }
                | HirLuauInliningBody::GuardedCounter { .. }
                | HirLuauInliningBody::ResetCounter { .. }
                | HirLuauInliningBody::ArrayFold { .. }
                | HirLuauInliningBody::NestedSearch { .. }
                | HirLuauInliningBody::CallingValue { .. }
                | HirLuauInliningBody::CallingSharedValue { .. }
                | HirLuauInliningBody::CallingObservedValue { .. }
                | HirLuauInliningBody::CallingReadPair { .. }
                | HirLuauInliningBody::RepeatPrefix { .. }
                | HirLuauInliningBody::RepeatLookup { .. }
                | HirLuauInliningBody::CounterRepeat { .. }
                | HirLuauInliningBody::GenericLookupWhile { .. }
                | HirLuauInliningBody::GenericCounter { .. }
                | HirLuauInliningBody::CounterWhile { .. }
                | HirLuauInliningBody::StatefulGenericWhile { .. }
                | HirLuauInliningBody::NumericForExit { .. }
                | HirLuauInliningBody::CapturedIncrementIdentity { .. }
                | HirLuauInliningBody::GenericBreak { .. }
        ) && (requirement.result_frames.len() != requirement.occurrences.len()
            || requirement
                .occurrences
                .iter()
                .any(|site| !requirement.result_frames.contains_key(site)))
        {
            return false;
        }
        result_frames.extend(
            requirement
                .result_frames
                .iter()
                .map(|(&site, &frame)| (site, frame)),
        );
        if hir
            .protos
            .get(requirement.child.index())
            .is_none_or(|proto| proto.signature.is_vararg)
            || requirement.owner != owner
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
    let extended_scope = owner != hir.entry
        || !validated.is_empty()
        || requirements.iter().any(|requirement| {
            matches!(
                requirement.body,
                HirLuauInliningBody::CapturedIncrementIdentity { .. }
                    | HirLuauInliningBody::SeededPredicate { .. }
                    | HirLuauInliningBody::ConstantControl { .. }
                    | HirLuauInliningBody::NumericRepeat { .. }
                    | HirLuauInliningBody::GuardedCounter { .. }
                    | HirLuauInliningBody::ResetCounter { .. }
                    | HirLuauInliningBody::ArrayFold { .. }
                    | HirLuauInliningBody::NestedSearch { .. }
                    | HirLuauInliningBody::CallingValue { .. }
                    | HirLuauInliningBody::CallingSharedValue { .. }
                    | HirLuauInliningBody::CallingObservedValue { .. }
                    | HirLuauInliningBody::CallingReadPair { .. }
            )
        });
    macro_rules! condition {
        ($value:expr) => {{
            InvocationExpressions {
                shared_factories: &shared_factories,
                published_globals: &published_globals,
                bodies: &bodies,
                hir,
                result_frames: &result_frames,
                constant_controls: &constant_controls,
                opaque_locals: &opaque_locals,
                runtime_functions: &opaque_functions.runtime,
                written_locals: &written_locals,
                nonconstant_locals: &nonconstant_locals,
                callable_arguments: &callable_arguments,
                callees: &callees,
                occurrences: &occurrences,
                declared: &declared,
                seen: &mut seen_occurrences,
            }
            .condition($value, active, &result_frames, &mut seen_result_slots)
        }};
    }

    let mut pending = body
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
                } else if callable_arguments.contains(local) {
                    callable_arguments.declaration(local, &decl.func, hir, &written_locals)
                } else if let Some(child) = callees.get(&local) {
                    *child == decl.func.function
                        && declared.insert(local)
                        && callee_body(&decl.func, contracts[&local], hir, &opaque_functions, &constant_controls)
                } else {
                    if validated.contains(&decl.func.function) { true }
                    else if opaque_functions.locals.contains(&local) {
                        opaque_functions.validate(&decl.func)
                    } else {
                        PlainExpressions::new(&callees).function(&decl.func)
                    }
                };
                if !valid {
                    return false;
                }
                active += 1;
            }
            AstStmt::LocalDecl(decl) => {
                if decl.values.iter().enumerate().any(|(offset, value)| matches!(value, AstExpr::Call(call) if !captured_transfers::slots(call, active + offset, &occurrences, &bodies, &result_frames, &mut seen_result_slots))) { return false; }
                // 整组 local 的 target 已预留；只允许一对一的 fixed-one 调用。
                if let [AstExpr::Call(call)] = decl.values.as_slice()
                    && let Some(site) = call.required_luau_inlining
                    && let Some(frame) = result_frames.get(&site)
                {
                    // 宏必须作为原固定结果声明发射；不允许移入参数树后复用一个估算的 top。
                    if decl.bindings.len() != frame.width
                        || active != frame.base
                        || !seen_result_slots.insert(site)
                    {
                        return false;
                    }
                }
                if decl.values.len() > 1 {
                    for (offset, value) in decl.values.iter().enumerate() {
                        let value = match value {
                            AstExpr::SingleValue(value) => value.as_ref(),
                            other => other,
                        };
                        if let AstExpr::Call(call) = value
                            && let Some(site) = call.required_luau_inlining
                            && matches!(occurrences.get(&site).and_then(|local| bodies.get(local)),
                                Some(HirLuauInliningBody::GuardedCounter { .. }))
                            && (decl.bindings.len() != decl.values.len()
                                || result_frames.get(&site).map(|frame| frame.base) != Some(active + offset)
                                || !seen_result_slots.insert(site))
                        {
                            return false;
                        }
                    }
                }
                active += decl.bindings.len();
                let mut expression = InvocationExpressions {
                    shared_factories: &shared_factories,
                    published_globals: &published_globals,
                    bodies: &bodies,
                hir,
                result_frames: &result_frames,
                constant_controls: &constant_controls,
                    opaque_locals: &opaque_locals,
                runtime_functions: &opaque_functions.runtime,
                    written_locals: &written_locals,
                nonconstant_locals: &nonconstant_locals,
                    callable_arguments: &callable_arguments,
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
                if decl.values.iter().enumerate().any(|(index, value)| {
                    !expression.check(
                        value,
                        active,
                        index + 1 < decl.values.len() || decl.bindings.len() == decl.values.len(),
                    )
                }) {
                    return false;
                }
            }
            AstStmt::CallStmt(stmt) => {
                let AstCallKind::Call(call) = &stmt.call else {
                    return false;
                };
                if !captured_transfers::slots(call, active, &occurrences, &bodies, &result_frames, &mut seen_result_slots) { return false; }
                if !scopes::captured_value_slots(call, active, &occurrences, &bodies, &result_frames, &mut seen_result_slots) {
                    return false;
                }
                if !literal_choices::comparison_slots(call, active, &occurrences, &bodies, &result_frames, &mut seen_result_slots) {
                    return false;
                }
                for (argument, value) in call.args.iter().enumerate() {
                    let value = match value {
                        AstExpr::SingleValue(value) => value.as_ref(),
                        value => value,
                    };
                    if let AstExpr::Call(inner) = value
                        && let Some(site) = inner.required_luau_inlining
                        && occurrences.get(&site).and_then(|local| bodies.get(local))
                            .is_some_and(|body| matches!(body, HirLuauInliningBody::GenericCounter { .. } | HirLuauInliningBody::SeededPredicate { .. }
                | HirLuauInliningBody::ConstantControl { .. }
                        | HirLuauInliningBody::NumericRepeat { .. } | HirLuauInliningBody::CallingValue { .. } | HirLuauInliningBody::CallingSharedValue { .. }
 | HirLuauInliningBody::CallingObservedValue { .. }))
                        && (result_frames.get(&site).map(|frame| frame.base) != Some(active + 1 + argument)
                            || !seen_result_slots.insert(site))
                    {
                        // 完整观察帧按从左到右的实参槽承接每次展开返回。
                        return false;
                    }
                }
                if let Some(site) = generic_lookup::comparison_result(call)
                    && occurrences.get(&site).and_then(|local| bodies.get(local))
                        .is_some_and(|body| matches!(body, HirLuauInliningBody::GenericLookupWhile { .. }))
                    && (result_frames.get(&site).map(|frame| frame.base) != Some(active + 2)
                        || !seen_result_slots.insert(site)) { return false; }
                if let Some(site) = counter_while::comparison_result(call)
                    && occurrences.get(&site).and_then(|local| bodies.get(local))
                        .is_some_and(|body| matches!(body, HirLuauInliningBody::CounterWhile { .. } | HirLuauInliningBody::NumericRepeat { .. } | HirLuauInliningBody::NestedSearch { .. }))
                    && (result_frames.get(&site).map(|frame| frame.base) != Some(active + 2)
                        || !seen_result_slots.insert(site))
                {
                    // assert 的 callee/Boolean 占前两槽，循环返回值必须留在原比较左输入槽。
                    return false;
                }
                if call.required_luau_inlining.is_some()
                    || !(matches!(&call.callee, AstExpr::Var(AstNameRef::Global(name))
                    if name.text == "assert" || name.text == "print")
                        || matches!(&call.callee, AstExpr::Var(AstNameRef::Local(local)) if opaque_locals.contains(local)))
                    || !call.args.iter().enumerate().all(|(index, arg)| {
                        InvocationExpressions {
                            shared_factories: &shared_factories,
                            published_globals: &published_globals,
                            bodies: &bodies,
                hir,
                result_frames: &result_frames,
                constant_controls: &constant_controls,
                            opaque_locals: &opaque_locals,
                runtime_functions: &opaque_functions.runtime,
                            written_locals: &written_locals,
                nonconstant_locals: &nonconstant_locals,
                            callable_arguments: &callable_arguments,
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
            AstStmt::If(branch) if extended_scope => {
                if !condition!(&branch.cond) { return false; }
                pending.push((None, active));
                if let Some(other) = &branch.else_block {
                    pending.extend(other.stmts.iter().rev().map(|stmt| (Some(stmt), 0)));
                    pending.push((None, active));
                }
                pending.extend(branch.then_block.stmts.iter().rev().map(|stmt| (Some(stmt), 0)));
            }
            AstStmt::Repeat(loop_) if extended_scope => {
                // 候选拒绝[ProofIncomplete]：带顶层正文声明时，尚未发布 until 的活跃前缀。
                if scope_statements(&loop_.body).iter().any(|stmt|
                    matches!(stmt, AstStmt::LocalDecl(_) | AstStmt::LocalFunctionDecl(_)))
                    || !condition!(&loop_.cond) { return false; }
                pending.push((None, active));
                pending.extend(loop_.body.stmts.iter().rev().map(|stmt| (Some(stmt), 0)));
            }
            AstStmt::GenericFor(loop_) if extended_scope
                && matches!(loop_.iterator.as_slice(), [AstExpr::Var(AstNameRef::Local(_))]) => {
                pending.push((None, active));
                active += 3 + loop_.bindings.len();
                pending.extend(loop_.body.stmts.iter().rev().map(|stmt| (Some(stmt), 0)));
            }
            AstStmt::Break | AstStmt::Continue if extended_scope => {}
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
                hir,
                result_frames: &result_frames,
                constant_controls: &constant_controls,
                    opaque_locals: &opaque_locals,
                runtime_functions: &opaque_functions.runtime,
                    written_locals: &written_locals,
                nonconstant_locals: &nonconstant_locals,
                    callable_arguments: &callable_arguments,
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
            AstStmt::NumericFor(loop_) if expression_loops
                && expression_loops::unchanged(loop_, &numeric_bindings, match loop_.binding { AstBindingRef::Local(local) => mandatory_loops.get(&local).copied(), _ => None }) => {
                pending.push((None, active));
                active += 3;
                pending.extend(loop_.body.stmts.iter().rev().map(|stmt| (Some(stmt), 0)));
            }
            AstStmt::NumericFor(loop_) if !expression_loops && loops::unchanged(loop_, &callees) => {}
            AstStmt::GenericFor(loop_)
                if matches!(loop_.iterator.as_slice(), [value @ AstExpr::TableConstructor(_)]
                    if PlainExpressions::new(&callees).expr(value)) => {
                // 表字面量是固定单值；Luau 不展开 generic-for，构造与正文分别核对。
                pending.push((None, active));
                active += 3 + loop_.bindings.len();
                pending.extend(loop_.body.stmts.iter().rev().map(|stmt| (Some(stmt), 0)));
            }
            // pinned Luau 只展开数值循环；迭代器和循环体仍逐项排除额外内联及常量折叠。
            AstStmt::GenericFor(loop_)
                if matches!(loop_.iterator.as_slice(), [AstExpr::Call(call)]
                    if matches!(&call.callee, AstExpr::Var(AstNameRef::Global(name)) if name.text == "ipairs")
                        && call.required_luau_inlining.is_none() && call.method_key.is_none()
                        && matches!(call.args.as_slice(), [argument] if PlainExpressions::new(&callees).expr(argument))) => {
                if PlainExpressions::new(&callees).block(&loop_.body) { continue; }
                pending.push((None, active));
                active += 3 + loop_.bindings.len();
                pending.extend(loop_.body.stmts.iter().rev().map(|stmt| (Some(stmt), 0)));
            }
            AstStmt::FunctionDecl(decl) if PlainExpressions::new(&callees).field_function(decl) => {}
            AstStmt::Return(ret) if ret.values.is_empty()
                || owner != hir.entry && PlainExpressions::new(&callees).values(&ret.values, false) => {}
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
                if result_frames.get(&site).map(|frame| frame.base) != Some(active)
                    || !seen_result_slots.insert(site)
                    || !(InvocationExpressions {
                        shared_factories: &shared_factories,
                        published_globals: &published_globals,
                        bodies: &bodies,
                hir,
                result_frames: &result_frames,
                constant_controls: &constant_controls,
                        opaque_locals: &opaque_locals,
                runtime_functions: &opaque_functions.runtime,
                        written_locals: &written_locals,
                nonconstant_locals: &nonconstant_locals,
                        callable_arguments: &callable_arguments,
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
            AstStmt::Assign(assign) if PlainExpressions::new(&callees).assign(assign)
                || matches!((assign.targets.as_slice(), assign.values.as_slice()),
                    ([AstLValue::Name(AstNameRef::Local(local))], [value])
                    if !callees.contains_key(local)
                        && runtime_arithmetic(value, &|name| matches!(name, AstNameRef::Local(local) if nonconstant_locals.contains(local)).then_some(true)) == Some(true)) => {}
            AstStmt::Assign(assign) if matches!(assign.targets.as_slice(), [AstLValue::Name(AstNameRef::Local(local))] if opaque_locals.contains(local)) => {
                if assign.values.len() != 1
                    || !(InvocationExpressions {
                        shared_factories: &shared_factories,
                        published_globals: &published_globals,
                        bodies: &bodies,
                hir,
                result_frames: &result_frames,
                constant_controls: &constant_controls,
                        opaque_locals: &opaque_locals,
                runtime_functions: &opaque_functions.runtime,
                        written_locals: &written_locals,
                nonconstant_locals: &nonconstant_locals,
                        callable_arguments: &callable_arguments,
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
        && callable_arguments.complete()
        && declared.len() == callees.len()
        && seen_result_slots.len() == result_frames.len()
}

struct InvocationExpressions<'a> {
    published_globals: &'a BTreeSet<&'a str>,
    shared_factories: &'a BTreeSet<crate::hir::LocalId>,
    bodies: &'a BTreeMap<crate::hir::LocalId, HirLuauInliningBody>,
    hir: &'a crate::hir::HirModule,
    result_frames: &'a BTreeMap<crate::hir::HirSourceSite, crate::hir::HirLuauResultFrame>,
    opaque_locals: &'a BTreeSet<crate::hir::LocalId>,
    runtime_functions: &'a BTreeMap<crate::hir::LocalId, usize>,
    written_locals: &'a BTreeSet<crate::hir::LocalId>,
    nonconstant_locals: &'a BTreeSet<crate::hir::LocalId>,
    constant_controls: &'a constant_control::Models,
    callable_arguments: &'a calling_values::Dependencies<'a>,
    callees: &'a BTreeMap<crate::hir::LocalId, crate::hir::HirProtoRef>,
    occurrences: &'a BTreeMap<crate::hir::HirSourceSite, crate::hir::LocalId>,
    declared: &'a BTreeSet<crate::hir::LocalId>,
    seen: &'a mut BTreeSet<crate::hir::HirSourceSite>,
}

impl InvocationExpressions<'_> {
    fn condition(
        &mut self,
        expr: &AstExpr,
        top: usize,
        slots: &BTreeMap<crate::hir::HirSourceSite, crate::hir::HirLuauResultFrame>,
        seen: &mut BTreeSet<crate::hir::HirSourceSite>,
    ) -> bool {
        match expr {
            AstExpr::Call(call) if call.required_luau_inlining.is_some() => {
                let site = call.required_luau_inlining.unwrap();
                matches!(
                    self.occurrences
                        .get(&site)
                        .and_then(|local| self.bodies.get(local)),
                    Some(HirLuauInliningBody::CapturedIncrementIdentity { .. })
                ) && slots.get(&site).map(|frame| frame.base) == Some(top)
                    && seen.insert(site)
                    && self.check(expr, top, true)
            }
            AstExpr::LogicalAnd(value) | AstExpr::LogicalOr(value) => {
                self.condition(&value.lhs, top, slots, seen)
                    && self.condition(&value.rhs, top, slots, seen)
            }
            AstExpr::Unary(value)
                if value.op == AstUnaryOpKind::Not && !value.original_operation =>
            {
                self.condition(&value.expr, top, slots, seen)
            }
            AstExpr::Boolean(_)
            | AstExpr::Nil
            | AstExpr::Integer(_)
            | AstExpr::Number(_)
            | AstExpr::String(_) => false,
            _ => self.check(expr, top, true),
        }
    }

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
        let arguments = match self.bodies.get(callee) {
            Some(HirLuauInliningBody::ArrayFold { .. }) => {
                array_fold::arguments(&call.args)
                    && call.args.iter().all(|arg| self.check(arg, top + 2, true))
            }
            Some(HirLuauInliningBody::CapturedCallablePair) => call.args.is_empty(),
            Some(HirLuauInliningBody::CallingReadPair { .. }) => {
                self.callable_arguments.arguments(call, self.written_locals)
            }
            Some(HirLuauInliningBody::LiteralChoice { .. }) => {
                let parameters = self.hir.protos[self.callees[callee].index()].params.len();
                call.args.len() == parameters
                    && call
                        .args
                        .iter()
                        .all(|arg| self.check(arg, top + parameters + 2, true))
            }
            _ => false,
        };
        arguments
            && self
                .result_frames
                .get(&site)
                .is_some_and(|frame| frame.width == 2)
            && call.args.len() == self.hir.protos[self.callees[callee].index()].params.len()
            && top <= 128
            && self.declared.contains(callee)
            && call.callee == AstExpr::Var(AstNameRef::Local(*callee))
            && call.method_key.is_none()
            && self.seen.insert(site)
    }

    /// 参数准备的编译约束与模板一一对应；通用签名和结果包已由调用入口检查。
    fn arguments(&self, call: &AstCallExpr, callee: crate::hir::LocalId) -> bool {
        use HirLuauInliningBody as Body;
        let args = call.args.as_slice();
        match self.bodies[&callee] {
            Body::Identity => {
                matches!(args, [AstExpr::Number(value)] if value.is_nan())
                    || matches!(args, [AstExpr::Integer(value)] if (-32768..=32767).contains(value))
                    || matches!(args, [AstExpr::Boolean(_)])
            }
            Body::CapturedIncrementIdentity { .. } | Body::ScalarNotCall { .. } => {
                matches!(args, [AstExpr::Boolean(_)])
            }
            Body::NumericForExit { .. } => numeric_exit::arguments(args),
            Body::ValueClosureFactory { .. }
            | Body::SnapshotClosureFactory { .. }
            | Body::NestedValueClosureFactory { .. } => {
                matches!(args, [AstExpr::Integer(value)] if (-32768..=32767).contains(value))
            }
            Body::EventClosureFactory { .. } => matches!(args, [AstExpr::String(_)]),
            Body::ConditionalMethod { .. } => {
                matches!(args, [AstExpr::Var(AstNameRef::Local(local))] if !self.opaque_locals.contains(local))
            }
            Body::ValueExpression { .. } => value_expressions::arguments(args, self.written_locals),
            Body::SeededPredicate { .. } => seeded_predicates::arguments(args, self.written_locals),
            Body::CallingValue { .. }
            | Body::CallingSharedValue { .. }
            | Body::CallingObservedValue { .. } => {
                self.callable_arguments.arguments(call, self.written_locals)
            }
            Body::RepeatPrefix { .. } => args == [AstExpr::Boolean(true), AstExpr::Boolean(true)],
            Body::GenericLookupWhile { .. } => generic_lookup::arguments(args, self.written_locals),
            Body::ResetCounter { .. } => reset_counter::arguments(args),
            Body::CounterRepeat { .. } => counter_repeat::arguments(args),
            Body::NumericRepeat { .. } => numeric_repeat::arguments(args, self.nonconstant_locals),
            Body::NestedSearch { .. } => nested_search::arguments(args, self.written_locals),
            Body::GuardedCounter { .. } => guarded_counter::arguments(args),
            Body::ConstantControl { .. } => self.constant_controls.inlined(callee, args),
            Body::GenericCounter { .. } => generic_counter::arguments(args),
            Body::CounterWhile { .. } => counter_while::inlined_arguments(args),
            Body::StatefulGenericWhile { .. } => {
                stateful_generic::inlined_arguments(args, self.written_locals)
            }
            Body::RepeatLookup { .. } => {
                matches!(args, [AstExpr::Boolean(true), AstExpr::TableConstructor(_)])
            }
            // 候选拒绝[TargetConstraint]：这些恢复使用固定双结果声明，由 pair 核对完整参数和预留槽。
            Body::CapturedCallablePair | Body::CallingReadPair { .. } | Body::ArrayFold { .. } => {
                false
            }
            Body::CapturedValue
            | Body::CapturedAppendTransfer { .. }
            | Body::CapturedConcatSum
            | Body::CapturedAddIdentity
            | Body::LiteralChoice { .. }
            | Body::ParameterWriteback { .. }
            | Body::GenericBreak { .. }
            | Body::TableFactory { .. }
            | Body::PublishedTableFactory { .. }
            | Body::ClosureFactory { .. }
            | Body::PublishedClosureFactory { .. }
            | Body::UnpackedTable
            | Body::FrozenTableIndex => true,
        }
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
                    && call.args.len() == self.hir.protos[self.callees[callee].index()].params.len()
                    // 结果包的 fixed 宽度由 HIR 帧计划签发；单结果语境不能截断双结果合同。
                    && self.result_frames.get(&site).is_none_or(|frame| frame.width == 1)
                    && self.arguments(call, *callee)
                    && call.args.iter().enumerate().all(|(index, arg)| {
                        PlainExpressions::new(self.callees).expr(arg)
                            || self.callable_arguments.inline_argument(call, index)
                    })
                    && self.seen.insert(site)
            }
            AstExpr::Call(call)
                if !fixed_one
                    && matches!(call.callee, AstExpr::Var(AstNameRef::Local(local))
                        if self.callees.contains_key(&local) && self.declared.contains(&local)) =>
            {
                // pinned Luau 的 multRet 调用始终拒绝内联；不推断其返回宽度。
                // 原普通 CALL 的每个实参仍须核对，只有最后一项可保持开放返回。
                call.method_key.is_none()
                    && call.args.iter().enumerate().all(|(index, arg)| {
                        self.check(arg, top + 1 + call.args.len(), index + 1 < call.args.len())
                    })
            }
            AstExpr::Call(call)
                if matches!(&call.callee,
                AstExpr::Var(AstNameRef::Global(name)) if name.text == "select") =>
            {
                // 原固定参数中的展开结果由 AST 保留单值括号；select 的计数
                // 调用不参与额外内联，内部 occurrence 仍须通过同一编译合同。
                fixed_one && PlainExpressions::new(self.callees).expr(expr)
                    || call.method_key.is_none()
                        && matches!(call.args.as_slice(), [AstExpr::String(marker), AstExpr::SingleValue(value)]
                        if marker.as_utf8() == Some("#")
                            && matches!(value.as_ref(), AstExpr::Call(inner) if inner.required_luau_inlining.is_some()))
                        && self.check(&call.args[1], top + 3, true)
                    || fixed_one
                        && call.method_key.is_none()
                        && matches!(call.args.as_slice(), [AstExpr::String(marker), AstExpr::Call(inner)]
                            if marker.as_utf8() == Some("#") && inner.required_luau_inlining.is_none())
                        && self.check(&call.args[1], top + 3, false)
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
            AstExpr::Binary(_) | AstExpr::Call(_)
                if runtime_arithmetic(expr, &|name| {
                    matches!(name, AstNameRef::Local(local) if self.nonconstant_locals.contains(local)).then_some(true)
                }) == Some(true) =>
            {
                true
            }
            AstExpr::SingleValue(value) => self.check(value, top, true),
            AstExpr::Call(call) if matches!(call.callee, AstExpr::Var(AstNameRef::Local(local)) if self.shared_factories.contains(&local) && self.declared.contains(&local)) => {
                fixed_one && top <= 128 && call.method_key.is_none() && call.args.is_empty()
            }
            AstExpr::Call(call)
                if matches!(call.callee, AstExpr::Var(AstNameRef::Local(local))
                if matches!(self.bodies.get(&local), Some(HirLuauInliningBody::CounterWhile { .. })) && self.declared.contains(&local)) =>
            {
                call.method_key.is_none() && counter_while::retained_arguments(&call.args)
            }
            AstExpr::Call(call)
                if matches!(call.callee, AstExpr::Var(AstNameRef::Local(local))
                if matches!(self.bodies.get(&local), Some(HirLuauInliningBody::GenericCounter { .. })) && self.declared.contains(&local)) =>
            {
                call.method_key.is_none()
                    && generic_counter::retained_arguments(&call.args)
                    && call
                        .args
                        .iter()
                        .all(|arg| PlainExpressions::new(self.callees).expr(arg))
            }
            AstExpr::Call(call)
                if matches!(call.callee, AstExpr::Var(AstNameRef::Local(local))
                if matches!(self.bodies.get(&local), Some(HirLuauInliningBody::RepeatPrefix { .. })) && self.declared.contains(&local)) =>
            {
                call.method_key.is_none() && repeat_prefix::retained_arguments(&call.args)
            }
            AstExpr::Call(call) if matches!(call.callee, AstExpr::Var(AstNameRef::Local(local)) if matches!(self.bodies.get(&local), Some(HirLuauInliningBody::ConstantControl { .. })) && self.declared.contains(&local)) =>
            {
                let AstExpr::Var(AstNameRef::Local(local)) = call.callee else {
                    unreachable!()
                };
                call.method_key.is_none()
                    && self
                        .constant_controls
                        .retained(local, &call.args, self.nonconstant_locals)
                    && call
                        .args
                        .iter()
                        .all(|arg| PlainExpressions::new(self.callees).expr(arg))
            }
            AstExpr::Call(call)
                if matches!(call.callee, AstExpr::Var(AstNameRef::Local(local))
                if matches!(self.bodies.get(&local), Some(HirLuauInliningBody::NumericRepeat { .. })) && self.declared.contains(&local)) =>
            {
                call.method_key.is_none()
                    && numeric_repeat::retained(&call.args, self.nonconstant_locals)
                    && call
                        .args
                        .iter()
                        .all(|arg| PlainExpressions::new(self.callees).expr(arg))
            }
            AstExpr::Call(call)
                if matches!(call.callee, AstExpr::Var(AstNameRef::Local(local))
                if matches!(self.bodies.get(&local), Some(HirLuauInliningBody::GuardedCounter { .. })) && self.declared.contains(&local)) =>
            {
                call.method_key.is_none()
                    && guarded_counter::retained(&call.args, self.nonconstant_locals)
                    && call
                        .args
                        .iter()
                        .all(|arg| PlainExpressions::new(self.callees).expr(arg))
            }
            AstExpr::Call(call) if matches!(call.callee, AstExpr::Var(AstNameRef::Local(local)) if self.runtime_functions.contains_key(&local)) =>
            {
                let AstExpr::Var(AstNameRef::Local(local)) = call.callee else {
                    unreachable!()
                };
                call.required_luau_inlining.is_none() && call.method_key.is_none()
                    && call.args.len() == self.runtime_functions[&local]
                    && call.args.iter().all(|arg| matches!(arg,
                        AstExpr::Var(AstNameRef::Local(local)) if self.nonconstant_locals.contains(local)))
            }
            AstExpr::Call(call) if matches!(call.callee, AstExpr::Var(AstNameRef::Local(local)) if self.opaque_locals.contains(&local)) => {
                call.method_key.is_none()
                    && call.args.iter().enumerate().all(|(index, arg)| {
                        self.check(arg, top + 1 + call.args.len(), index + 1 < call.args.len())
                    })
            }
            AstExpr::MethodCall(call) => {
                PlainExpressions::new(self.callees).expr(&call.receiver)
                    && call.args.iter().enumerate().all(|(index, arg)| {
                        self.check(arg, top + 2 + call.args.len(), index + 1 < call.args.len())
                    })
            }
            _ => {
                PlainExpressions::new(self.callees).expr(expr)
                    && (fixed_one || open_tail_unchanged(expr))
            }
        }
    }
}

/// 先消费前层发布的完整签名，再选择该函数体的编译证明；新增模板必须显式分派。
fn callee_body(
    func: &AstFunctionExpr,
    requirement: &crate::hir::HirRequiredLuauInlining,
    hir: &crate::hir::HirModule,
    opaque_functions: &opaque::Functions<'_>,
    constant_controls: &constant_control::Models,
) -> bool {
    let Some(proto) = hir.protos.get(requirement.child.index()) else {
        return false;
    };
    if func.function != requirement.child
        || func.params != proto.params
        || func.is_vararg
        || func.named_vararg.is_some()
    {
        return false;
    }
    // 原闭包没有 upvalue 时，后层不能为它引入捕获；有捕获的合同仍在对应体证明中核对身份。
    if proto.upvalues.is_empty()
        && (!func.captured_bindings.is_empty()
            || !func.captured_params.is_empty()
            || !func.capture_write_names.is_empty())
    {
        return false;
    }
    let body = requirement.body;
    let expected_field = &requirement.field;
    let capture = requirement.capture;
    use HirLuauInliningBody as Body;
    match body {
        Body::CapturedCallablePair => {
            return returned_calls::body(func, expected_field, opaque_functions);
        }
        Body::NumericForExit { template } => {
            return hir
                .protos
                .get(template)
                .is_some_and(|proto| numeric_exit::body(func, proto, capture));
        }
        Body::ConstantControl { .. } => return constant_controls.declaration(requirement.callee),
        Body::CapturedAppendTransfer { template } => {
            return hir
                .protos
                .get(template)
                .zip(opaque_functions.capture_layout(func.function))
                .is_some_and(|(proto, closure)| captured_transfers::body(func, proto, closure));
        }
        Body::CallingValue { template }
        | Body::CallingSharedValue { template }
        | Body::CallingObservedValue { template }
        | Body::CallingReadPair { template } => {
            return hir
                .protos
                .get(template)
                .is_some_and(|proto| calling_values::body(func, proto));
        }
        Body::SeededPredicate { template } => return seeded_predicates::body(func, template),
        Body::ValueExpression { template } => {
            return value_expressions::body(func, template, proto.params.len());
        }
        Body::LiteralChoice { template } => {
            return literal_choices::body(func, template, proto.params.len());
        }
        Body::StatefulGenericWhile {
            template,
            initial,
            increment,
        } => return stateful_generic::body(func, template, initial, increment, expected_field),
        Body::GenericLookupWhile { template, key } => {
            return generic_lookup::body(func, template, key, expected_field);
        }
        Body::GenericCounter {
            template,
            initial,
            increment,
            repeats,
        } => return generic_counter::body(func, template, initial, increment, repeats),
        Body::CounterRepeat {
            template,
            initial,
            increment,
            limit,
        } => return counter_repeat::body(func, template, initial, increment, limit),
        Body::CounterWhile {
            template,
            initial,
            increment,
            limit,
        } => return counter_while::body(func, template, initial, increment, limit),
        Body::GenericBreak {
            template, initial, ..
        } => return generic_break::body(func, template, initial),
        Body::RepeatLookup {
            template,
            key,
            result,
        } => return repeat_lookup::body(func, template, key, result),
        Body::RepeatPrefix { template } => return repeat_prefix::body(func, template),
        Body::ConditionalMethod { template } => return conditional_methods::body(func, template),
        Body::SnapshotClosureFactory { template } => {
            return snapshot_closure_factory(func, template);
        }
        Body::PublishedTableFactory { key } => return published_table_factory(func, key, capture),
        Body::PublishedClosureFactory {
            intermediate,
            leaf,
            result,
        } => return published_closure_factory(func, expected_field, intermediate, leaf, result),
        Body::EventClosureFactory {
            intermediate,
            result,
        } => return event_closure_factory(func, expected_field, intermediate, result),
        Body::ValueClosureFactory { template } => {
            return value_closure_factory_body(func, template);
        }
        Body::NestedValueClosureFactory {
            intermediate,
            result,
        } => return nested_value_closure_factory_body(func, intermediate, result),
        Body::CapturedIncrementIdentity { increment } => {
            return scopes::increment_identity(func, capture, increment);
        }
        Body::CapturedAddIdentity => return captured_identity_body(func, capture),
        Body::TableFactory { shared } => return table_factory_body(func, shared, expected_field),
        Body::ClosureFactory { shared } => return closure_factory_body(func, shared, capture),
        Body::CapturedConcatSum => return captured_concat_body(func, expected_field, capture),
        Body::ResetCounter { template } => {
            return hir
                .protos
                .get(template)
                .is_some_and(|proto| reset_counter::body(func, proto));
        }
        Body::NestedSearch { template } => {
            return hir
                .protos
                .get(template)
                .is_some_and(|proto| nested_search::body(func, proto));
        }
        Body::ArrayFold { template } => {
            return hir
                .protos
                .get(template)
                .is_some_and(|proto| array_fold::body(func, proto));
        }
        Body::GuardedCounter { template } => {
            return hir
                .protos
                .get(template)
                .is_some_and(|proto| guarded_counter::body(func, proto));
        }
        Body::NumericRepeat { template } => {
            return hir
                .protos
                .get(template)
                .is_some_and(|proto| numeric_repeat::body(func, proto));
        }
        Body::ParameterWriteback { template } => {
            return hir
                .protos
                .get(template)
                .is_some_and(|proto| parameter_writebacks::body(func, proto));
        }
        Body::CapturedValue => {
            let Some(capture) = capture else {
                return false;
            };
            return func.params.is_empty()
                && func.captured_bindings == BTreeSet::from([AstBindingRef::Local(capture)])
                && func.captured_params.is_empty()
                && func.capture_write_names.is_empty()
                && matches!(func.body.stmts.as_slice(), [AstStmt::Return(ret)]
                    if ret.values == [AstExpr::Var(AstNameRef::Upvalue(crate::hir::UpvalueId(0)))]);
        }
        Body::Identity
        | Body::UnpackedTable
        | Body::FrozenTableIndex
        | Body::ScalarNotCall { .. } => {}
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
                && PlainExpressions::new(&BTreeMap::new()).values(&call.args, false))))
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

fn opaque_callee(call: &AstCallExpr) -> bool {
    // pinned Luau 不把这几个库调用识别为 builtin；索引调用也不参与 getFunctionExpr。
    ["pack", "freeze", "isfrozen", "concat"]
        .iter()
        .any(|name| table_callee(call, name))
        || matches!(&call.callee, AstExpr::Var(AstNameRef::Global(name)) if matches!(name.text.as_str(), "next" | "collectgarbage" | "pcall" | "error"))
        || matches!(&call.callee, AstExpr::IndexAccess(_))
}

fn open_tail_unchanged(expr: &AstExpr) -> bool {
    // O2 的已知单返回 builtin 会把 open 尾部压为一个值；外围不能借 pragma 改变它。
    !matches!(expr, AstExpr::Call(call) if !opaque_callee(call))
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
                && PlainExpressions::new(&BTreeMap::new()).function(child)
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

// 每个运算节点都必须含有不能被常量传播的输入；不能用整棵表达式含 local 掩盖内部纯常量子树。
fn runtime_arithmetic(
    expr: &AstExpr,
    nonconstant: &impl Fn(&AstNameRef) -> Option<bool>,
) -> Option<bool> {
    match expr {
        AstExpr::Integer(_) | AstExpr::Number(_) => Some(false),
        AstExpr::Var(name) => nonconstant(name),
        AstExpr::Call(call)
            if call.required_luau_inlining.is_none()
                && call.method_key.is_none()
                && matches!(&call.callee, AstExpr::FieldAccess(field)
                    if field.field == "floor" && matches!(&field.base,
                        AstExpr::Var(AstNameRef::Global(name)) if name.text == "math")) =>
        {
            let [argument] = call.args.as_slice() else {
                return None;
            };
            // 只有参数依赖不展开循环或显式写入时才保留动态调用，
            // 不能把 math.floor 的常量实参误作阻止 O2 折叠的证据。
            (runtime_arithmetic(argument, nonconstant) == Some(true)).then_some(true)
        }
        AstExpr::Binary(binary)
            if matches!(
                binary.op,
                AstBinaryOpKind::Add
                    | AstBinaryOpKind::Sub
                    | AstBinaryOpKind::Mul
                    | AstBinaryOpKind::Div
                    | AstBinaryOpKind::Mod
            ) =>
        {
            let left = runtime_arithmetic(&binary.lhs, nonconstant)?;
            let right = runtime_arithmetic(&binary.rhs, nonconstant)?;
            (left || right).then_some(true)
        }
        _ => None,
    }
}
