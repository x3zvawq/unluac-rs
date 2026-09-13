//! 词法 child-first 闭包效果摘要：把 child upvalue 的写入、逃逸、返回与调用投影到父级。
//!
//! capture 直接查询当前 binding 状态；嵌套返回 closure 的效果仍逐层投影到父域。
//! 消费显式 capture 对应和共享 HIR CFG；例如 factory 返回读取 u0 的 closure，
//! 调用方获得对应 capture 效果，不靠函数文本或参数位置猜测。对象存活由父模块消费摘要。
//! 并行赋值只暂存本次 RHS 与索引目标的投影，统一读取写入前状态；例如 a,b=b,a
//! 交换来源后再提交，不复制无关 binding 或已经累积的效果。合流直接记录集合增长。

use crate::hir::HirBinding;

use super::super::lexical_cfg::{
    FlowRefinement, HirFlowNodeKind, HirFlowProtocolId, HirForBindings, HirGenericForFlow,
};
use super::{
    ClosureCaptures, EffectClosure, EffectValue, ProtoEffects, ProtoFlowFacts, extend_map_sets,
    union_set,
};
use crate::hir::common::{
    HirCapture, HirCaptureMode, HirExpr, HirLValue, HirProto, HirProtoRef, HirStmt, HirTableField,
    HirValuePack, UpvalueId,
};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Default, Eq, PartialEq)]
struct EffectState {
    origins: BTreeMap<HirBinding, BTreeSet<UpvalueId>>,
    closures: BTreeMap<HirBinding, BTreeSet<EffectClosure>>,
    call_targets: BTreeMap<HirBinding, BTreeSet<UpvalueId>>,
    escapes: BTreeSet<UpvalueId>,
    returns: BTreeSet<EffectValue>,
    calls: BTreeSet<UpvalueId>,
    generic_for: BTreeMap<HirFlowProtocolId, GenericForEffectSnapshot>,
}

#[derive(Clone, Default, Eq, PartialEq)]
struct GenericForEffectSnapshot {
    callees: BTreeSet<EffectClosure>,
    call_targets: BTreeSet<UpvalueId>,
    argument_origins: BTreeSet<UpvalueId>,
    result_origins: BTreeSet<UpvalueId>,
    result_closures: BTreeSet<EffectClosure>,
    result_call_targets: BTreeSet<UpvalueId>,
}

impl EffectState {
    fn new(proto: &HirProto) -> Self {
        let origins = proto
            .upvalues
            .iter()
            .copied()
            .map(|upvalue| (HirBinding::Upvalue(upvalue), BTreeSet::from([upvalue])))
            .collect();
        let call_targets = proto
            .upvalues
            .iter()
            .copied()
            .map(|upvalue| (HirBinding::Upvalue(upvalue), BTreeSet::from([upvalue])))
            .collect();
        Self {
            origins,
            call_targets,
            ..Self::default()
        }
    }

    // 缺失 binding 与空集合都是 bottom；只保留有 capture 来源的值，避免所有临时值
    // 都成为每个 CFG 节点必须复制的空状态。覆盖仍需移除旧来源，不能只忽略空写入。
    fn write_binding(
        &mut self,
        binding: HirBinding,
        origins: BTreeSet<UpvalueId>,
        closures: BTreeSet<EffectClosure>,
        call_targets: BTreeSet<UpvalueId>,
    ) {
        fn replace<V>(
            map: &mut BTreeMap<HirBinding, BTreeSet<V>>,
            binding: HirBinding,
            values: BTreeSet<V>,
        ) {
            if values.is_empty() {
                map.remove(&binding);
            } else {
                map.insert(binding, values);
            }
        }
        replace(&mut self.origins, binding, origins);
        replace(&mut self.closures, binding, closures);
        replace(&mut self.call_targets, binding, call_targets);
    }

    fn join(&mut self, other: &Self) -> bool {
        let mut changed = extend_map_sets(&mut self.origins, &other.origins);
        changed |= extend_map_sets(&mut self.closures, &other.closures);
        changed |= extend_map_sets(&mut self.call_targets, &other.call_targets);
        changed |= union_set(&mut self.escapes, &other.escapes);
        changed |= union_set(&mut self.returns, &other.returns);
        changed |= union_set(&mut self.calls, &other.calls);
        let protocol_count = self.generic_for.len();
        for (&protocol, snapshot) in &other.generic_for {
            let current = self.generic_for.entry(protocol).or_default();
            changed |= union_set(&mut current.callees, &snapshot.callees);
            changed |= union_set(&mut current.call_targets, &snapshot.call_targets);
            changed |= union_set(&mut current.argument_origins, &snapshot.argument_origins);
            changed |= union_set(&mut current.result_origins, &snapshot.result_origins);
            changed |= union_set(&mut current.result_closures, &snapshot.result_closures);
            changed |= union_set(
                &mut current.result_call_targets,
                &snapshot.result_call_targets,
            );
        }
        changed || protocol_count != self.generic_for.len()
    }
}

struct EffectContext<'a> {
    captures: &'a ClosureCaptures<'a>,
    effects: &'a [ProtoEffects],
}

fn effect_expr_origins(
    expr: &HirExpr,
    state: &EffectState,
    context: &EffectContext<'_>,
) -> BTreeSet<UpvalueId> {
    if let Some(binding) = HirBinding::from_expr(expr) {
        return state.origins.get(&binding).cloned().unwrap_or_default();
    }
    let mut origins = BTreeSet::new();
    match expr {
        HirExpr::TableAccess(access) => {
            origins.extend(effect_expr_origins(&access.base, state, context));
            origins.extend(effect_expr_origins(&access.key, state, context));
        }
        HirExpr::Unary(unary) => {
            origins.extend(effect_expr_origins(&unary.expr, state, context));
        }
        HirExpr::Binary(binary) => {
            origins.extend(effect_expr_origins(&binary.lhs, state, context));
            origins.extend(effect_expr_origins(&binary.rhs, state, context));
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            origins.extend(effect_expr_origins(&logical.lhs, state, context));
            origins.extend(effect_expr_origins(&logical.rhs, state, context));
        }
        HirExpr::Decision(decision) => {
            for node in &decision.nodes {
                origins.extend(effect_expr_origins(&node.test, state, context));
                if let crate::hir::common::HirDecisionTarget::Expr(expr) = &node.truthy {
                    origins.extend(effect_expr_origins(expr, state, context));
                }
                if let crate::hir::common::HirDecisionTarget::Expr(expr) = &node.falsy {
                    origins.extend(effect_expr_origins(expr, state, context));
                }
            }
        }
        HirExpr::Call(call) => {
            origins.extend(effect_expr_origins(&call.callee, state, context));
            for closure in effect_expr_closures(&call.callee, state, context) {
                for value in &closure.returns {
                    origins.extend(effect_value_origins(value));
                }
            }
        }
        HirExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    HirTableField::Array(value) => {
                        origins.extend(effect_expr_origins(value, state, context));
                    }
                    HirTableField::Record(record) => {
                        origins.extend(effect_expr_origins(&record.key, state, context));
                        origins.extend(effect_expr_origins(&record.value, state, context));
                    }
                }
            }
            if let Some(tail) = &table.trailing_multivalue {
                origins.extend(effect_expr_origins(tail.as_expr(), state, context));
            }
        }
        HirExpr::Closure(closure) => {
            for capture in &closure.captures {
                origins.extend(state.origins.get(&capture.binding).into_iter().flatten());
            }
        }
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
        | HirExpr::Vector(_)
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::CaptureInitializer(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => {}
    }
    origins
}

fn effect_value_origins(value: &EffectValue) -> BTreeSet<UpvalueId> {
    match value {
        EffectValue::Upvalue(upvalue) => BTreeSet::from([*upvalue]),
        EffectValue::Closure(closure) => closure.captures.clone(),
    }
}

fn effect_expr_closures(
    expr: &HirExpr,
    state: &EffectState,
    context: &EffectContext<'_>,
) -> BTreeSet<EffectClosure> {
    if let Some(binding) = HirBinding::from_expr(expr) {
        return state.closures.get(&binding).cloned().unwrap_or_default();
    }
    match expr {
        HirExpr::Closure(closure) => project_direct_closure(closure.proto, state, context)
            .into_iter()
            .collect(),
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            let mut closures = effect_expr_closures(&logical.lhs, state, context);
            closures.extend(effect_expr_closures(&logical.rhs, state, context));
            closures
        }
        HirExpr::Decision(decision) => {
            let mut closures = BTreeSet::new();
            for node in &decision.nodes {
                if let crate::hir::common::HirDecisionTarget::Expr(expr) = &node.truthy {
                    closures.extend(effect_expr_closures(expr, state, context));
                }
                if let crate::hir::common::HirDecisionTarget::Expr(expr) = &node.falsy {
                    closures.extend(effect_expr_closures(expr, state, context));
                }
            }
            closures
        }
        HirExpr::Call(call) => {
            let mut closures = BTreeSet::new();
            for callee in effect_expr_closures(&call.callee, state, context) {
                for value in callee.returns {
                    if let EffectValue::Closure(closure) = value {
                        closures.insert(*closure);
                    }
                }
            }
            closures
        }
        _ => BTreeSet::new(),
    }
}

fn project_direct_closure(
    proto: HirProtoRef,
    state: &EffectState,
    context: &EffectContext<'_>,
) -> Option<EffectClosure> {
    let effect = &context.effects[proto.index()];
    let captures = context.captures.get(&proto)?;
    Some(project_proto_effect(proto, effect, captures, state))
}

fn project_proto_effect(
    proto: HirProtoRef,
    effect: &ProtoEffects,
    captures: &[HirCapture],
    state: &EffectState,
) -> EffectClosure {
    let captured = captures
        .iter()
        .filter_map(|capture| state.origins.get(&capture.binding))
        .flatten()
        .copied()
        .collect();
    let writes = project_written_upvalues(&effect.writes, captures, state);
    let escapes = project_origin_upvalues(&effect.escapes, captures, state);
    let returns = project_return_values(&effect.returns, captures, state);
    let (mut call_escapes, calls) = project_called_upvalues(&effect.calls, captures, state);
    call_escapes.extend(escapes);
    EffectClosure {
        proto,
        captures: captured,
        writes,
        escapes: call_escapes,
        returns,
        calls,
    }
}

fn project_nested_closure(
    closure: &EffectClosure,
    captures: &[HirCapture],
    state: &EffectState,
) -> EffectClosure {
    let captured = project_origin_upvalues(&closure.captures, captures, state);
    let writes = project_written_upvalues(&closure.writes, captures, state);
    let escapes = project_origin_upvalues(&closure.escapes, captures, state);
    let returns = project_return_values(&closure.returns, captures, state);
    let (mut call_escapes, calls) = project_called_upvalues(&closure.calls, captures, state);
    call_escapes.extend(escapes);
    EffectClosure {
        proto: closure.proto,
        captures: captured,
        writes,
        escapes: call_escapes,
        returns,
        calls,
    }
}

fn project_origin_upvalues(
    upvalues: &BTreeSet<UpvalueId>,
    captures: &[HirCapture],
    state: &EffectState,
) -> BTreeSet<UpvalueId> {
    upvalues
        .iter()
        .filter_map(|upvalue| captures.get(upvalue.index()))
        .filter_map(|capture| state.origins.get(&capture.binding))
        .flatten()
        .copied()
        .collect()
}

fn project_written_upvalues(
    upvalues: &BTreeSet<UpvalueId>,
    captures: &[HirCapture],
    state: &EffectState,
) -> BTreeSet<UpvalueId> {
    upvalues
        .iter()
        .filter_map(|upvalue| captures.get(upvalue.index()))
        .filter(|capture| capture.mode == HirCaptureMode::ByReference)
        .filter_map(|capture| state.origins.get(&capture.binding))
        .flatten()
        .copied()
        .collect()
}

fn project_return_values(
    values: &BTreeSet<EffectValue>,
    captures: &[HirCapture],
    state: &EffectState,
) -> BTreeSet<EffectValue> {
    let mut projected = BTreeSet::new();
    for value in values {
        match value {
            EffectValue::Upvalue(upvalue) => {
                let Some(capture) = captures.get(upvalue.index()) else {
                    continue;
                };
                projected.extend(
                    state
                        .origins
                        .get(&capture.binding)
                        .into_iter()
                        .flatten()
                        .copied()
                        .map(EffectValue::Upvalue),
                );
                projected.extend(
                    state
                        .closures
                        .get(&capture.binding)
                        .into_iter()
                        .flatten()
                        .cloned()
                        .map(|closure| EffectValue::Closure(Box::new(closure))),
                );
            }
            EffectValue::Closure(closure) => {
                projected.insert(EffectValue::Closure(Box::new(project_nested_closure(
                    closure, captures, state,
                ))));
            }
        }
    }
    projected
}

fn project_called_upvalues(
    upvalues: &BTreeSet<UpvalueId>,
    captures: &[HirCapture],
    state: &EffectState,
) -> (BTreeSet<UpvalueId>, BTreeSet<UpvalueId>) {
    let mut escapes = BTreeSet::new();
    let mut calls = BTreeSet::new();
    for upvalue in upvalues {
        let Some(capture) = captures.get(upvalue.index()) else {
            continue;
        };
        calls.extend(
            state
                .call_targets
                .get(&capture.binding)
                .into_iter()
                .flatten(),
        );
        for closure in state.closures.get(&capture.binding).into_iter().flatten() {
            escapes.extend(&closure.escapes);
            calls.extend(&closure.calls);
        }
    }
    (escapes, calls)
}

fn effect_expr_call_targets(
    expr: &HirExpr,
    state: &EffectState,
    context: &EffectContext<'_>,
) -> BTreeSet<UpvalueId> {
    if let Some(binding) = HirBinding::from_expr(expr) {
        return state
            .call_targets
            .get(&binding)
            .cloned()
            .unwrap_or_default();
    }
    match expr {
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            let mut targets = effect_expr_call_targets(&logical.lhs, state, context);
            targets.extend(effect_expr_call_targets(&logical.rhs, state, context));
            targets
        }
        HirExpr::Decision(decision) => {
            let mut targets = BTreeSet::new();
            for node in &decision.nodes {
                if let crate::hir::common::HirDecisionTarget::Expr(expr) = &node.truthy {
                    targets.extend(effect_expr_call_targets(expr, state, context));
                }
                if let crate::hir::common::HirDecisionTarget::Expr(expr) = &node.falsy {
                    targets.extend(effect_expr_call_targets(expr, state, context));
                }
            }
            targets
        }
        HirExpr::Call(call) => {
            let mut targets = BTreeSet::new();
            for closure in effect_expr_closures(&call.callee, state, context) {
                for value in closure.returns {
                    if let EffectValue::Upvalue(upvalue) = value {
                        targets.insert(upvalue);
                    }
                }
            }
            targets
        }
        _ => BTreeSet::new(),
    }
}

fn project_known_call_effects(
    closure: &EffectClosure,
    escapes: &mut BTreeSet<UpvalueId>,
    calls: &mut BTreeSet<UpvalueId>,
) {
    escapes.extend(&closure.escapes);
    calls.extend(&closure.calls);
}

fn effect_note_expr_escapes(
    expr: &HirExpr,
    state: &EffectState,
    context: &EffectContext<'_>,
    escapes: &mut BTreeSet<UpvalueId>,
    calls: &mut BTreeSet<UpvalueId>,
) {
    match expr {
        HirExpr::Call(call) => {
            calls.extend(effect_expr_call_targets(&call.callee, state, context));
            for arg in &call.args {
                escapes.extend(effect_expr_origins(arg, state, context));
                effect_note_expr_escapes(arg, state, context, escapes, calls);
            }
            for closure in effect_expr_closures(&call.callee, state, context) {
                project_known_call_effects(&closure, escapes, calls);
            }
            effect_note_expr_escapes(&call.callee, state, context, escapes, calls);
        }
        HirExpr::TableAccess(access) => {
            effect_note_expr_escapes(&access.base, state, context, escapes, calls);
            effect_note_expr_escapes(&access.key, state, context, escapes, calls);
        }
        HirExpr::Unary(unary) => {
            effect_note_expr_escapes(&unary.expr, state, context, escapes, calls);
        }
        HirExpr::Binary(binary) => {
            effect_note_expr_escapes(&binary.lhs, state, context, escapes, calls);
            effect_note_expr_escapes(&binary.rhs, state, context, escapes, calls);
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            effect_note_expr_escapes(&logical.lhs, state, context, escapes, calls);
            effect_note_expr_escapes(&logical.rhs, state, context, escapes, calls);
        }
        HirExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    HirTableField::Array(value) => {
                        effect_note_expr_escapes(value, state, context, escapes, calls);
                    }
                    HirTableField::Record(record) => {
                        effect_note_expr_escapes(&record.key, state, context, escapes, calls);
                        effect_note_expr_escapes(&record.value, state, context, escapes, calls);
                    }
                }
            }
            if let Some(tail) = &table.trailing_multivalue {
                effect_note_expr_escapes(tail.as_expr(), state, context, escapes, calls);
            }
        }
        HirExpr::Decision(decision) => {
            for node in &decision.nodes {
                effect_note_expr_escapes(&node.test, state, context, escapes, calls);
                if let crate::hir::common::HirDecisionTarget::Expr(expr) = &node.truthy {
                    effect_note_expr_escapes(expr, state, context, escapes, calls);
                }
                if let crate::hir::common::HirDecisionTarget::Expr(expr) = &node.falsy {
                    effect_note_expr_escapes(expr, state, context, escapes, calls);
                }
            }
        }
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
        | HirExpr::Vector(_)
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::Closure(_)
        | HirExpr::CaptureInitializer(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => {}
    }
}

fn scan_effect_pack(
    pack: &HirValuePack,
    state: &EffectState,
    context: &EffectContext<'_>,
    escapes: &mut BTreeSet<UpvalueId>,
    calls: &mut BTreeSet<UpvalueId>,
) {
    for value in pack {
        effect_note_expr_escapes(value, state, context, escapes, calls);
    }
}

fn note_effect_escapes(expr: &HirExpr, state: &mut EffectState, context: &EffectContext<'_>) {
    let mut escapes = BTreeSet::new();
    let mut calls = BTreeSet::new();
    effect_note_expr_escapes(expr, state, context, &mut escapes, &mut calls);
    state.escapes.extend(escapes);
    state.calls.extend(calls);
}

fn note_effect_pack_escapes(
    pack: &HirValuePack,
    state: &mut EffectState,
    context: &EffectContext<'_>,
) {
    let mut escapes = BTreeSet::new();
    let mut calls = BTreeSet::new();
    scan_effect_pack(pack, state, context, &mut escapes, &mut calls);
    state.escapes.extend(escapes);
    state.calls.extend(calls);
}

fn snapshot_generic_for_effect(
    flow: HirGenericForFlow<'_>,
    state: &mut EffectState,
    context: &EffectContext<'_>,
) {
    let Some(callee) = flow.for_stmt().iterator.result_source(0) else {
        return;
    };
    let callees = effect_expr_closures(callee, state, context);
    let call_targets = effect_expr_call_targets(callee, state, context);
    let argument_origins = flow
        .for_stmt()
        .iterator
        .iter()
        .skip(1)
        .flat_map(|argument| effect_expr_origins(argument, state, context))
        .collect::<BTreeSet<_>>();
    let mut result_origins = BTreeSet::new();
    let mut result_closures = BTreeSet::new();
    for callee in &callees {
        for value in &callee.returns {
            match value {
                EffectValue::Upvalue(upvalue) => {
                    result_origins.insert(*upvalue);
                }
                EffectValue::Closure(closure) => {
                    result_closures.insert(closure.as_ref().clone());
                }
            }
        }
    }
    let result_call_targets = result_origins.clone();
    let snapshot = state.generic_for.entry(flow.protocol()).or_default();
    snapshot.callees.extend(callees);
    snapshot.call_targets.extend(call_targets);
    snapshot.argument_origins.extend(argument_origins);
    snapshot.result_origins.extend(result_origins);
    snapshot.result_closures.extend(result_closures);
    snapshot.result_call_targets.extend(result_call_targets);
}

fn dispatch_generic_for_effect(flow: HirGenericForFlow<'_>, state: &mut EffectState) {
    let Some(snapshot) = state.generic_for.get(&flow.protocol()) else {
        return;
    };
    state.calls.extend(&snapshot.call_targets);
    state.escapes.extend(&snapshot.argument_origins);
    for callee in &snapshot.callees {
        project_known_call_effects(callee, &mut state.escapes, &mut state.calls);
    }
}

fn write_for_bindings_effect(bindings: HirForBindings<'_>, state: &mut EffectState) {
    match bindings {
        HirForBindings::Numeric(local) => {
            let binding = HirBinding::Local(local);
            state.write_binding(binding, BTreeSet::new(), BTreeSet::new(), BTreeSet::new());
        }
        HirForBindings::Generic(flow) => {
            let snapshot = state
                .generic_for
                .get(&flow.protocol())
                .cloned()
                .unwrap_or_default();
            for &local in &flow.for_stmt().bindings {
                let binding = HirBinding::Local(local);
                state.write_binding(
                    binding,
                    snapshot.result_origins.clone(),
                    snapshot.result_closures.clone(),
                    snapshot.result_call_targets.clone(),
                );
            }
        }
    }
}

#[derive(Default)]
struct EffectAssignmentValue {
    origins: BTreeSet<UpvalueId>,
    closures: BTreeSet<EffectClosure>,
    call_targets: BTreeSet<UpvalueId>,
}

fn assignment_value_effects(
    value: Option<&HirExpr>,
    state: &EffectState,
    context: &EffectContext<'_>,
) -> EffectAssignmentValue {
    let Some(value) = value else {
        return EffectAssignmentValue::default();
    };
    EffectAssignmentValue {
        origins: effect_expr_origins(value, state, context),
        closures: effect_expr_closures(value, state, context),
        call_targets: effect_expr_call_targets(value, state, context),
    }
}

fn update_effect_for_stmt(stmt: &HirStmt, state: &mut EffectState, context: &EffectContext<'_>) {
    match stmt {
        HirStmt::LocalRootRelease(local) => state.write_binding(
            HirBinding::Local(*local),
            BTreeSet::new(),
            BTreeSet::new(),
            BTreeSet::new(),
        ),
        HirStmt::LocalDecl(decl) => {
            let values = (0..decl.bindings.len())
                .map(|index| {
                    assignment_value_effects(decl.values.result_source(index), state, context)
                })
                .collect::<Vec<_>>();
            note_effect_pack_escapes(&decl.values, state, context);
            for (&local, value) in decl.bindings.iter().zip(values) {
                state.write_binding(
                    HirBinding::Local(local),
                    value.origins,
                    value.closures,
                    value.call_targets,
                );
            }
        }
        HirStmt::Assign(assign) => {
            let values = assign
                .targets
                .iter()
                .enumerate()
                .map(|(index, target)| {
                    let mut value = assignment_value_effects(
                        assign.values.result_source(index),
                        state,
                        context,
                    );
                    if let HirLValue::TableAccess(access) = target {
                        value
                            .origins
                            .extend(effect_expr_origins(&access.base, state, context));
                        value
                            .origins
                            .extend(effect_expr_origins(&access.key, state, context));
                    }
                    value
                })
                .collect::<Vec<_>>();
            note_effect_pack_escapes(&assign.values, state, context);
            for (target, value) in assign.targets.iter().zip(values) {
                let EffectAssignmentValue {
                    origins,
                    closures,
                    call_targets,
                } = value;
                match target {
                    HirLValue::Param(_) | HirLValue::Temp(_) | HirLValue::Local(_) => {
                        state.write_binding(
                            HirBinding::from_lvalue(target).expect("direct binding target"),
                            origins,
                            closures,
                            call_targets,
                        );
                    }
                    HirLValue::Upvalue(upvalue) => {
                        state.escapes.extend(origins);
                        state.write_binding(
                            HirBinding::Upvalue(*upvalue),
                            BTreeSet::from([*upvalue]),
                            closures,
                            call_targets,
                        );
                    }
                    HirLValue::Global(_) | HirLValue::TableAccess(_) => {
                        state.escapes.extend(origins)
                    }
                }
            }
        }
        HirStmt::GlobalDecl(decl) => {
            for value in &decl.values {
                state
                    .escapes
                    .extend(effect_expr_origins(value, state, context));
                note_effect_escapes(value, state, context);
            }
        }
        HirStmt::TableSetList(set) => {
            state
                .escapes
                .extend(effect_expr_origins(&set.base, state, context));
            for value in &set.values {
                state
                    .escapes
                    .extend(effect_expr_origins(value, state, context));
            }
        }
        HirStmt::CallStmt(call) => {
            let expr = HirExpr::Call(Box::new(call.call.clone()));
            note_effect_escapes(&expr, state, context);
        }
        HirStmt::Return(ret) => {
            for value in &ret.values {
                state.returns.extend(
                    effect_expr_origins(value, state, context)
                        .into_iter()
                        .map(EffectValue::Upvalue),
                );
                state.returns.extend(
                    effect_expr_closures(value, state, context)
                        .into_iter()
                        .map(|closure| EffectValue::Closure(Box::new(closure))),
                );
                note_effect_escapes(value, state, context);
            }
        }
        HirStmt::If(if_stmt) => note_effect_escapes(&if_stmt.cond, state, context),
        HirStmt::While(while_stmt) => note_effect_escapes(&while_stmt.cond, state, context),
        HirStmt::Repeat(_) => {}
        HirStmt::NumericFor(for_) => {
            note_effect_escapes(&for_.start, state, context);
            note_effect_escapes(&for_.limit, state, context);
            note_effect_escapes(&for_.step, state, context);
        }
        HirStmt::GenericFor(for_) => {
            note_effect_pack_escapes(&for_.iterator, state, context);
        }
        HirStmt::Block(_) => {}
        HirStmt::ErrNil(err) => note_effect_escapes(&err.value, state, context),
        HirStmt::ToBeClosed(tbc) => note_effect_escapes(&tbc.value, state, context),
        HirStmt::Close(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => {}
    }
}

pub(super) fn collect_effect_state(
    flow: &ProtoFlowFacts<'_>,
    effects: &[ProtoEffects],
) -> ProtoEffects {
    let ProtoFlowFacts {
        proto,
        captures,
        graph,
        live_out,
        reference_cells,
        ..
    } = flow;
    let context = EffectContext { captures, effects };
    // 复用 HIR 共享 topology：若通过重复扫描结构树求收敛，没有回边的后续赋值
    // 也会倒灌到先前调用。for initializer 与 loop dispatch 必须是不同节点，避免每次
    // 回边伪造对 initializer 的重复观测。
    // may-effect 的已知 closure 仍能间接读取当前 reference cell。直接 liveness 只裁
    // 普通 binding；不能删除这种环境后把后续 callback 投影成无效果。
    // 输出只需要可观察效果；中间 binding/loop 状态不能汇入函数摘要。
    let mut summary = ProtoEffects {
        writes: proto.mutable_upvalues.clone(),
        ..ProtoEffects::default()
    };
    graph.solve_forward(
        EffectState::new(proto),
        EffectState::join,
        |id, kind, output| {
            match kind {
                HirFlowNodeKind::Exit
                | HirFlowNodeKind::FunctionExit
                | HirFlowNodeKind::UnknownControl
                | HirFlowNodeKind::NumericForDispatch => {}
                HirFlowNodeKind::Stmt(stmt) => update_effect_for_stmt(stmt, output, &context),
                HirFlowNodeKind::GenericForInit(flow) => {
                    update_effect_for_stmt(flow.stmt(), output, &context);
                    snapshot_generic_for_effect(flow, output, &context);
                }
                HirFlowNodeKind::GenericForDispatch(flow) => {
                    dispatch_generic_for_effect(flow, output);
                }
                HirFlowNodeKind::ForBinding(bindings) => {
                    write_for_bindings_effect(bindings, output);
                }
                HirFlowNodeKind::RepeatCondition(repeat) => {
                    note_effect_escapes(&repeat.cond, output, &context);
                }
            }
            summary.escapes.extend(&output.escapes);
            summary.returns.extend(output.returns.iter().cloned());
            summary.calls.extend(&output.calls);
            let retained = |binding: &HirBinding| {
                live_out[id.index()].contains(binding) || reference_cells.contains(binding)
            };
            output.origins.retain(|binding, _| retained(binding));
            output.closures.retain(|binding, _| retained(binding));
            output.call_targets.retain(|binding, _| retained(binding));
            // returns/escapes/calls 与 generic_for 快照承载已累计或独立持有的效果，
            // 不属于死 binding；这些集合不参与上述投影。
        },
        |_expr, _truthy, _state| FlowRefinement::Unchanged,
    );
    summary
}
