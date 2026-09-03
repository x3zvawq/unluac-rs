//! 词法 child-first 闭包效果摘要：把 child upvalue 的写入、逃逸、返回与调用投影到父级。
//!
//! 消费显式 capture 对应和共享 HIR CFG；例如 factory 返回读取 u0 的 closure，
//! 调用方获得对应 capture 效果，不靠函数文本或参数位置猜测。对象存活由父模块消费摘要。

use super::super::lexical_cfg::{
    HirFlowGraph, HirFlowNodeKind, HirFlowProtocolId, HirForBindings, HirGenericForFlow,
};
use super::{
    Binding, EffectClosure, EffectValue, ProtoEffects, adjusted_value, binding_from_expr,
    closure_captures_in_block, extend_map_sets,
};
use crate::hir::common::{
    HirCapture, HirCaptureMode, HirExpr, HirLValue, HirModule, HirProto, HirProtoRef, HirStmt,
    HirTableField, HirValuePack, UpvalueId,
};
use crate::hir::expr_safety::HirExprSafety;
use std::collections::{BTreeMap, BTreeSet};

pub(in crate::hir::simplify) fn collect_proto_effects(
    module: &HirModule,
    safety: HirExprSafety,
) -> Vec<ProtoEffects> {
    // Closure definitions form a lexical DAG. Summarize children first so a direct child call can
    // project its escaped/returned captures into the parent's upvalue domain.
    fn collect_one(
        index: usize,
        module: &HirModule,
        effects: &mut [ProtoEffects],
        visiting: &mut [bool],
        ready: &mut [bool],
        safety: HirExprSafety,
    ) {
        if ready[index] {
            return;
        }
        assert!(!visiting[index], "HIR lexical child graph must be acyclic");
        visiting[index] = true;
        let proto = &module.protos[index];
        for child in &proto.children {
            collect_one(child.index(), module, effects, visiting, ready, safety);
        }

        let captures = closure_captures_in_block(&proto.body);
        let state = collect_effect_state(proto, &captures, effects, safety);
        effects[index] = ProtoEffects {
            writes: proto.mutable_upvalues.clone(),
            escapes: state.escapes,
            returns: state.returns,
            calls: state.calls,
        };
        visiting[index] = false;
        ready[index] = true;
    }

    let mut effects = module
        .protos
        .iter()
        .map(|proto| ProtoEffects {
            writes: proto.mutable_upvalues.clone(),
            ..ProtoEffects::default()
        })
        .collect::<Vec<_>>();
    let mut visiting = vec![false; module.protos.len()];
    let mut ready = vec![false; module.protos.len()];
    for index in 0..module.protos.len() {
        collect_one(
            index,
            module,
            &mut effects,
            &mut visiting,
            &mut ready,
            safety,
        );
    }
    effects
}

#[derive(Clone, Default, Eq, PartialEq)]
struct EffectState {
    origins: BTreeMap<Binding, BTreeSet<UpvalueId>>,
    closures: BTreeMap<Binding, BTreeSet<EffectClosure>>,
    call_targets: BTreeMap<Binding, BTreeSet<UpvalueId>>,
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
            .map(|upvalue| (Binding::Upvalue(upvalue), BTreeSet::from([upvalue])))
            .collect();
        let call_targets = proto
            .upvalues
            .iter()
            .copied()
            .map(|upvalue| (Binding::Upvalue(upvalue), BTreeSet::from([upvalue])))
            .collect();
        Self {
            origins,
            call_targets,
            ..Self::default()
        }
    }

    fn join(&mut self, other: &Self) -> bool {
        let before = self.clone();
        extend_map_sets(&mut self.origins, &other.origins);
        extend_map_sets(&mut self.closures, &other.closures);
        extend_map_sets(&mut self.call_targets, &other.call_targets);
        self.escapes.extend(&other.escapes);
        self.returns.extend(other.returns.iter().cloned());
        self.calls.extend(&other.calls);
        for (&protocol, snapshot) in &other.generic_for {
            let current = self.generic_for.entry(protocol).or_default();
            current.callees.extend(snapshot.callees.iter().cloned());
            current.call_targets.extend(&snapshot.call_targets);
            current.argument_origins.extend(&snapshot.argument_origins);
            current.result_origins.extend(&snapshot.result_origins);
            current
                .result_closures
                .extend(snapshot.result_closures.iter().cloned());
            current
                .result_call_targets
                .extend(&snapshot.result_call_targets);
        }
        *self != before
    }
}

struct EffectContext<'a> {
    captures: &'a BTreeMap<HirProtoRef, Vec<HirCapture>>,
    effects: &'a [ProtoEffects],
}

fn effect_expr_origins(
    expr: &HirExpr,
    state: &EffectState,
    context: &EffectContext<'_>,
) -> BTreeSet<UpvalueId> {
    if let Some(binding) = binding_from_expr(expr) {
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
            effect_note_expr_escapes(
                expr,
                state,
                context,
                &mut BTreeSet::new(),
                &mut BTreeSet::new(),
            );
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
                origins.extend(effect_expr_origins(&capture.value, state, context));
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
    if let Some(binding) = binding_from_expr(expr) {
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
    let effect = context.effects.get(proto.index())?;
    let captures = context.captures.get(&proto)?;
    Some(project_proto_effect(
        proto, effect, captures, state, context,
    ))
}

fn project_proto_effect(
    proto: HirProtoRef,
    effect: &ProtoEffects,
    captures: &[HirCapture],
    state: &EffectState,
    context: &EffectContext<'_>,
) -> EffectClosure {
    let captured = captures
        .iter()
        .flat_map(|capture| effect_expr_origins(&capture.value, state, context))
        .collect();
    let writes = project_written_upvalues(&effect.writes, captures, state, context);
    let escapes = project_origin_upvalues(&effect.escapes, captures, state, context);
    let returns = project_return_values(&effect.returns, captures, state, context);
    let (mut call_escapes, calls) =
        project_called_upvalues(&effect.calls, captures, state, context);
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
    context: &EffectContext<'_>,
) -> EffectClosure {
    let captured = project_origin_upvalues(&closure.captures, captures, state, context);
    let writes = project_written_upvalues(&closure.writes, captures, state, context);
    let escapes = project_origin_upvalues(&closure.escapes, captures, state, context);
    let returns = project_return_values(&closure.returns, captures, state, context);
    let (mut call_escapes, calls) =
        project_called_upvalues(&closure.calls, captures, state, context);
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
    context: &EffectContext<'_>,
) -> BTreeSet<UpvalueId> {
    upvalues
        .iter()
        .filter_map(|upvalue| captures.get(upvalue.index()))
        .flat_map(|capture| effect_expr_origins(&capture.value, state, context))
        .collect()
}

fn project_written_upvalues(
    upvalues: &BTreeSet<UpvalueId>,
    captures: &[HirCapture],
    state: &EffectState,
    context: &EffectContext<'_>,
) -> BTreeSet<UpvalueId> {
    upvalues
        .iter()
        .filter_map(|upvalue| captures.get(upvalue.index()))
        .filter(|capture| capture.mode == HirCaptureMode::ByReference)
        .flat_map(|capture| effect_expr_origins(&capture.value, state, context))
        .collect()
}

fn project_return_values(
    values: &BTreeSet<EffectValue>,
    captures: &[HirCapture],
    state: &EffectState,
    context: &EffectContext<'_>,
) -> BTreeSet<EffectValue> {
    let mut projected = BTreeSet::new();
    for value in values {
        match value {
            EffectValue::Upvalue(upvalue) => {
                let Some(capture) = captures.get(upvalue.index()) else {
                    continue;
                };
                projected.extend(
                    effect_expr_origins(&capture.value, state, context)
                        .into_iter()
                        .map(EffectValue::Upvalue),
                );
                projected.extend(
                    effect_expr_closures(&capture.value, state, context)
                        .into_iter()
                        .map(|closure| EffectValue::Closure(Box::new(closure))),
                );
            }
            EffectValue::Closure(closure) => {
                projected.insert(EffectValue::Closure(Box::new(project_nested_closure(
                    closure, captures, state, context,
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
    context: &EffectContext<'_>,
) -> (BTreeSet<UpvalueId>, BTreeSet<UpvalueId>) {
    let mut escapes = BTreeSet::new();
    let mut calls = BTreeSet::new();
    for upvalue in upvalues {
        let Some(capture) = captures.get(upvalue.index()) else {
            continue;
        };
        calls.extend(effect_expr_call_targets(&capture.value, state, context));
        for closure in effect_expr_closures(&capture.value, state, context) {
            escapes.extend(closure.escapes);
            calls.extend(closure.calls);
        }
    }
    (escapes, calls)
}

fn effect_expr_call_targets(
    expr: &HirExpr,
    state: &EffectState,
    context: &EffectContext<'_>,
) -> BTreeSet<UpvalueId> {
    if let Some(binding) = binding_from_expr(expr) {
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
        HirExpr::Closure(closure) => {
            for capture in &closure.captures {
                effect_note_expr_escapes(&capture.value, state, context, escapes, calls);
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
    let Some(callee) = adjusted_value(&flow.for_stmt().iterator, 0) else {
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
    let Some(snapshot) = state.generic_for.get(&flow.protocol()).cloned() else {
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
            let binding = Binding::Local(local);
            state.origins.insert(binding, BTreeSet::new());
            state.closures.insert(binding, BTreeSet::new());
            state.call_targets.insert(binding, BTreeSet::new());
        }
        HirForBindings::Generic(flow) => {
            let snapshot = state
                .generic_for
                .get(&flow.protocol())
                .cloned()
                .unwrap_or_default();
            for &local in &flow.for_stmt().bindings {
                let binding = Binding::Local(local);
                state
                    .origins
                    .insert(binding, snapshot.result_origins.clone());
                state
                    .closures
                    .insert(binding, snapshot.result_closures.clone());
                state
                    .call_targets
                    .insert(binding, snapshot.result_call_targets.clone());
            }
        }
    }
}

fn update_effect_for_stmt(stmt: &HirStmt, state: &mut EffectState, context: &EffectContext<'_>) {
    match stmt {
        HirStmt::LocalDecl(decl) => {
            let snapshot = state.clone();
            note_effect_pack_escapes(&decl.values, state, context);
            for (index, local) in decl.bindings.iter().copied().enumerate() {
                let origins = adjusted_value(&decl.values, index)
                    .map_or_else(BTreeSet::new, |value| {
                        effect_expr_origins(value, &snapshot, context)
                    });
                let closures = adjusted_value(&decl.values, index)
                    .map_or_else(BTreeSet::new, |value| {
                        effect_expr_closures(value, &snapshot, context)
                    });
                let call_targets = adjusted_value(&decl.values, index)
                    .map_or_else(BTreeSet::new, |value| {
                        effect_expr_call_targets(value, &snapshot, context)
                    });
                state.origins.insert(Binding::Local(local), origins);
                state.closures.insert(Binding::Local(local), closures);
                state
                    .call_targets
                    .insert(Binding::Local(local), call_targets);
            }
        }
        HirStmt::Assign(assign) => {
            let snapshot = state.clone();
            note_effect_pack_escapes(&assign.values, state, context);
            for (index, target) in assign.targets.iter().enumerate() {
                let origins = adjusted_value(&assign.values, index)
                    .map_or_else(BTreeSet::new, |value| {
                        effect_expr_origins(value, &snapshot, context)
                    });
                let closures = adjusted_value(&assign.values, index)
                    .map_or_else(BTreeSet::new, |value| {
                        effect_expr_closures(value, &snapshot, context)
                    });
                let call_targets = adjusted_value(&assign.values, index)
                    .map_or_else(BTreeSet::new, |value| {
                        effect_expr_call_targets(value, &snapshot, context)
                    });
                match target {
                    HirLValue::Param(param) => {
                        state.origins.insert(Binding::Param(*param), origins);
                        state.closures.insert(Binding::Param(*param), closures);
                        state
                            .call_targets
                            .insert(Binding::Param(*param), call_targets);
                    }
                    HirLValue::Temp(temp) => {
                        state.origins.insert(Binding::Temp(*temp), origins);
                        state.closures.insert(Binding::Temp(*temp), closures);
                        state
                            .call_targets
                            .insert(Binding::Temp(*temp), call_targets);
                    }
                    HirLValue::Local(local) => {
                        state.origins.insert(Binding::Local(*local), origins);
                        state.closures.insert(Binding::Local(*local), closures);
                        state
                            .call_targets
                            .insert(Binding::Local(*local), call_targets);
                    }
                    HirLValue::Upvalue(upvalue) => {
                        state.escapes.extend(origins);
                        state
                            .origins
                            .insert(Binding::Upvalue(*upvalue), BTreeSet::from([*upvalue]));
                        state.closures.insert(Binding::Upvalue(*upvalue), closures);
                        state
                            .call_targets
                            .insert(Binding::Upvalue(*upvalue), call_targets);
                    }
                    HirLValue::Global(_) => state.escapes.extend(origins),
                    HirLValue::TableAccess(access) => {
                        state.escapes.extend(origins);
                        state
                            .escapes
                            .extend(effect_expr_origins(&access.base, &snapshot, context));
                        state
                            .escapes
                            .extend(effect_expr_origins(&access.key, &snapshot, context));
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

fn collect_effect_state(
    proto: &HirProto,
    captures: &BTreeMap<HirProtoRef, Vec<HirCapture>>,
    effects: &[ProtoEffects],
    safety: HirExprSafety,
) -> EffectState {
    let context = EffectContext { captures, effects };
    // 复用 HIR 共享 topology：若通过重复扫描结构树求收敛，没有回边的后续赋值
    // 也会倒灌到先前调用。for initializer 与 loop dispatch 必须是不同节点，避免每次
    // 回边伪造对 initializer 的重复观测。
    let graph = HirFlowGraph::for_block(&proto.body, safety)
        .expect("HIR labels must be unique before effect finalization");
    let mut summary = EffectState::default();
    graph.solve_forward(
        EffectState::new(proto),
        EffectState::join,
        |_, kind, output| {
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
            summary.join(output);
        },
    );
    summary
}
