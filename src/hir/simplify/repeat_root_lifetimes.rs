//! fixed-point 后为 `repeat ... until` 条件保留物理 GC root。
//!
//! 该分析消费最终 HIR 的稳定 binding、closure capture 和结构化控制流；它不重建
//! 字节码寄存器。只有 body 中的 local/temp 当前仍持有已逃逸 collectable identity，
//! 或已知 closure 调用可能把 collectable 值写入该 binding，且 `until` 条件可执行
//! 用户代码/GC 时，才把 binding 标成 physical root。未逃逸的 fresh aggregate 不标记。
//! closure 的 escape/return effect 按词法 child-first 汇总，每个 proto 都在真实 HIR CFG
//! 上求 fixed point；因此 `loop { sink(a); a = captured }` 的回边可以传播 capture，直线
//! 代码中的后续赋值却不会倒灌到先前调用。通过 upvalue 调用的 closure 保留符号化 call
//! effect，直到拥有实际 capture 环境的 root 分析再解析。最终同时写入 proto-wide
//! `physical_root_*` 负向事实，以及具体 repeat condition endpoint 的正向
//! `may_end_before_condition` 事实。AST 只消费这些 typed provenance，并继续证明候选
//! 源码的词法/控制流合法性，不在源码候选上重建 VM 生命周期。

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::hir::common::{
    HirBlock, HirCapture, HirCaptureMode, HirExpr, HirLValue, HirModule, HirProto, HirProtoRef,
    HirRepeatBinding, HirRepeatConditionLifetimeFacts, HirStmt, HirTableField, HirValuePack,
    LocalId, ParamId, TempId, UpvalueId,
};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::ProtoPromotionFacts;

use super::lexical_cfg::{
    HirFlowGraph, HirFlowNodeKind, HirFlowProtocolId, HirForBindings, HirGenericForFlow,
};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Binding {
    Param(ParamId),
    Local(LocalId),
    Temp(TempId),
    Upvalue(UpvalueId),
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum ObjectId {
    Table(usize),
    Closure(HirProtoRef),
    ReturnedClosure {
        producer: HirProtoRef,
        closure: HirProtoRef,
    },
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum EffectValue {
    Upvalue(UpvalueId),
    Closure(Box<EffectClosure>),
}

/// 已投影到当前 proto upvalue 域的 closure 值。
///
/// `proto` 保留 allocation site 身份；其余集合让经 factory 返回的 closure 在离开原始
/// capture 表后，仍能由调用方精确应用 call/return effect。
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct EffectClosure {
    proto: HirProtoRef,
    captures: BTreeSet<UpvalueId>,
    writes: BTreeSet<UpvalueId>,
    escapes: BTreeSet<UpvalueId>,
    returns: BTreeSet<EffectValue>,
    calls: BTreeSet<UpvalueId>,
}

#[derive(Clone, Default)]
struct ProtoEffects {
    writes: BTreeSet<UpvalueId>,
    escapes: BTreeSet<UpvalueId>,
    returns: BTreeSet<EffectValue>,
    calls: BTreeSet<UpvalueId>,
}

/// 在所有结构改写收敛后补齐 repeat 条件仍可观察的物理 root。
///
/// 集成点应位于 `run_invalidation_loop` 成功收敛之后、AST build 之前。该步骤只增加
/// provenance 集合，不改写 HIR 形状，因此不需要重新唤醒 simplify passes。
pub(super) fn mark_repeat_trailing_condition_roots(
    module: &mut HirModule,
    promotion_facts: &[ProtoPromotionFacts],
    safety: HirExprSafety,
) -> bool {
    let effects = collect_proto_effects(module, safety);
    let mut roots = Vec::with_capacity(module.protos.len());
    for proto in &module.protos {
        let facts = promotion_facts.get(proto.id.index());
        roots.push(collect_proto_repeat_roots(proto, facts, &effects, safety));
    }

    let mut changed = false;
    for (proto, roots) in module.protos.iter_mut().zip(roots) {
        let old_local_count = proto.physical_root_locals.len();
        let old_temp_count = proto.physical_root_temps.len();
        proto.physical_root_locals.extend(roots.locals);
        proto.physical_root_temps.extend(roots.temps);
        changed |= old_local_count != proto.physical_root_locals.len()
            || old_temp_count != proto.physical_root_temps.len();
        changed |= install_repeat_condition_lifetime_facts(&mut proto.body, &roots.repeat_facts);
    }
    changed
}

#[derive(Default)]
struct RepeatRoots {
    locals: BTreeSet<LocalId>,
    temps: BTreeSet<TempId>,
    repeat_facts: BTreeMap<usize, HirRepeatConditionLifetimeFacts>,
}

fn collect_proto_repeat_roots(
    proto: &HirProto,
    facts: Option<&ProtoPromotionFacts>,
    effects: &[ProtoEffects],
    safety: HirExprSafety,
) -> RepeatRoots {
    let captures = closure_captures_in_block(&proto.body);
    let graph = HirFlowGraph::for_block(&proto.body, safety)
        .expect("HIR labels must be unique before repeat root finalization");
    let entry = graph.entry();
    let mut entries = vec![None::<RootState>; graph.nodes().len()];
    let mut initial = RootState::default();
    initial
        .unknown_collectable
        .extend(proto.params.iter().copied().map(Binding::Param));
    initial
        .unknown_collectable
        .extend(proto.upvalues.iter().copied().map(Binding::Upvalue));
    entries[entry.index()] = Some(initial);
    let mut pending = VecDeque::from([entry]);
    let mut roots = RepeatRoots::default();

    while let Some(index) = pending.pop_front() {
        let mut output = entries[index.index()]
            .as_ref()
            .expect("queued repeat-root node must be reachable")
            .clone();
        match graph.nodes()[index.index()].kind() {
            HirFlowNodeKind::Exit
            | HirFlowNodeKind::FunctionExit
            | HirFlowNodeKind::UnknownControl
            | HirFlowNodeKind::NumericForDispatch => {}
            HirFlowNodeKind::Stmt(stmt) => {
                update_state_for_stmt(stmt, &mut output, &captures, effects, safety)
            }
            HirFlowNodeKind::GenericForInit(flow) => {
                update_state_for_stmt(flow.stmt(), &mut output, &captures, effects, safety);
                snapshot_generic_for_root(flow, &mut output, effects);
            }
            HirFlowNodeKind::GenericForDispatch(flow) => {
                dispatch_generic_for_root(flow, &mut output, &captures, effects, safety);
            }
            HirFlowNodeKind::ForBinding(bindings) => {
                write_for_bindings_root(bindings, &mut output);
            }
            HirFlowNodeKind::RepeatCondition(repeat) => {
                note_repeat_condition_lifetimes(repeat, &output, facts, &mut roots, safety);
                observe_expr(&repeat.cond, &mut output, &captures, effects, safety);
            }
        }
        for &successor in graph.nodes()[index.index()].successors() {
            if join_state(&mut entries[successor.index()], &output) {
                pending.push_back(successor);
            }
        }
    }
    roots
}

fn note_repeat_condition_lifetimes(
    repeat: &crate::hir::common::HirRepeat,
    state: &RootState,
    facts: Option<&ProtoPromotionFacts>,
    roots: &mut RepeatRoots,
    safety: HirExprSafety,
) {
    let direct_bindings = direct_repeat_bindings(&repeat.body);
    let repeat_key = std::ptr::from_ref(repeat).addr();
    roots
        .repeat_facts
        .entry(repeat_key)
        .or_insert_with(|| HirRepeatConditionLifetimeFacts {
            may_end_before_condition: direct_bindings
                .iter()
                .filter_map(|binding| repeat_binding(*binding))
                .collect(),
        });

    for binding in direct_repeat_bindings(&repeat.body) {
        let eventful = !safety.is_discard_safe_without_residual(&repeat.cond);
        let observable = eventful
            && (state.roots.get(&binding).copied().unwrap_or(false)
                || state
                    .holders
                    .get(&binding)
                    .is_some_and(|holders| !holders.is_disjoint(&state.escaped)));
        let has_physical_home = match binding {
            Binding::Local(local) => {
                !facts.is_some_and(|facts| facts.local_has_no_physical_home(local))
            }
            Binding::Temp(temp) => !facts.is_some_and(|facts| {
                facts
                    .possible_temp_home_slots(temp)
                    .is_some_and(|homes| homes.is_empty())
            }),
            Binding::Param(_) | Binding::Upvalue(_) => false,
        };
        if observable && has_physical_home {
            if let Some(binding) = repeat_binding(binding) {
                roots
                    .repeat_facts
                    .get_mut(&repeat_key)
                    .expect("reachable repeat must have endpoint facts")
                    .may_end_before_condition
                    .remove(&binding);
            }
            match binding {
                Binding::Local(local) => {
                    roots.locals.insert(local);
                }
                Binding::Temp(temp) => {
                    roots.temps.insert(temp);
                }
                Binding::Param(_) | Binding::Upvalue(_) => {}
            }
        }
    }
}

fn repeat_binding(binding: Binding) -> Option<HirRepeatBinding> {
    match binding {
        Binding::Local(local) => Some(HirRepeatBinding::Local(local)),
        Binding::Temp(temp) => Some(HirRepeatBinding::Temp(temp)),
        Binding::Param(_) | Binding::Upvalue(_) => None,
    }
}

fn install_repeat_condition_lifetime_facts(
    block: &mut HirBlock,
    facts: &BTreeMap<usize, HirRepeatConditionLifetimeFacts>,
) -> bool {
    let mut changed = false;
    for stmt in &mut block.stmts {
        match stmt {
            HirStmt::If(if_stmt) => {
                changed |= install_repeat_condition_lifetime_facts(&mut if_stmt.then_block, facts);
                if let Some(else_block) = &mut if_stmt.else_block {
                    changed |= install_repeat_condition_lifetime_facts(else_block, facts);
                }
            }
            HirStmt::While(while_stmt) => {
                changed |= install_repeat_condition_lifetime_facts(&mut while_stmt.body, facts);
            }
            HirStmt::Repeat(repeat) => {
                let repeat_key = std::ptr::from_ref(repeat.as_ref()).addr();
                let replacement = facts.get(&repeat_key).cloned().unwrap_or_default();
                if repeat.lifetime != replacement {
                    repeat.lifetime = replacement;
                    changed = true;
                }
                changed |= install_repeat_condition_lifetime_facts(&mut repeat.body, facts);
            }
            HirStmt::NumericFor(for_) => {
                changed |= install_repeat_condition_lifetime_facts(&mut for_.body, facts);
            }
            HirStmt::GenericFor(for_) => {
                changed |= install_repeat_condition_lifetime_facts(&mut for_.body, facts);
            }
            HirStmt::Block(block) => {
                changed |= install_repeat_condition_lifetime_facts(block, facts);
            }
            HirStmt::LocalDecl(_)
            | HirStmt::GlobalDecl(_)
            | HirStmt::Assign(_)
            | HirStmt::TableSetList(_)
            | HirStmt::ErrNil(_)
            | HirStmt::ToBeClosed(_)
            | HirStmt::Close(_)
            | HirStmt::CallStmt(_)
            | HirStmt::Return(_)
            | HirStmt::Break
            | HirStmt::Continue
            | HirStmt::Goto(_)
            | HirStmt::Label(_) => {}
        }
    }
    changed
}

fn direct_repeat_bindings(block: &HirBlock) -> BTreeSet<Binding> {
    let mut bindings = BTreeSet::new();
    for stmt in &block.stmts {
        match stmt {
            HirStmt::LocalDecl(decl) => {
                bindings.extend(decl.bindings.iter().copied().map(Binding::Local))
            }
            HirStmt::Assign(assign) => bindings.extend(
                assign
                    .targets
                    .iter()
                    .filter_map(binding_from_lvalue)
                    .filter(|binding| matches!(binding, Binding::Temp(_))),
            ),
            _ => {}
        }
    }
    bindings
}

#[derive(Clone, Default)]
struct RootState {
    roots: BTreeMap<Binding, bool>,
    holders: BTreeMap<Binding, BTreeSet<ObjectId>>,
    tables: BTreeMap<Binding, BTreeSet<ObjectId>>,
    unknown_collectable: BTreeSet<Binding>,
    escaped: BTreeSet<ObjectId>,
    generic_for: BTreeMap<HirFlowProtocolId, GenericForRootSnapshot>,
}

#[derive(Clone, Default, Eq, PartialEq)]
struct GenericForRootSnapshot {
    callees: BTreeSet<ObjectId>,
    arguments: BTreeSet<ObjectId>,
    returns: BTreeSet<ObjectId>,
}

fn join_state(entry: &mut Option<RootState>, incoming: &RootState) -> bool {
    let Some(current) = entry else {
        *entry = Some(incoming.clone());
        return true;
    };
    let before = (
        current.roots.clone(),
        current.holders.clone(),
        current.tables.clone(),
        current.unknown_collectable.clone(),
        current.escaped.clone(),
        current.generic_for.clone(),
    );
    for (&binding, &root) in &incoming.roots {
        if root {
            current.roots.insert(binding, true);
        }
    }
    extend_map_sets(&mut current.holders, &incoming.holders);
    extend_map_sets(&mut current.tables, &incoming.tables);
    current
        .unknown_collectable
        .extend(&incoming.unknown_collectable);
    current.escaped.extend(&incoming.escaped);
    for (&protocol, snapshot) in &incoming.generic_for {
        let current_snapshot = current.generic_for.entry(protocol).or_default();
        current_snapshot.callees.extend(&snapshot.callees);
        current_snapshot.arguments.extend(&snapshot.arguments);
        current_snapshot.returns.extend(&snapshot.returns);
    }
    before
        != (
            current.roots.clone(),
            current.holders.clone(),
            current.tables.clone(),
            current.unknown_collectable.clone(),
            current.escaped.clone(),
            current.generic_for.clone(),
        )
}

fn extend_map_sets<K: Copy + Ord, V: Clone + Ord>(
    target: &mut BTreeMap<K, BTreeSet<V>>,
    source: &BTreeMap<K, BTreeSet<V>>,
) {
    for (&key, values) in source {
        target
            .entry(key)
            .or_default()
            .extend(values.iter().cloned());
    }
}

fn snapshot_generic_for_root(
    flow: HirGenericForFlow<'_>,
    state: &mut RootState,
    effects: &[ProtoEffects],
) {
    let Some(callee) = adjusted_value(&flow.for_stmt().iterator, 0) else {
        return;
    };
    let callees = holder_values(callee, state, effects);
    let mut arguments = BTreeSet::new();
    for argument in flow.for_stmt().iterator.iter().skip(1) {
        arguments.extend(holder_values(argument, state, effects));
    }
    let returns = returned_holder_values(&callees, effects);
    let snapshot = state.generic_for.entry(flow.protocol()).or_default();
    snapshot.callees.extend(callees);
    snapshot.arguments.extend(arguments);
    snapshot.returns.extend(returns);
}

fn dispatch_generic_for_root(
    flow: HirGenericForFlow<'_>,
    state: &mut RootState,
    captures: &BTreeMap<HirProtoRef, Vec<HirCapture>>,
    effects: &[ProtoEffects],
    safety: HirExprSafety,
) {
    let Some(snapshot) = state.generic_for.get(&flow.protocol()).cloned() else {
        return;
    };
    activate_object_ids(&snapshot.callees, state, captures, effects, false, safety);
    state.escaped.extend(&snapshot.arguments);
    activate_object_ids(&snapshot.arguments, state, captures, effects, true, safety);
}

fn write_for_bindings_root(bindings: HirForBindings<'_>, state: &mut RootState) {
    match bindings {
        HirForBindings::Numeric(local) => {
            let binding = Binding::Local(local);
            state.holders.insert(binding, BTreeSet::new());
            state.tables.insert(binding, BTreeSet::new());
            state.unknown_collectable.remove(&binding);
            state.roots.insert(binding, false);
        }
        HirForBindings::Generic(flow) => {
            let returned = state
                .generic_for
                .get(&flow.protocol())
                .map(|snapshot| snapshot.returns.clone())
                .unwrap_or_default();
            for &local in &flow.for_stmt().bindings {
                let binding = Binding::Local(local);
                state.holders.insert(binding, returned.clone());
                state.tables.insert(binding, BTreeSet::new());
                state.unknown_collectable.insert(binding);
                state.roots.insert(binding, true);
            }
        }
    }
}

fn update_state_for_stmt(
    stmt: &HirStmt,
    state: &mut RootState,
    captures: &BTreeMap<HirProtoRef, Vec<HirCapture>>,
    effects: &[ProtoEffects],
    safety: HirExprSafety,
) {
    observe_stmt(stmt, state, captures, effects, safety);
    match stmt {
        HirStmt::LocalDecl(decl) => assign_bindings(
            decl.bindings.iter().copied().map(Binding::Local),
            &decl.values,
            state,
            effects,
            safety,
        ),
        HirStmt::Assign(assign) => {
            let snapshot = state.clone();
            for (index, target) in assign.targets.iter().enumerate() {
                if matches!(target, HirLValue::Global(_) | HirLValue::Upvalue(_))
                    && let Some(value) = adjusted_value(&assign.values, index)
                {
                    escape_expr(value, state, captures, effects, safety);
                }
                if let Some(binding) = binding_from_lvalue(target) {
                    assign_binding(
                        binding,
                        adjusted_value(&assign.values, index),
                        &snapshot,
                        state,
                        effects,
                        safety,
                    );
                } else if let HirLValue::TableAccess(access) = target {
                    store_table(
                        access,
                        adjusted_value(&assign.values, index),
                        state,
                        captures,
                        effects,
                        safety,
                    );
                }
            }
        }
        HirStmt::GlobalDecl(decl) => {
            for value in &decl.values {
                escape_expr(value, state, captures, effects, safety);
            }
        }
        HirStmt::TableSetList(set) => {
            for value in &set.values {
                escape_expr(value, state, captures, effects, safety);
            }
        }
        _ => {}
    }
}

fn assign_bindings(
    bindings: impl Iterator<Item = Binding>,
    values: &HirValuePack,
    state: &mut RootState,
    effects: &[ProtoEffects],
    safety: HirExprSafety,
) {
    let bindings = bindings.collect::<Vec<_>>();
    let snapshot = state.clone();
    for (index, binding) in bindings.iter().copied().enumerate() {
        assign_binding(
            binding,
            adjusted_value(values, index),
            &snapshot,
            state,
            effects,
            safety,
        );
    }
}

fn assign_binding(
    binding: Binding,
    value: Option<&HirExpr>,
    snapshot: &RootState,
    state: &mut RootState,
    effects: &[ProtoEffects],
    safety: HirExprSafety,
) {
    let holders = value.map_or_else(BTreeSet::new, |value| {
        holder_values(value, snapshot, effects)
    });
    let tables = value.map_or_else(BTreeSet::new, |value| table_values(value, snapshot));
    state.holders.insert(binding, holders);
    state.tables.insert(binding, tables);
    let unknown = adjusted_value_may_be_unknown(value, snapshot, safety);
    if unknown {
        state.unknown_collectable.insert(binding);
    } else {
        state.unknown_collectable.remove(&binding);
    }
    state.roots.insert(
        binding,
        value.is_some_and(|value| expr_may_root(value, snapshot, safety)),
    );
}

fn adjusted_value(values: &HirValuePack, index: usize) -> Option<&HirExpr> {
    if let Some(value) = values.fixed.get(index) {
        return Some(value);
    }
    let tail = values.tail.as_ref()?;
    let tail_index = index - values.fixed.len();
    tail.exact_width()
        .is_none_or(|width| tail_index < width)
        .then(|| tail.as_expr())
}

fn adjusted_value_may_be_unknown(
    value: Option<&HirExpr>,
    state: &RootState,
    safety: HirExprSafety,
) -> bool {
    value.is_some_and(|value| expr_may_be_unknown(value, state, safety))
}

fn expr_may_be_unknown(expr: &HirExpr, state: &RootState, safety: HirExprSafety) -> bool {
    match expr {
        HirExpr::ParamRef(id) => state.unknown_collectable.contains(&Binding::Param(*id)),
        HirExpr::LocalRef(id) => state.unknown_collectable.contains(&Binding::Local(*id)),
        HirExpr::TempRef(id) => state.unknown_collectable.contains(&Binding::Temp(*id)),
        HirExpr::UpvalueRef(id) => state.unknown_collectable.contains(&Binding::Upvalue(*id)),
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_may_be_unknown(&logical.lhs, state, safety)
                || expr_may_be_unknown(&logical.rhs, state, safety)
        }
        HirExpr::TableConstructor(_) | HirExpr::Closure(_) => false,
        _ => !safety.result_is_gc_inert(expr),
    }
}

fn expr_may_root(expr: &HirExpr, state: &RootState, safety: HirExprSafety) -> bool {
    if let Some(binding) = binding_from_expr(expr) {
        return state.roots.get(&binding).copied().unwrap_or(false)
            || state
                .holders
                .get(&binding)
                .is_some_and(|holders| !holders.is_disjoint(&state.escaped));
    }
    match expr {
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_may_root(&logical.lhs, state, safety) || expr_may_root(&logical.rhs, state, safety)
        }
        HirExpr::TableConstructor(table) => table.fields.iter().any(|field| match field {
            HirTableField::Array(value) => expr_may_root(value, state, safety),
            HirTableField::Record(record) => {
                expr_may_root(&record.key, state, safety)
                    || expr_may_root(&record.value, state, safety)
            }
        }),
        HirExpr::Closure(_) => false,
        _ => !safety.result_is_gc_inert(expr),
    }
}

fn holder_values(
    expr: &HirExpr,
    state: &RootState,
    effects: &[ProtoEffects],
) -> BTreeSet<ObjectId> {
    if let Some(binding) = binding_from_expr(expr) {
        return state.holders.get(&binding).cloned().unwrap_or_default();
    }
    match expr {
        HirExpr::Closure(closure) => BTreeSet::from([ObjectId::Closure(closure.proto)]),
        HirExpr::TableConstructor(table) => {
            let mut holders =
                BTreeSet::from([ObjectId::Table(std::ptr::from_ref(table.as_ref()).addr())]);
            for field in &table.fields {
                match field {
                    HirTableField::Array(value) => {
                        holders.extend(holder_values(value, state, effects));
                    }
                    HirTableField::Record(record) => {
                        holders.extend(holder_values(&record.key, state, effects));
                        holders.extend(holder_values(&record.value, state, effects));
                    }
                }
            }
            holders
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            let mut values = holder_values(&logical.lhs, state, effects);
            values.extend(holder_values(&logical.rhs, state, effects));
            values
        }
        HirExpr::TableAccess(access) => holder_values(&access.base, state, effects),
        HirExpr::Call(call) => {
            returned_holder_values(&holder_values(&call.callee, state, effects), effects)
        }
        _ => BTreeSet::new(),
    }
}

fn returned_holder_values(
    callees: &BTreeSet<ObjectId>,
    effects: &[ProtoEffects],
) -> BTreeSet<ObjectId> {
    let mut returned = BTreeSet::new();
    for &callee in callees {
        let (producer, returns) = match callee {
            ObjectId::Closure(proto) => {
                let Some(effect) = effects.get(proto.index()) else {
                    continue;
                };
                (proto, &effect.returns)
            }
            ObjectId::ReturnedClosure { producer, closure } => {
                let Some(effect) = effects.get(producer.index()) else {
                    continue;
                };
                for closure in returned_closures(&effect.returns, closure) {
                    returned.extend(closure.returns.iter().filter_map(|value| match value {
                        EffectValue::Upvalue(_) => None,
                        EffectValue::Closure(closure) => Some(ObjectId::ReturnedClosure {
                            producer,
                            closure: closure.proto,
                        }),
                    }));
                }
                continue;
            }
            ObjectId::Table(_) => continue,
        };
        returned.extend(returns.iter().filter_map(|value| match value {
            EffectValue::Upvalue(_) => None,
            EffectValue::Closure(closure) => Some(ObjectId::ReturnedClosure {
                producer,
                closure: closure.proto,
            }),
        }));
    }
    returned
}

fn returned_closures(values: &BTreeSet<EffectValue>, target: HirProtoRef) -> Vec<&EffectClosure> {
    fn collect<'a>(
        values: &'a BTreeSet<EffectValue>,
        target: HirProtoRef,
        found: &mut Vec<&'a EffectClosure>,
    ) {
        for value in values {
            let EffectValue::Closure(closure) = value else {
                continue;
            };
            if closure.proto == target {
                found.push(closure);
            }
            collect(&closure.returns, target, found);
        }
    }

    let mut found = Vec::new();
    collect(values, target, &mut found);
    found
}

fn table_values(expr: &HirExpr, state: &RootState) -> BTreeSet<ObjectId> {
    if let Some(binding) = binding_from_expr(expr) {
        return state.tables.get(&binding).cloned().unwrap_or_default();
    }
    match expr {
        HirExpr::TableConstructor(table) => {
            BTreeSet::from([ObjectId::Table(std::ptr::from_ref(table.as_ref()).addr())])
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            let mut values = table_values(&logical.lhs, state);
            values.extend(table_values(&logical.rhs, state));
            values
        }
        _ => BTreeSet::new(),
    }
}

fn store_table(
    access: &crate::hir::common::HirTableAccess,
    value: Option<&HirExpr>,
    state: &mut RootState,
    captures: &BTreeMap<HirProtoRef, Vec<HirCapture>>,
    effects: &[ProtoEffects],
    safety: HirExprSafety,
) {
    let tables = table_values(&access.base, state);
    let base_has_unknown = bindings_in_expr(&access.base)
        .iter()
        .any(|binding| state.unknown_collectable.contains(binding));
    let is_known_plain =
        !tables.is_empty() && tables.is_disjoint(&state.escaped) && !base_has_unknown;
    if !is_known_plain {
        escape_expr(&access.base, state, captures, effects, safety);
        escape_expr(&access.key, state, captures, effects, safety);
        if let Some(value) = value {
            escape_expr(value, state, captures, effects, safety);
        }
        return;
    }

    let mut stored = holder_values(&access.key, state, effects);
    if let Some(value) = value {
        stored.extend(holder_values(value, state, effects));
    }
    let may_root = expr_may_root(&access.key, state, safety)
        || value.is_some_and(|value| expr_may_root(value, state, safety));
    let aliases = state
        .tables
        .iter()
        .filter_map(|(&binding, values)| (!values.is_disjoint(&tables)).then_some(binding))
        .collect::<Vec<_>>();
    for binding in aliases {
        state.holders.entry(binding).or_default().extend(&stored);
        if may_root {
            state.roots.insert(binding, true);
        }
    }
}

fn observe_stmt(
    stmt: &HirStmt,
    state: &mut RootState,
    captures: &BTreeMap<HirProtoRef, Vec<HirCapture>>,
    effects: &[ProtoEffects],
    safety: HirExprSafety,
) {
    match stmt {
        HirStmt::LocalDecl(decl) => observe_pack(&decl.values, state, captures, effects, safety),
        HirStmt::GlobalDecl(decl) => observe_pack(&decl.values, state, captures, effects, safety),
        HirStmt::Assign(assign) => {
            for target in &assign.targets {
                if let HirLValue::TableAccess(access) = target {
                    observe_expr(&access.base, state, captures, effects, safety);
                    observe_expr(&access.key, state, captures, effects, safety);
                }
            }
            observe_pack(&assign.values, state, captures, effects, safety);
        }
        HirStmt::TableSetList(set) => {
            observe_expr(&set.base, state, captures, effects, safety);
            observe_pack(&set.values, state, captures, effects, safety);
        }
        HirStmt::ErrNil(err) => observe_expr(&err.value, state, captures, effects, safety),
        HirStmt::ToBeClosed(tbc) => observe_expr(&tbc.value, state, captures, effects, safety),
        HirStmt::CallStmt(call) => observe_call(&call.call, state, captures, effects, safety),
        HirStmt::Return(ret) => {
            observe_pack(&ret.values, state, captures, effects, safety);
            for value in &ret.values {
                escape_expr(value, state, captures, effects, safety);
            }
        }
        HirStmt::If(if_stmt) => observe_expr(&if_stmt.cond, state, captures, effects, safety),
        HirStmt::While(while_stmt) => {
            observe_expr(&while_stmt.cond, state, captures, effects, safety)
        }
        HirStmt::NumericFor(for_) => {
            observe_expr(&for_.start, state, captures, effects, safety);
            observe_expr(&for_.limit, state, captures, effects, safety);
            observe_expr(&for_.step, state, captures, effects, safety);
        }
        HirStmt::GenericFor(for_) => observe_pack(&for_.iterator, state, captures, effects, safety),
        HirStmt::Repeat(_)
        | HirStmt::Close(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_)
        | HirStmt::Block(_) => {}
    }
}

fn observe_pack(
    pack: &HirValuePack,
    state: &mut RootState,
    captures: &BTreeMap<HirProtoRef, Vec<HirCapture>>,
    effects: &[ProtoEffects],
    safety: HirExprSafety,
) {
    for value in pack {
        observe_expr(value, state, captures, effects, safety);
    }
}

fn observe_expr(
    expr: &HirExpr,
    state: &mut RootState,
    captures: &BTreeMap<HirProtoRef, Vec<HirCapture>>,
    effects: &[ProtoEffects],
    safety: HirExprSafety,
) {
    match expr {
        HirExpr::TableAccess(access) => {
            observe_expr(&access.base, state, captures, effects, safety);
            observe_expr(&access.key, state, captures, effects, safety);
        }
        HirExpr::Unary(unary) => observe_expr(&unary.expr, state, captures, effects, safety),
        HirExpr::Binary(binary) => {
            observe_expr(&binary.lhs, state, captures, effects, safety);
            observe_expr(&binary.rhs, state, captures, effects, safety);
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            observe_expr(&logical.lhs, state, captures, effects, safety);
            observe_expr(&logical.rhs, state, captures, effects, safety);
        }
        HirExpr::Decision(decision) => {
            for node in &decision.nodes {
                observe_expr(&node.test, state, captures, effects, safety);
                if let crate::hir::common::HirDecisionTarget::Expr(expr) = &node.truthy {
                    observe_expr(expr, state, captures, effects, safety);
                }
                if let crate::hir::common::HirDecisionTarget::Expr(expr) = &node.falsy {
                    observe_expr(expr, state, captures, effects, safety);
                }
            }
        }
        HirExpr::Call(call) => observe_call(call, state, captures, effects, safety),
        HirExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    HirTableField::Array(value) => {
                        observe_expr(value, state, captures, effects, safety)
                    }
                    HirTableField::Record(record) => {
                        observe_expr(&record.key, state, captures, effects, safety);
                        observe_expr(&record.value, state, captures, effects, safety);
                    }
                }
            }
            if let Some(tail) = &table.trailing_multivalue {
                observe_expr(tail.as_expr(), state, captures, effects, safety);
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
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => {}
    }
}

fn observe_call(
    call: &crate::hir::common::HirCallExpr,
    state: &mut RootState,
    captures: &BTreeMap<HirProtoRef, Vec<HirCapture>>,
    effects: &[ProtoEffects],
    safety: HirExprSafety,
) {
    activate_closures(&call.callee, state, captures, effects, false, safety);
    observe_expr(&call.callee, state, captures, effects, safety);
    for arg in &call.args {
        escape_expr(arg, state, captures, effects, safety);
        observe_expr(arg, state, captures, effects, safety);
    }
}

fn escape_expr(
    expr: &HirExpr,
    state: &mut RootState,
    captures: &BTreeMap<HirProtoRef, Vec<HirCapture>>,
    effects: &[ProtoEffects],
    safety: HirExprSafety,
) {
    let holders = holder_values(expr, state, effects);
    state.escaped.extend(&holders);
    for binding in bindings_in_expr(expr) {
        if state.unknown_collectable.contains(&binding) {
            state.roots.insert(binding, true);
        }
    }
    activate_object_ids(&holders, state, captures, effects, true, safety);
    if let HirExpr::Call(call) = expr {
        activate_closures(&call.callee, state, captures, effects, true, safety);
    }
}

fn activate_closures(
    expr: &HirExpr,
    state: &mut RootState,
    captures: &BTreeMap<HirProtoRef, Vec<HirCapture>>,
    effects: &[ProtoEffects],
    include_returns: bool,
    safety: HirExprSafety,
) {
    let holders = holder_values(expr, state, effects);
    activate_object_ids(&holders, state, captures, effects, include_returns, safety);
}

fn activate_object_ids(
    holders: &BTreeSet<ObjectId>,
    state: &mut RootState,
    captures: &BTreeMap<HirProtoRef, Vec<HirCapture>>,
    effects: &[ProtoEffects],
    include_returns: bool,
    _safety: HirExprSafety,
) {
    let mut pending = holders.iter().copied().collect::<VecDeque<_>>();
    let mut visited = BTreeSet::new();
    while let Some(holder) = pending.pop_front() {
        if !visited.insert(holder) {
            continue;
        }
        match holder {
            ObjectId::Table(_) => {}
            ObjectId::Closure(proto) => {
                let Some(closure_captures) = captures.get(&proto) else {
                    continue;
                };
                let Some(effect) = effects.get(proto.index()) else {
                    continue;
                };
                activate_projected_effect(
                    proto,
                    closure_captures,
                    &effect.writes,
                    &effect.escapes,
                    &effect.returns,
                    &effect.calls,
                    state,
                    effects,
                    include_returns,
                    &mut pending,
                );
            }
            ObjectId::ReturnedClosure { producer, closure } => {
                let Some(closure_captures) = captures.get(&producer) else {
                    continue;
                };
                let Some(effect) = effects.get(producer.index()) else {
                    continue;
                };
                for returned in returned_closures(&effect.returns, closure) {
                    activate_projected_effect(
                        producer,
                        closure_captures,
                        &returned.writes,
                        &returned.escapes,
                        &returned.returns,
                        &returned.calls,
                        state,
                        effects,
                        include_returns,
                        &mut pending,
                    );
                }
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn activate_projected_effect(
    producer: HirProtoRef,
    closure_captures: &[HirCapture],
    writes: &BTreeSet<UpvalueId>,
    escapes: &BTreeSet<UpvalueId>,
    returns: &BTreeSet<EffectValue>,
    calls: &BTreeSet<UpvalueId>,
    state: &mut RootState,
    effects: &[ProtoEffects],
    include_returns: bool,
    pending: &mut VecDeque<ObjectId>,
) {
    for upvalue in writes {
        let Some(capture) = closure_captures.get(upvalue.index()) else {
            continue;
        };
        if capture.mode == HirCaptureMode::ByReference
            && let Some(binding) = binding_from_expr(&capture.value)
        {
            state.roots.insert(binding, true);
            state.unknown_collectable.insert(binding);
        }
    }
    for upvalue in escapes.iter().chain(
        include_returns
            .then(|| returned_upvalues(returns))
            .into_iter()
            .flatten(),
    ) {
        let Some(capture) = closure_captures.get(upvalue.index()) else {
            continue;
        };
        let captured_holders = holder_values(&capture.value, state, effects);
        state.escaped.extend(&captured_holders);
        pending.extend(captured_holders);
        for binding in bindings_in_expr(&capture.value) {
            if state.unknown_collectable.contains(&binding) {
                state.roots.insert(binding, true);
            }
        }
    }
    if include_returns {
        for value in returns {
            let EffectValue::Closure(closure) = value else {
                continue;
            };
            let returned = ObjectId::ReturnedClosure {
                producer,
                closure: closure.proto,
            };
            state.escaped.insert(returned);
            pending.push_back(returned);
            for upvalue in &closure.captures {
                let Some(capture) = closure_captures.get(upvalue.index()) else {
                    continue;
                };
                let captured_holders = holder_values(&capture.value, state, effects);
                state.escaped.extend(&captured_holders);
                pending.extend(captured_holders);
                for binding in bindings_in_expr(&capture.value) {
                    if state.unknown_collectable.contains(&binding) {
                        state.roots.insert(binding, true);
                    }
                }
            }
        }
    }
    for upvalue in calls {
        let Some(capture) = closure_captures.get(upvalue.index()) else {
            continue;
        };
        pending.extend(holder_values(&capture.value, state, effects));
    }
}

fn returned_upvalues(values: &BTreeSet<EffectValue>) -> impl Iterator<Item = &UpvalueId> {
    values.iter().filter_map(|value| match value {
        EffectValue::Upvalue(upvalue) => Some(upvalue),
        EffectValue::Closure(_) => None,
    })
}

fn bindings_in_expr(expr: &HirExpr) -> BTreeSet<Binding> {
    let mut bindings = BTreeSet::new();
    collect_bindings(expr, &mut bindings);
    bindings
}

fn collect_bindings(expr: &HirExpr, bindings: &mut BTreeSet<Binding>) {
    if let Some(binding) = binding_from_expr(expr) {
        bindings.insert(binding);
        return;
    }
    match expr {
        HirExpr::TableAccess(access) => {
            collect_bindings(&access.base, bindings);
            collect_bindings(&access.key, bindings);
        }
        HirExpr::Unary(unary) => collect_bindings(&unary.expr, bindings),
        HirExpr::Binary(binary) => {
            collect_bindings(&binary.lhs, bindings);
            collect_bindings(&binary.rhs, bindings);
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            collect_bindings(&logical.lhs, bindings);
            collect_bindings(&logical.rhs, bindings);
        }
        HirExpr::Call(call) => {
            collect_bindings(&call.callee, bindings);
            for value in &call.args {
                collect_bindings(value, bindings);
            }
        }
        HirExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    HirTableField::Array(value) => collect_bindings(value, bindings),
                    HirTableField::Record(record) => {
                        collect_bindings(&record.key, bindings);
                        collect_bindings(&record.value, bindings);
                    }
                }
            }
            if let Some(tail) = &table.trailing_multivalue {
                collect_bindings(tail.as_expr(), bindings);
            }
        }
        HirExpr::Closure(closure) => {
            for capture in &closure.captures {
                collect_bindings(&capture.value, bindings);
            }
        }
        _ => {}
    }
}

fn binding_from_expr(expr: &HirExpr) -> Option<Binding> {
    match expr {
        HirExpr::ParamRef(param) => Some(Binding::Param(*param)),
        HirExpr::LocalRef(local) => Some(Binding::Local(*local)),
        HirExpr::TempRef(temp) => Some(Binding::Temp(*temp)),
        HirExpr::UpvalueRef(upvalue) => Some(Binding::Upvalue(*upvalue)),
        _ => None,
    }
}

fn binding_from_lvalue(lvalue: &HirLValue) -> Option<Binding> {
    match lvalue {
        HirLValue::Param(param) => Some(Binding::Param(*param)),
        HirLValue::Local(local) => Some(Binding::Local(*local)),
        HirLValue::Temp(temp) => Some(Binding::Temp(*temp)),
        HirLValue::Upvalue(upvalue) => Some(Binding::Upvalue(*upvalue)),
        HirLValue::Global(_) | HirLValue::TableAccess(_) => None,
    }
}

fn closure_captures_in_block(block: &HirBlock) -> BTreeMap<HirProtoRef, Vec<HirCapture>> {
    fn visit_expr(expr: &HirExpr, captures: &mut BTreeMap<HirProtoRef, Vec<HirCapture>>) {
        match expr {
            HirExpr::TableAccess(access) => {
                visit_expr(&access.base, captures);
                visit_expr(&access.key, captures);
            }
            HirExpr::Unary(unary) => visit_expr(&unary.expr, captures),
            HirExpr::Binary(binary) => {
                visit_expr(&binary.lhs, captures);
                visit_expr(&binary.rhs, captures);
            }
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                visit_expr(&logical.lhs, captures);
                visit_expr(&logical.rhs, captures);
            }
            HirExpr::Decision(decision) => {
                for node in &decision.nodes {
                    visit_expr(&node.test, captures);
                    if let crate::hir::common::HirDecisionTarget::Expr(expr) = &node.truthy {
                        visit_expr(expr, captures);
                    }
                    if let crate::hir::common::HirDecisionTarget::Expr(expr) = &node.falsy {
                        visit_expr(expr, captures);
                    }
                }
            }
            HirExpr::Call(call) => {
                visit_expr(&call.callee, captures);
                for arg in &call.args {
                    visit_expr(arg, captures);
                }
            }
            HirExpr::TableConstructor(table) => {
                for field in &table.fields {
                    match field {
                        HirTableField::Array(value) => visit_expr(value, captures),
                        HirTableField::Record(record) => {
                            visit_expr(&record.key, captures);
                            visit_expr(&record.value, captures);
                        }
                    }
                }
                if let Some(tail) = &table.trailing_multivalue {
                    visit_expr(tail.as_expr(), captures);
                }
            }
            HirExpr::Closure(closure) => {
                if let Some(previous) = captures.insert(closure.proto, closure.captures.clone()) {
                    debug_assert_eq!(
                        previous, closure.captures,
                        "a child proto must have one capture shape within its lexical parent"
                    );
                }
                for capture in &closure.captures {
                    visit_expr(&capture.value, captures);
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

    fn visit_block(block: &HirBlock, captures: &mut BTreeMap<HirProtoRef, Vec<HirCapture>>) {
        for stmt in &block.stmts {
            match stmt {
                HirStmt::LocalDecl(decl) => {
                    for value in &decl.values {
                        visit_expr(value, captures);
                    }
                }
                HirStmt::GlobalDecl(decl) => {
                    for value in &decl.values {
                        visit_expr(value, captures);
                    }
                }
                HirStmt::Assign(assign) => {
                    for target in &assign.targets {
                        if let HirLValue::TableAccess(access) = target {
                            visit_expr(&access.base, captures);
                            visit_expr(&access.key, captures);
                        }
                    }
                    for value in &assign.values {
                        visit_expr(value, captures);
                    }
                }
                HirStmt::TableSetList(set) => {
                    visit_expr(&set.base, captures);
                    for value in &set.values {
                        visit_expr(value, captures);
                    }
                }
                HirStmt::ErrNil(err) => visit_expr(&err.value, captures),
                HirStmt::ToBeClosed(tbc) => visit_expr(&tbc.value, captures),
                HirStmt::CallStmt(call) => {
                    visit_expr(&HirExpr::Call(Box::new(call.call.clone())), captures)
                }
                HirStmt::Return(ret) => {
                    for value in &ret.values {
                        visit_expr(value, captures);
                    }
                }
                HirStmt::If(if_stmt) => {
                    visit_expr(&if_stmt.cond, captures);
                    visit_block(&if_stmt.then_block, captures);
                    if let Some(block) = &if_stmt.else_block {
                        visit_block(block, captures);
                    }
                }
                HirStmt::While(while_stmt) => {
                    visit_expr(&while_stmt.cond, captures);
                    visit_block(&while_stmt.body, captures);
                }
                HirStmt::Repeat(repeat) => {
                    visit_block(&repeat.body, captures);
                    visit_expr(&repeat.cond, captures);
                }
                HirStmt::NumericFor(for_) => {
                    visit_expr(&for_.start, captures);
                    visit_expr(&for_.limit, captures);
                    visit_expr(&for_.step, captures);
                    visit_block(&for_.body, captures);
                }
                HirStmt::GenericFor(for_) => {
                    for value in &for_.iterator {
                        visit_expr(value, captures);
                    }
                    visit_block(&for_.body, captures);
                }
                HirStmt::Block(block) => visit_block(block, captures),
                HirStmt::Close(_)
                | HirStmt::Break
                | HirStmt::Continue
                | HirStmt::Goto(_)
                | HirStmt::Label(_) => {}
            }
        }
    }

    let mut captures = BTreeMap::new();
    visit_block(block, &mut captures);
    captures
}

fn collect_proto_effects(module: &HirModule, safety: HirExprSafety) -> Vec<ProtoEffects> {
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
    let entry = graph.entry();
    let mut entries = vec![None::<EffectState>; graph.nodes().len()];
    entries[entry.index()] = Some(EffectState::new(proto));
    let mut pending = VecDeque::from([entry]);
    let mut summary = EffectState::default();

    while let Some(index) = pending.pop_front() {
        let mut output = entries[index.index()]
            .as_ref()
            .expect("queued effect node must be reachable")
            .clone();
        match graph.nodes()[index.index()].kind() {
            HirFlowNodeKind::Exit
            | HirFlowNodeKind::FunctionExit
            | HirFlowNodeKind::UnknownControl
            | HirFlowNodeKind::NumericForDispatch => {}
            HirFlowNodeKind::Stmt(stmt) => update_effect_for_stmt(stmt, &mut output, &context),
            HirFlowNodeKind::GenericForInit(flow) => {
                update_effect_for_stmt(flow.stmt(), &mut output, &context);
                snapshot_generic_for_effect(flow, &mut output, &context);
            }
            HirFlowNodeKind::GenericForDispatch(flow) => {
                dispatch_generic_for_effect(flow, &mut output);
            }
            HirFlowNodeKind::ForBinding(bindings) => {
                write_for_bindings_effect(bindings, &mut output);
            }
            HirFlowNodeKind::RepeatCondition(repeat) => {
                note_effect_escapes(&repeat.cond, &mut output, &context);
            }
        }
        summary.join(&output);
        for &successor in graph.nodes()[index.index()].successors() {
            let changed = if let Some(current) = &mut entries[successor.index()] {
                current.join(&output)
            } else {
                entries[successor.index()] = Some(output.clone());
                true
            };
            if changed {
                pending.push_back(successor);
            }
        }
    }
    summary
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decompile::DecompileDialect;
    use crate::hir::common::{HirGenericFor, HirGlobalRef};

    fn generic_for_block(iterator: HirExpr, binding: LocalId) -> HirBlock {
        HirBlock {
            stmts: vec![HirStmt::GenericFor(Box::new(HirGenericFor {
                bindings: vec![binding],
                iterator: HirValuePack::fixed(vec![iterator]),
                body: HirBlock::default(),
                initializer_transaction: None,
                initializer_roots: Vec::new(),
                dispatch_results: Vec::new(),
            }))],
        }
    }

    #[test]
    fn generic_for_dispatch_uses_the_initializer_snapshot() {
        let iterator = LocalId(0);
        let captured = LocalId(1);
        let child = HirProtoRef(1);
        let later_child = HirProtoRef(2);
        let block = generic_for_block(HirExpr::LocalRef(iterator), LocalId(2));
        let graph =
            HirFlowGraph::for_block(&block, HirExprSafety::for_dialect(DecompileDialect::Lua54))
                .expect("generic-for topology");
        let init = graph
            .nodes()
            .iter()
            .find_map(|node| match node.kind() {
                HirFlowNodeKind::GenericForInit(flow) => Some(flow),
                _ => None,
            })
            .expect("generic-for init event");
        let dispatch = graph
            .nodes()
            .iter()
            .find_map(|node| match node.kind() {
                HirFlowNodeKind::GenericForDispatch(flow) => Some(flow),
                _ => None,
            })
            .expect("generic-for dispatch event");

        let escaped_table = ObjectId::Table(7);
        let mut state = RootState::default();
        state.holders.insert(
            Binding::Local(iterator),
            BTreeSet::from([ObjectId::Closure(child)]),
        );
        state
            .holders
            .insert(Binding::Local(captured), BTreeSet::from([escaped_table]));
        state.unknown_collectable.insert(Binding::Local(captured));
        let mut effects = vec![ProtoEffects::default(); 3];
        effects[child.index()].escapes.insert(UpvalueId(0));
        snapshot_generic_for_root(init, &mut state, &effects);

        state.holders.insert(
            Binding::Local(iterator),
            BTreeSet::from([ObjectId::Closure(later_child)]),
        );
        let captures = BTreeMap::from([(
            child,
            vec![HirCapture {
                mode: HirCaptureMode::ByReference,
                value: HirExpr::LocalRef(captured),
            }],
        )]);
        dispatch_generic_for_root(
            dispatch,
            &mut state,
            &captures,
            &effects,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        );

        assert!(state.escaped.contains(&escaped_table));
        assert_eq!(state.roots.get(&Binding::Local(captured)), Some(&true));
        assert_eq!(init.protocol(), dispatch.protocol());
    }

    #[test]
    fn generic_for_binding_write_replaces_the_old_identity_with_call_results() {
        let binding = LocalId(0);
        let block = generic_for_block(
            HirExpr::GlobalRef(HirGlobalRef { key: "next".into() }),
            binding,
        );
        let graph =
            HirFlowGraph::for_block(&block, HirExprSafety::for_dialect(DecompileDialect::Lua54))
                .expect("generic-for topology");
        let flow = graph
            .nodes()
            .iter()
            .find_map(|node| match node.kind() {
                HirFlowNodeKind::ForBinding(HirForBindings::Generic(flow)) => Some(flow),
                _ => None,
            })
            .expect("generic-for binding event");
        let returned = ObjectId::ReturnedClosure {
            producer: HirProtoRef(1),
            closure: HirProtoRef(2),
        };
        let mut state = RootState::default();
        state.holders.insert(
            Binding::Local(binding),
            BTreeSet::from([ObjectId::Table(9)]),
        );
        state.generic_for.insert(
            flow.protocol(),
            GenericForRootSnapshot {
                returns: BTreeSet::from([returned]),
                ..GenericForRootSnapshot::default()
            },
        );

        write_for_bindings_root(HirForBindings::Generic(flow), &mut state);

        assert_eq!(
            state.holders.get(&Binding::Local(binding)),
            Some(&BTreeSet::from([returned]))
        );
        assert!(state.unknown_collectable.contains(&Binding::Local(binding)));
        assert_eq!(state.roots.get(&Binding::Local(binding)), Some(&true));
    }
}
