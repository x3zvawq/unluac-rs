//! HIR 共享对象流：稳定 binding、aggregate identity、逃逸与 closure effect 的正向传播。
//!
//! 消费 HIR 控制流图及显式 capture，不重建 VM 寄存器。fresh table 的内部存储仅传播
//! 持有关系，真正外部调用/存储才使可达对象逃逸；例如 a={}; b={}; a.x=b 不等于 sink(b)。
//! repeat endpoint 与物理 root overwrite 共同消费此模型和模块入口提供的 child 效果快照，
//! 分别决定生命周期事务；局部消费者不得用 capture 清单合成另一份调用效果。
//! binding 状态只存正向 root 与非空对象集合，缺项就是该域的空值；未知 collectable
//! 单独记录，不能随空 holder 清除。例如 `object=nil` 清除持有者，但不撤销已经发生的逃逸。

mod closure_effects;
pub(super) use closure_effects::collect_proto_effects;

use super::lexical_cfg::{
    FlowRefinement, HirFlowGraph, HirFlowNodeKind, HirFlowProtocolId, HirForBindings,
    HirGenericForFlow,
};
use crate::hir::common::{
    HirBinding, HirBlock, HirCapture, HirCaptureMode, HirExpr, HirLValue, HirProtoRef, HirStmt,
    HirTableField, HirValuePack, TempId, UpvalueId,
};
use crate::hir::expr_safety::HirExprSafety;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) enum ObjectId {
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
pub(super) struct ProtoEffects {
    writes: BTreeSet<UpvalueId>,
    pub(super) escapes: BTreeSet<UpvalueId>,
    returns: BTreeSet<EffectValue>,
    calls: BTreeSet<UpvalueId>,
}

/// 当前模块形状的共享语义快照；子 proto 效果由模块入口计算，任一 pass 改写后失效。
#[derive(Clone, Copy)]
pub(super) struct RootAnalysisContext<'a> {
    pub(super) safety: HirExprSafety,
    pub(super) effects: &'a [ProtoEffects],
}

#[derive(Clone, Default)]
pub(super) struct RootState {
    pub(super) roots: BTreeSet<HirBinding>,
    pub(super) holders: BTreeMap<HirBinding, BTreeSet<ObjectId>>,
    tables: BTreeMap<HirBinding, BTreeSet<ObjectId>>,
    pub(super) unknown_collectable: BTreeSet<HirBinding>,
    pub(super) escaped: BTreeSet<ObjectId>,
    contents: BTreeMap<ObjectId, BTreeSet<ObjectId>>,
    allocations: BTreeSet<ObjectId>,
    pub(super) generic_for: BTreeMap<HirFlowProtocolId, GenericForRootSnapshot>,
}

impl RootState {
    pub(super) fn binding_may_hold_observable_root(&self, binding: HirBinding) -> bool {
        self.roots.contains(&binding)
            || !self
                .binding_holder_values(binding)
                .is_disjoint(&self.escaped)
    }

    fn binding_holder_values(&self, binding: HirBinding) -> BTreeSet<ObjectId> {
        reachable_holders(
            self.holders.get(&binding).cloned().unwrap_or_default(),
            self,
        )
    }
}

#[derive(Clone, Default, Eq, PartialEq)]
pub(super) struct GenericForRootSnapshot {
    callees: BTreeSet<ObjectId>,
    arguments: BTreeSet<ObjectId>,
    pub(super) returns: BTreeSet<ObjectId>,
}

pub(super) fn join_state(current: &mut RootState, incoming: &RootState) -> bool {
    let mut changed = union_set(&mut current.roots, &incoming.roots);
    changed |= extend_map_sets(&mut current.holders, &incoming.holders);
    changed |= extend_map_sets(&mut current.tables, &incoming.tables);
    changed |= union_set(
        &mut current.unknown_collectable,
        &incoming.unknown_collectable,
    );
    changed |= union_set(&mut current.escaped, &incoming.escaped);
    changed |= extend_map_sets(&mut current.contents, &incoming.contents);
    changed |= union_set(&mut current.allocations, &incoming.allocations);
    let protocol_count = current.generic_for.len();
    for (&protocol, snapshot) in &incoming.generic_for {
        let current_snapshot = current.generic_for.entry(protocol).or_default();
        changed |= union_set(&mut current_snapshot.callees, &snapshot.callees);
        changed |= union_set(&mut current_snapshot.arguments, &snapshot.arguments);
        changed |= union_set(&mut current_snapshot.returns, &snapshot.returns);
    }
    changed || protocol_count != current.generic_for.len()
}

fn union_set<T: Clone + Ord>(target: &mut BTreeSet<T>, source: &BTreeSet<T>) -> bool {
    let before = target.len();
    target.extend(source.iter().cloned());
    before != target.len()
}

fn extend_map_sets<K: Copy + Ord, V: Clone + Ord>(
    target: &mut BTreeMap<K, BTreeSet<V>>,
    source: &BTreeMap<K, BTreeSet<V>>,
) -> bool {
    let before = target.len();
    let mut changed = false;
    for (&key, values) in source {
        changed |= union_set(target.entry(key).or_default(), values);
    }
    changed || before != target.len()
}
pub(super) fn snapshot_generic_for_root(
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

pub(super) fn dispatch_generic_for_root(
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

pub(super) fn write_for_bindings_root(bindings: HirForBindings<'_>, state: &mut RootState) {
    match bindings {
        HirForBindings::Numeric(local) => {
            BindingValue::default().install(HirBinding::Local(local), state);
        }
        HirForBindings::Generic(flow) => {
            let returned = state
                .generic_for
                .get(&flow.protocol())
                .map(|snapshot| snapshot.returns.clone())
                .unwrap_or_default();
            for &local in &flow.for_stmt().bindings {
                BindingValue {
                    holders: returned.clone(),
                    unknown: true,
                    root: true,
                    ..BindingValue::default()
                }
                .install(HirBinding::Local(local), state);
            }
        }
    }
}

pub(super) fn update_state_for_stmt(
    stmt: &HirStmt,
    state: &mut RootState,
    captures: &BTreeMap<HirProtoRef, Vec<HirCapture>>,
    effects: &[ProtoEffects],
    safety: HirExprSafety,
) {
    observe_stmt(stmt, state, captures, effects, safety);
    match stmt {
        HirStmt::LocalRootRelease(local) => {
            BindingValue::default().install(HirBinding::Local(*local), state);
        }
        HirStmt::LocalDecl(decl) => assign_bindings(
            decl.bindings.iter().copied().map(HirBinding::Local),
            &decl.values,
            state,
            effects,
            safety,
        ),
        HirStmt::Assign(assign) => {
            let values = assign
                .targets
                .iter()
                .enumerate()
                .map(|(index, target)| {
                    binding_from_lvalue(target).map(|binding| {
                        (
                            binding,
                            BindingValue::resolve(
                                adjusted_value(&assign.values, index),
                                state,
                                effects,
                                safety,
                            ),
                        )
                    })
                })
                .collect::<Vec<_>>();
            for (index, (target, value)) in assign.targets.iter().zip(values).enumerate() {
                if matches!(target, HirLValue::Global(_) | HirLValue::Upvalue(_))
                    && let Some(value) = adjusted_value(&assign.values, index)
                {
                    escape_expr(value, state, captures, effects, safety);
                }
                if let Some((binding, value)) = value {
                    value.install(binding, state);
                } else if let HirLValue::TableAccess(access) = target {
                    store_table(
                        &access.base,
                        Some(&access.key),
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
                store_table(
                    &set.base,
                    None,
                    Some(value),
                    state,
                    captures,
                    effects,
                    safety,
                );
            }
        }
        _ => {}
    }
}

fn assign_bindings(
    bindings: impl Iterator<Item = HirBinding>,
    values: &HirValuePack,
    state: &mut RootState,
    effects: &[ProtoEffects],
    safety: HirExprSafety,
) {
    let values = bindings
        .enumerate()
        .map(|(index, binding)| {
            (
                binding,
                BindingValue::resolve(adjusted_value(values, index), state, effects, safety),
            )
        })
        .collect::<Vec<_>>();
    for (binding, value) in values {
        value.install(binding, state);
    }
}

/// 同一次并行赋值在写入前解析所有 RHS，只保留目标值事实，避免复制完整对象图。
/// 例如 `a,b=b,a` 的两个值都来自旧状态；表存储与捕获效果仍按语句 owner 的顺序处理。
#[derive(Default)]
struct BindingValue {
    holders: BTreeSet<ObjectId>,
    tables: BTreeSet<ObjectId>,
    unknown: bool,
    root: bool,
}

impl BindingValue {
    fn resolve(
        value: Option<&HirExpr>,
        state: &RootState,
        effects: &[ProtoEffects],
        safety: HirExprSafety,
    ) -> Self {
        Self {
            holders: value.map_or_else(BTreeSet::new, |value| holder_values(value, state, effects)),
            tables: value.map_or_else(BTreeSet::new, |value| table_values(value, state)),
            unknown: adjusted_value_may_be_unknown(value, state, safety),
            root: value.is_some_and(|value| expr_may_root(value, state, safety)),
        }
    }

    fn install(self, binding: HirBinding, state: &mut RootState) {
        for (map, objects) in [
            (&mut state.holders, self.holders),
            (&mut state.tables, self.tables),
        ] {
            if objects.is_empty() {
                map.remove(&binding);
            } else {
                map.insert(binding, objects);
            }
        }
        if self.unknown {
            state.unknown_collectable.insert(binding);
        } else {
            state.unknown_collectable.remove(&binding);
        }
        if self.root {
            state.roots.insert(binding);
        } else {
            state.roots.remove(&binding);
        }
    }
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
        HirExpr::ParamRef(id) => state.unknown_collectable.contains(&HirBinding::Param(*id)),
        HirExpr::LocalRef(id) => state.unknown_collectable.contains(&HirBinding::Local(*id)),
        HirExpr::TempRef(id) => state.unknown_collectable.contains(&HirBinding::Temp(*id)),
        HirExpr::UpvalueRef(id) => state
            .unknown_collectable
            .contains(&HirBinding::Upvalue(*id)),
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_may_be_unknown(&logical.lhs, state, safety)
                || expr_may_be_unknown(&logical.rhs, state, safety)
        }
        HirExpr::TableConstructor(_) | HirExpr::Closure(_) => false,
        _ => !safety.result_is_gc_inert(expr),
    }
}

fn expr_may_root(expr: &HirExpr, state: &RootState, safety: HirExprSafety) -> bool {
    if let Some(binding) = HirBinding::from_expr(expr) {
        return state.binding_may_hold_observable_root(binding);
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

/// 对象持有关系按 allocation identity 保存，不能随某个临时 binding 被覆盖而丢失。
fn holder_values(
    expr: &HirExpr,
    state: &RootState,
    effects: &[ProtoEffects],
) -> BTreeSet<ObjectId> {
    reachable_holders(direct_holder_values(expr, state, effects), state)
}

fn reachable_holders(mut holders: BTreeSet<ObjectId>, state: &RootState) -> BTreeSet<ObjectId> {
    let mut pending: Vec<_> = holders.iter().copied().collect();
    while let Some(object) = pending.pop() {
        if let Some(contents) = state.contents.get(&object) {
            for &child in contents {
                if holders.insert(child) {
                    pending.push(child);
                }
            }
        }
    }
    holders
}

fn direct_holder_values(
    expr: &HirExpr,
    state: &RootState,
    effects: &[ProtoEffects],
) -> BTreeSet<ObjectId> {
    if let Some(binding) = HirBinding::from_expr(expr) {
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
                let effect = &effects[proto.index()];
                (proto, &effect.returns)
            }
            ObjectId::ReturnedClosure { producer, closure } => {
                let effect = &effects[producer.index()];
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
    if let Some(binding) = HirBinding::from_expr(expr) {
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
    base: &HirExpr,
    key: Option<&HirExpr>,
    value: Option<&HirExpr>,
    state: &mut RootState,
    captures: &BTreeMap<HirProtoRef, Vec<HirCapture>>,
    effects: &[ProtoEffects],
    safety: HirExprSafety,
) {
    let tables = table_values(base, state);
    let base_has_unknown = bindings_in_expr(base)
        .iter()
        .any(|binding| state.unknown_collectable.contains(binding));
    let is_known_plain =
        !tables.is_empty() && tables.is_disjoint(&state.escaped) && !base_has_unknown;
    if !is_known_plain {
        escape_expr(base, state, captures, effects, safety);
        if let Some(key) = key {
            escape_expr(key, state, captures, effects, safety);
        }
        if let Some(value) = value {
            escape_expr(value, state, captures, effects, safety);
        }
        return;
    }

    let mut stored = key.map_or_else(BTreeSet::new, |key| holder_values(key, state, effects));
    if let Some(value) = value {
        stored.extend(holder_values(value, state, effects));
    }
    let may_root = key.is_some_and(|key| expr_may_root(key, state, safety))
        || value.is_some_and(|value| expr_may_root(value, state, safety));
    let aliases = state
        .tables
        .iter()
        .filter_map(|(&binding, values)| (!values.is_disjoint(&tables)).then_some(binding))
        .collect::<Vec<_>>();
    for table in tables {
        state.contents.entry(table).or_default().extend(&stored);
    }
    for binding in aliases {
        if !stored.is_empty() {
            state.holders.entry(binding).or_default().extend(&stored);
        }
        if may_root {
            state.roots.insert(binding);
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
        HirStmt::LocalRootRelease(_) => {}
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

pub(super) fn observe_expr(
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
            let tables = table_values(&access.base, state);
            if tables.is_empty()
                || !tables.is_disjoint(&state.escaped)
                || expr_may_be_unknown(&access.base, state, safety)
            {
                // 未知接收者的 __index 可把 key/receiver 留给外部；普通读取不等于无逃逸。
                escape_expr(&access.base, state, captures, effects, safety);
                escape_expr(&access.key, state, captures, effects, safety);
            }
        }
        HirExpr::Unary(unary) => {
            observe_expr(&unary.expr, state, captures, effects, safety);
            if safety.unary_operator_may_observe_gc_roots(unary.op) {
                escape_expr(&unary.expr, state, captures, effects, safety);
            }
        }
        HirExpr::Binary(binary) => {
            observe_expr(&binary.lhs, state, captures, effects, safety);
            observe_expr(&binary.rhs, state, captures, effects, safety);
            if safety.binary_operator_may_observe_gc_roots(binary.op, &binary.lhs, &binary.rhs) {
                escape_expr(&binary.lhs, state, captures, effects, safety);
                escape_expr(&binary.rhs, state, captures, effects, safety);
            }
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
            let object = ObjectId::Table(std::ptr::from_ref(table.as_ref()).addr());
            state.allocations.insert(object);
            let mut contents = holder_values(expr, state, effects);
            contents.remove(&object);
            state.contents.entry(object).or_default().extend(contents);
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
            state.roots.insert(binding);
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
                let effect = &effects[proto.index()];
                activate_projected_effect(
                    proto,
                    closure_captures,
                    &effect.writes,
                    &effect.escapes,
                    &effect.returns,
                    &effect.calls,
                    state,
                    include_returns,
                    &mut pending,
                );
            }
            ObjectId::ReturnedClosure { producer, closure } => {
                let Some(closure_captures) = captures.get(&producer) else {
                    continue;
                };
                let effect = &effects[producer.index()];
                for returned in returned_closures(&effect.returns, closure) {
                    activate_projected_effect(
                        producer,
                        closure_captures,
                        &returned.writes,
                        &returned.escapes,
                        &returned.returns,
                        &returned.calls,
                        state,
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
    include_returns: bool,
    pending: &mut VecDeque<ObjectId>,
) {
    for upvalue in writes {
        let Some(capture) = closure_captures.get(upvalue.index()) else {
            continue;
        };
        if capture.mode == HirCaptureMode::ByReference {
            state.roots.insert(capture.binding);
            state.unknown_collectable.insert(capture.binding);
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
        let captured_holders = state.binding_holder_values(capture.binding);
        state.escaped.extend(&captured_holders);
        pending.extend(captured_holders);
        if state.unknown_collectable.contains(&capture.binding) {
            state.roots.insert(capture.binding);
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
                let captured_holders = state.binding_holder_values(capture.binding);
                state.escaped.extend(&captured_holders);
                pending.extend(captured_holders);
                if state.unknown_collectable.contains(&capture.binding) {
                    state.roots.insert(capture.binding);
                }
            }
        }
    }
    for upvalue in calls {
        let Some(capture) = closure_captures.get(upvalue.index()) else {
            continue;
        };
        pending.extend(state.binding_holder_values(capture.binding));
    }
}

fn returned_upvalues(values: &BTreeSet<EffectValue>) -> impl Iterator<Item = &UpvalueId> {
    values.iter().filter_map(|value| match value {
        EffectValue::Upvalue(upvalue) => Some(upvalue),
        EffectValue::Closure(_) => None,
    })
}

fn bindings_in_expr(expr: &HirExpr) -> BTreeSet<HirBinding> {
    struct Bindings(BTreeSet<HirBinding>);
    impl crate::hir::visit::HirVisitor for Bindings {
        fn visit_expr(&mut self, expr: &HirExpr) {
            if let Some(binding) = HirBinding::from_expr(expr) {
                self.0.insert(binding);
            }
        }
    }
    let mut bindings = Bindings(BTreeSet::new());
    crate::hir::visit::visit_expr(expr, &mut bindings);
    bindings.0
}

pub(super) fn binding_from_lvalue(lvalue: &HirLValue) -> Option<HirBinding> {
    match lvalue {
        HirLValue::Param(param) => Some(HirBinding::Param(*param)),
        HirLValue::Local(local) => Some(HirBinding::Local(*local)),
        HirLValue::Temp(temp) => Some(HirBinding::Temp(*temp)),
        HirLValue::Upvalue(upvalue) => Some(HirBinding::Upvalue(*upvalue)),
        HirLValue::Global(_) | HirLValue::TableAccess(_) => None,
    }
}

pub(super) fn closure_captures_in_block(
    block: &HirBlock,
) -> BTreeMap<HirProtoRef, Vec<HirCapture>> {
    closure_captures_in_stmts(&block.stmts)
}

fn closure_captures_in_stmts(stmts: &[HirStmt]) -> BTreeMap<HirProtoRef, Vec<HirCapture>> {
    #[derive(Default)]
    struct CaptureCollector(BTreeMap<HirProtoRef, Vec<HirCapture>>);

    impl crate::hir::visit::HirVisitor for CaptureCollector {
        fn visit_expr(&mut self, expr: &HirExpr) {
            if let HirExpr::Closure(closure) = expr
                && let Some(previous) = self.0.insert(closure.proto, closure.captures.clone())
            {
                debug_assert_eq!(
                    previous, closure.captures,
                    "a child proto must have one capture shape within its lexical parent"
                );
            }
        }
    }

    let mut captures = CaptureCollector::default();
    crate::hir::visit::visit_stmts(stmts, &mut captures);
    captures.0
}

/// 当前不可变语句切片内 allocation 到观察点的正向事实；指针只作本次分析的 site key。
/// 缺失或不可达状态不签发未逃逸证明。调用方仍拥有物理 home 与删除事务。
#[derive(Default)]
pub(super) struct AllocationEscapeFacts {
    unescaped: BTreeMap<usize, BTreeSet<ObjectId>>,
}

impl AllocationEscapeFacts {
    pub(super) fn analyze(
        stmts: &[HirStmt],
        context: RootAnalysisContext<'_>,
        opaque: &BTreeSet<TempId>,
    ) -> Self {
        let RootAnalysisContext { safety, effects } = context;
        let Ok(graph) = HirFlowGraph::for_stmts(stmts, safety) else {
            return Self::default();
        };
        if graph.has_reachable_unresolved_goto() {
            return Self::default();
        }
        let captures = closure_captures_in_stmts(stmts);
        struct ExternalBindings(BTreeSet<HirBinding>);
        impl crate::hir::visit::HirVisitor for ExternalBindings {
            fn visit_expr(&mut self, expr: &HirExpr) {
                if let Some(binding) = HirBinding::from_expr(expr) {
                    self.0.insert(binding);
                }
            }
        }
        let mut external = ExternalBindings(BTreeSet::new());
        crate::hir::visit::visit_stmts(stmts, &mut external);
        let initial = RootState {
            unknown_collectable: external.0,
            ..RootState::default()
        };
        let unescaped = graph.solve_forward(
            initial,
            join_state,
            |_, kind, state| {
                transfer_overwrite_node(kind, state, &captures, effects, safety, opaque);
                let HirFlowNodeKind::Stmt(stmt) = kind else {
                    return None;
                };
                let escaped = reachable_holders(state.escaped.clone(), state);
                Some((
                    std::ptr::from_ref(stmt).addr(),
                    state
                        .allocations
                        .iter()
                        .copied()
                        .filter(|object| {
                            reachable_holders(BTreeSet::from([*object]), state)
                                .is_disjoint(&escaped)
                        })
                        .collect(),
                ))
            },
            |_expr, _truthy, _state| FlowRefinement::Unchanged,
        );
        Self {
            unescaped: unescaped.into_iter().flatten().flatten().collect(),
        }
    }

    pub(super) fn proves_unescaped(&self, allocation_site: usize, stmt: &HirStmt) -> bool {
        self.unescaped
            .get(&std::ptr::from_ref(stmt).addr())
            .is_some_and(|objects| objects.contains(&ObjectId::Table(allocation_site)))
    }
}

pub(super) fn transfer_root_node(
    kind: HirFlowNodeKind<'_>,
    state: &mut RootState,
    captures: &BTreeMap<HirProtoRef, Vec<HirCapture>>,
    effects: &[ProtoEffects],
    safety: HirExprSafety,
) {
    match kind {
        HirFlowNodeKind::Stmt(stmt) => {
            update_state_for_stmt(stmt, state, captures, effects, safety);
        }
        HirFlowNodeKind::GenericForInit(flow) => {
            update_state_for_stmt(flow.stmt(), state, captures, effects, safety);
            snapshot_generic_for_root(flow, state, effects);
        }
        HirFlowNodeKind::GenericForDispatch(flow) => {
            dispatch_generic_for_root(flow, state, captures, effects, safety)
        }
        HirFlowNodeKind::ForBinding(bindings) => write_for_bindings_root(bindings, state),
        HirFlowNodeKind::RepeatCondition(repeat) => {
            observe_expr(&repeat.cond, state, captures, effects, safety)
        }
        HirFlowNodeKind::UnknownControl => {
            state.escaped.extend(&state.allocations);
        }
        HirFlowNodeKind::Exit
        | HirFlowNodeKind::FunctionExit
        | HirFlowNodeKind::NumericForDispatch => {}
    }
}

fn transfer_overwrite_node(
    kind: HirFlowNodeKind<'_>,
    state: &mut RootState,
    captures: &BTreeMap<HirProtoRef, Vec<HirCapture>>,
    effects: &[ProtoEffects],
    safety: HirExprSafety,
    opaque: &BTreeSet<TempId>,
) {
    transfer_root_node(kind, state, captures, effects, safety);
    if let HirFlowNodeKind::Stmt(stmt) = kind {
        if let HirStmt::LocalDecl(decl) = stmt {
            for local in &decl.bindings {
                escape_expr(&HirExpr::LocalRef(*local), state, captures, effects, safety);
            }
        }
        if let HirStmt::Assign(assign) = stmt {
            for target in &assign.targets {
                if let HirLValue::Temp(temp) = target
                    && opaque.contains(temp)
                {
                    escape_expr(&HirExpr::TempRef(*temp), state, captures, effects, safety);
                }
            }
        }
    }
}
