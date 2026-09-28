//! HIR 共用的 binding、对象持有、逃逸与闭包效果分析。
//!
//! 消费共享 HIR 图及当前 capture 摘要，为构造器和 repeat 端点提供正向状态；
//! 物理根覆盖终点由 root_lifetimes 持有。

mod closure_effects;
mod fields;
mod return_values;
pub(super) use return_values::ReturnValueFacts;
pub(super) use return_values::gc_inert_bindings;

/// 一个不可变 HIR 模块快照同时发布 may-capture 效果和正常返回值；两者的证明域不同。
/// constructor/root 消费结果查询，不能把 may-holder 子集当成完整 callee 身份。
pub(super) struct ModuleEffects {
    protos: Vec<ProtoEffects>,
    pub(super) values: ReturnValueFacts,
}

pub(super) fn collect_proto_effects(
    module: &crate::hir::HirModule,
    safety: HirExprSafety,
    dialect: crate::decompile::DecompileDialect,
) -> ModuleEffects {
    let mut captures = module
        .protos
        .iter()
        .map(|proto| closure_captures_in_block(&proto.body))
        .collect::<Vec<_>>();
    let mut facts = ModuleEffects {
        protos: module
            .protos
            .iter()
            .map(|proto| ProtoEffects {
                writes: proto.mutable_upvalues.clone(),
                ..ProtoEffects::default()
            })
            .collect(),
        values: ReturnValueFacts::new(module, &captures),
    };
    let mut required = vec![false; module.protos.len()];
    for child in module.protos.iter().flat_map(|proto| &proto.children) {
        required[child.index()] = true;
    }
    // arena 父先子后；两域共用一次 child-first 调度和当前 proto 的不可变控制流快照。
    let mut value_flows = Vec::new();
    for index in (0..module.protos.len()).rev() {
        let proto = &module.protos[index];
        if !required[index] && proto.children.is_empty() {
            continue;
        }
        let flow = ProtoFlowFacts::new(proto, safety, std::mem::take(&mut captures[index]));
        if required[index] && !(proto.upvalues.is_empty() && proto.children.is_empty()) {
            facts.protos[index] = closure_effects::collect_effect_state(&flow, &facts.protos);
        }
        facts.values.analyze_proto(&flow);
        value_flows.push(flow);
    }
    for flow in &value_flows {
        facts.values.finalize_calls(flow);
    }
    // PUC/LuaJIT 的 debug.setlocal 可改写未捕获形参；封闭调用集并不关闭这个入口。
    if dialect == crate::decompile::DecompileDialect::Luau
        && facts.values.install_closed_parameter_entries(module)
    {
        for flow in &value_flows {
            facts.values.analyze_proto(flow);
        }
        for flow in &value_flows {
            facts.values.finalize_calls(flow);
        }
    }
    facts
}
pub(super) use fields::PrivateAllocationFacts;

use super::lexical_cfg::{
    HirFlowGraph, HirFlowNodeKind, HirFlowProtocolId, HirForBindings, HirGenericForFlow,
};
use crate::hir::common::{
    HirBinding, HirBlock, HirCapture, HirCaptureMode, HirExpr, HirLValue, HirProto, HirProtoRef,
    HirStmt, HirTableConstructor, HirTableField, HirValuePack, UpvalueId,
};
use crate::hir::expr_safety::HirExprSafety;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

/// 两个值域求解同一只读 proto 时共享 topology、直接读取需求和捕获身份。
/// 例如局部 f 的 capture 效果与调用结果都使用这一图；求解状态仍各自拥有，不混淆
/// may-origin 的 bottom 和正常值的 UNKNOWN。快照只活过当前 proto 的两次求解。
struct ProtoFlowFacts<'hir> {
    proto: &'hir HirProto,
    safety: HirExprSafety,
    graph: HirFlowGraph<'hir>,
    live_out: Vec<BTreeSet<HirBinding>>,
    captures: ClosureCaptures<'hir>,
    reference_cells: BTreeSet<HirBinding>,
}

impl<'hir> ProtoFlowFacts<'hir> {
    fn new(proto: &'hir HirProto, safety: HirExprSafety, captures: ClosureCaptures<'hir>) -> Self {
        let graph = HirFlowGraph::for_block(&proto.body, safety)
            .expect("HIR labels must be valid before module value analysis");
        let live_out = graph.binding_live_out();
        let reference_cells = captures
            .values()
            .flat_map(|captures| captures.iter())
            .filter(|capture| capture.mode == HirCaptureMode::ByReference)
            .map(|capture| capture.binding)
            .collect();
        Self {
            proto,
            safety,
            graph,
            live_out,
            captures,
            reference_cells,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) enum ObjectId {
    Table(usize),
    Closure(HirProtoRef),
    ReturnedClosure {
        producer: HirProtoRef,
        closure: HirProtoRef,
    },
}

impl ObjectId {
    fn table(table: &HirTableConstructor) -> Self {
        Self::Table(std::ptr::from_ref(table).addr())
    }
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
    pub(super) effects: &'a ModuleEffects,
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
    // 构造窗口需要确定字段身份；物理根覆盖分析仍使用原来的 may-holder 投影。
    fields: Option<fields::FieldFacts>,
    pub(super) generic_for: BTreeMap<HirFlowProtocolId, GenericForRootSnapshot>,
}

impl RootState {
    fn publish_objects(&mut self, objects: &BTreeSet<ObjectId>) {
        self.escaped.extend(objects);
        if let Some(fields) = &mut self.fields {
            for &object in objects {
                fields.mark_observed(object);
            }
        }
    }

    fn store_objects(&mut self, owner: ObjectId, children: &BTreeSet<ObjectId>) {
        self.contents.entry(owner).or_default().extend(children);
        if let Some(fields) = &mut self.fields {
            fields.record_contents(owner, children);
        }
    }

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
    effects: &ModuleEffects,
) {
    let Some(callee) = flow.for_stmt().iterator.result_source(0) else {
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
    captures: &ClosureCaptures<'_>,
    effects: &ModuleEffects,
    safety: HirExprSafety,
) {
    let Some(snapshot) = state.generic_for.get(&flow.protocol()).cloned() else {
        return;
    };
    activate_object_ids(&snapshot.callees, state, captures, effects, false, safety);
    state.publish_objects(&snapshot.arguments);
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
    captures: &ClosureCaptures<'_>,
    effects: &ModuleEffects,
    safety: HirExprSafety,
) {
    // 多目标赋值的表 RHS 来自统一旧快照；当前确定字段投影不跨这种事务签发事实。
    // may-holder 历史继续保留，故失效只扩大构造窗口的拒绝范围。
    if matches!(stmt, HirStmt::Assign(assign) if assign.targets.len() > 1
        && assign.targets.iter().any(|target| matches!(target, HirLValue::TableAccess(_))))
        && let Some(fields) = &mut state.fields
    {
        fields.invalidate_values();
    }
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
                    HirBinding::from_lvalue(target).map(|binding| {
                        (
                            binding,
                            BindingValue::resolve(
                                assign.values.result_source(index),
                                effects.values.pack_slot(&assign.values, index),
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
                    && let Some(value) = assign.values.result_source(index)
                {
                    escape_expr(value, state, captures, effects, safety);
                }
                if let Some((binding, value)) = value {
                    value.install(binding, state);
                } else if let HirLValue::TableAccess(access) = target {
                    store_table(
                        &access.base,
                        Some(&access.key),
                        assign.values.result_source(index),
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
            for (index, value) in (&set.values).into_iter().enumerate() {
                store_table(
                    &set.base,
                    Some(&HirExpr::Integer(i64::from(set.start_index) + index as i64)),
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
    effects: &ModuleEffects,
    safety: HirExprSafety,
) {
    let values = bindings
        .enumerate()
        .map(|(index, binding)| {
            (
                binding,
                BindingValue::resolve(
                    values.result_source(index),
                    effects.values.pack_slot(values, index),
                    state,
                    effects,
                    safety,
                ),
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
    known: Option<fields::KnownValue>,
}

impl BindingValue {
    fn resolve(
        value: Option<&HirExpr>,
        result: crate::value_semantics::results::LuaValueFacts,
        state: &RootState,
        effects: &ModuleEffects,
        safety: HirExprSafety,
    ) -> Self {
        Self {
            holders: value.map_or_else(BTreeSet::new, |value| {
                if state.fields.is_some() {
                    direct_holder_values(value, state, effects)
                } else {
                    holder_values(value, state, effects)
                }
            }),
            tables: value.map_or_else(BTreeSet::new, |value| table_values(value, state)),
            // tail 的第 n 槽已在 pack owner 投影；不能再用同一个 Call 表达式的首槽
            // 否定这里的资源可能性，例如 f() 返回 `1, object`。
            unknown: !result.is_gc_inert()
                && (matches!(value, Some(HirExpr::Call(_)))
                    || adjusted_value_may_be_unknown(value, state, effects, safety)),
            root: !result.is_gc_inert()
                && value.is_some_and(|value| {
                    matches!(value, HirExpr::Call(_))
                        || expr_may_root(value, state, effects, safety)
                }),
            known: fields::known_value(value.unwrap_or(&HirExpr::Nil), state),
        }
    }

    fn install(self, binding: HirBinding, state: &mut RootState) {
        // 引用cell可能早在其值为nil时就经closure公开；随后写入的新对象不能继承
        // 当时的未逃逸状态。此发布仅服务完整构造窗口，默认may-root投影保持原策略。
        if state
            .fields
            .as_ref()
            .is_some_and(|fields| fields.publishes_binding(binding))
        {
            state.publish_objects(&reachable_holders(self.holders.clone(), state));
        }
        if let Some(fields) = &mut state.fields {
            fields.install(binding, self.known);
        }
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

fn adjusted_value_may_be_unknown(
    value: Option<&HirExpr>,
    state: &RootState,
    effects: &ModuleEffects,
    safety: HirExprSafety,
) -> bool {
    value.is_some_and(|value| expr_may_be_unknown(value, state, effects, safety))
}

fn expr_may_be_unknown(
    expr: &HirExpr,
    state: &RootState,
    effects: &ModuleEffects,
    safety: HirExprSafety,
) -> bool {
    if fields::known_value(expr, state).is_some() {
        return false;
    }
    match expr {
        HirExpr::ParamRef(id) => state.unknown_collectable.contains(&HirBinding::Param(*id)),
        HirExpr::LocalRef(id) => state.unknown_collectable.contains(&HirBinding::Local(*id)),
        HirExpr::TempRef(id) => state.unknown_collectable.contains(&HirBinding::Temp(*id)),
        HirExpr::UpvalueRef(id) => state
            .unknown_collectable
            .contains(&HirBinding::Upvalue(*id)),
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_may_be_unknown(&logical.lhs, state, effects, safety)
                || expr_may_be_unknown(&logical.rhs, state, effects, safety)
        }
        HirExpr::TableConstructor(_) | HirExpr::Closure(_) => false,
        _ => !safety.result_is_gc_inert(expr) && !effects.values.value_facts(expr).is_gc_inert(),
    }
}

fn expr_may_root(
    expr: &HirExpr,
    state: &RootState,
    effects: &ModuleEffects,
    safety: HirExprSafety,
) -> bool {
    if let Some(value) = fields::known_value(expr, state) {
        return value
            .object()
            .is_some_and(|object| state.escaped.contains(&object));
    }
    if let Some(binding) = HirBinding::from_expr(expr) {
        return state.binding_may_hold_observable_root(binding);
    }
    match expr {
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_may_root(&logical.lhs, state, effects, safety)
                || expr_may_root(&logical.rhs, state, effects, safety)
        }
        HirExpr::TableConstructor(table) => table.fields.iter().any(|field| match field {
            HirTableField::Array(value) => expr_may_root(value, state, effects, safety),
            HirTableField::Record(record) => {
                expr_may_root(&record.key, state, effects, safety)
                    || expr_may_root(&record.value, state, effects, safety)
            }
        }),
        HirExpr::Closure(_) => false,
        _ => !safety.result_is_gc_inert(expr) && !effects.values.value_facts(expr).is_gc_inert(),
    }
}

/// 对象持有关系按 allocation identity 保存，不能随某个临时 binding 被覆盖而丢失。
fn holder_values(expr: &HirExpr, state: &RootState, effects: &ModuleEffects) -> BTreeSet<ObjectId> {
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
    effects: &ModuleEffects,
) -> BTreeSet<ObjectId> {
    if let Some(value) = fields::known_value(expr, state) {
        return value.object().into_iter().collect();
    }
    if let Some(binding) = HirBinding::from_expr(expr) {
        return state.holders.get(&binding).cloned().unwrap_or_default();
    }
    match expr {
        HirExpr::Closure(closure) => BTreeSet::from([ObjectId::Closure(closure.proto)]),
        HirExpr::TableConstructor(table) => {
            let mut holders = BTreeSet::from([ObjectId::table(table)]);
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
        HirExpr::TableAccess(access) if state.fields.is_some() => {
            direct_holder_values(&access.base, state, effects)
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
    effects: &ModuleEffects,
) -> BTreeSet<ObjectId> {
    let mut returned = BTreeSet::new();
    for &callee in callees {
        let (producer, returns) = match callee {
            ObjectId::Closure(proto) => {
                let effect = &effects.protos[proto.index()];
                (proto, &effect.returns)
            }
            ObjectId::ReturnedClosure { producer, closure } => {
                let effect = &effects.protos[producer.index()];
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
    if let Some(value) = fields::known_value(expr, state) {
        return value.object().into_iter().collect();
    }
    if let Some(binding) = HirBinding::from_expr(expr) {
        return state.tables.get(&binding).cloned().unwrap_or_default();
    }
    match expr {
        HirExpr::TableConstructor(table) => BTreeSet::from([ObjectId::table(table)]),
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
    captures: &ClosureCaptures<'_>,
    effects: &ModuleEffects,
    safety: HirExprSafety,
) {
    let tables = table_values(base, state);
    let base_has_unknown = crate::hir::visit::any_expr(base, &mut |expr| {
        HirBinding::from_expr(expr)
            .is_some_and(|binding| state.unknown_collectable.contains(&binding))
    });
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

    fields::store(&tables, key, value, state);

    let project_holders = |value| {
        if state.fields.is_some() {
            direct_holder_values(value, state, effects)
        } else {
            holder_values(value, state, effects)
        }
    };
    let mut stored = key.map_or_else(BTreeSet::new, project_holders);
    if let Some(value) = value {
        stored.extend(project_holders(value));
    }
    let may_root = key.is_some_and(|key| expr_may_root(key, state, effects, safety))
        || value.is_some_and(|value| expr_may_root(value, state, effects, safety));
    let aliases = if state.fields.is_none() {
        state
            .tables
            .iter()
            .filter_map(|(&binding, values)| (!values.is_disjoint(&tables)).then_some(binding))
            .collect::<Vec<_>>()
    } else {
        Vec::new()
    };
    for table in tables {
        state.store_objects(table, &stored);
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
    captures: &ClosureCaptures<'_>,
    effects: &ModuleEffects,
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
    captures: &ClosureCaptures<'_>,
    effects: &ModuleEffects,
    safety: HirExprSafety,
) {
    for value in pack {
        observe_expr(value, state, captures, effects, safety);
    }
}

pub(super) fn observe_expr(
    expr: &HirExpr,
    state: &mut RootState,
    captures: &ClosureCaptures<'_>,
    effects: &ModuleEffects,
    safety: HirExprSafety,
) {
    match expr {
        HirExpr::TableAccess(access) => {
            observe_expr(&access.base, state, captures, effects, safety);
            observe_expr(&access.key, state, captures, effects, safety);
            let tables = table_values(&access.base, state);
            if tables.is_empty()
                || !tables.is_disjoint(&state.escaped)
                || expr_may_be_unknown(&access.base, state, effects, safety)
            {
                // 未知接收者的 __index 可把 key/receiver 留给外部；普通读取不等于无逃逸。
                escape_expr(&access.base, state, captures, effects, safety);
                escape_expr(&access.key, state, captures, effects, safety);
            }
        }
        HirExpr::Unary(unary) => {
            observe_expr(&unary.expr, state, captures, effects, safety);
            if safety.unary_operator_may_observe_gc_roots(unary.op)
                && !fields::operator_is_plain(expr, state)
            {
                escape_expr(&unary.expr, state, captures, effects, safety);
            }
        }
        HirExpr::Binary(binary) => {
            observe_expr(&binary.lhs, state, captures, effects, safety);
            observe_expr(&binary.rhs, state, captures, effects, safety);
            if safety.binary_operator_may_observe_gc_roots(binary.op, &binary.lhs, &binary.rhs)
                && !fields::operator_is_plain(expr, state)
            {
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
            let epoch = state
                .fields
                .as_ref()
                .map(fields::FieldFacts::observation_epoch);
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
            let object = ObjectId::table(table);
            state.allocations.insert(object);
            let mut contents = if state.fields.is_some() {
                let mut contents = BTreeSet::new();
                for field in &table.fields {
                    match field {
                        HirTableField::Array(value) => {
                            contents.extend(direct_holder_values(value, state, effects))
                        }
                        HirTableField::Record(record) => {
                            contents.extend(direct_holder_values(&record.key, state, effects));
                            contents.extend(direct_holder_values(&record.value, state, effects));
                        }
                    }
                }
                contents
            } else {
                holder_values(expr, state, effects)
            };
            contents.remove(&object);
            state.store_objects(object, &contents);
            let stable = epoch
                == state
                    .fields
                    .as_ref()
                    .map(fields::FieldFacts::observation_epoch);
            fields::construct(table, state, stable);
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
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => {}
    }
}

fn observe_call(
    call: &crate::hir::common::HirCallExpr,
    state: &mut RootState,
    captures: &ClosureCaptures<'_>,
    effects: &ModuleEffects,
    safety: HirExprSafety,
) {
    if let Some(fields) = &mut state.fields {
        fields.observe();
    }
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
    captures: &ClosureCaptures<'_>,
    effects: &ModuleEffects,
    safety: HirExprSafety,
) {
    if let Some(fields) = &mut state.fields {
        fields.observe();
    }
    let holders = holder_values(expr, state, effects);
    state.publish_objects(&holders);
    struct EscapeBindings<'a>(&'a mut RootState);
    impl crate::hir::visit::HirVisitor<'_> for EscapeBindings<'_> {
        fn visit_expr(&mut self, expr: &HirExpr) {
            if let Some(binding) = HirBinding::from_expr(expr)
                && self.0.unknown_collectable.contains(&binding)
            {
                self.0.roots.insert(binding);
            }
        }
    }
    crate::hir::visit::visit_expr(expr, &mut EscapeBindings(state));
    activate_object_ids(&holders, state, captures, effects, true, safety);
    if let HirExpr::Call(call) = expr {
        activate_closures(&call.callee, state, captures, effects, true, safety);
    }
}

fn activate_closures(
    expr: &HirExpr,
    state: &mut RootState,
    captures: &ClosureCaptures<'_>,
    effects: &ModuleEffects,
    include_returns: bool,
    safety: HirExprSafety,
) {
    let holders = holder_values(expr, state, effects);
    activate_object_ids(&holders, state, captures, effects, include_returns, safety);
}

fn activate_object_ids(
    holders: &BTreeSet<ObjectId>,
    state: &mut RootState,
    captures: &ClosureCaptures<'_>,
    effects: &ModuleEffects,
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
                let effect = &effects.protos[proto.index()];
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
                let effect = &effects.protos[producer.index()];
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
            if let Some(fields) = &mut state.fields {
                fields.install(capture.binding, None);
            }
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
        state.publish_objects(&captured_holders);
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
            state.publish_objects(&BTreeSet::from([returned]));
            pending.push_back(returned);
            for upvalue in &closure.captures {
                let Some(capture) = closure_captures.get(upvalue.index()) else {
                    continue;
                };
                let captured_holders = state.binding_holder_values(capture.binding);
                state.publish_objects(&captured_holders);
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

// 捕获身份只在本次只读求解内使用；返回的效果/根事实不携带引用，不跨 HIR 改写缓存。
type ClosureCaptures<'hir> = BTreeMap<HirProtoRef, &'hir [HirCapture]>;

pub(super) fn closure_captures_in_block(block: &HirBlock) -> ClosureCaptures<'_> {
    closure_captures_in_stmts(&block.stmts)
}

#[derive(Default)]
struct CaptureCollector<'hir>(ClosureCaptures<'hir>);

impl<'hir> crate::hir::visit::HirVisitor<'hir> for CaptureCollector<'hir> {
    fn visit_closure(&mut self, closure: &'hir crate::hir::HirClosureExpr) {
        if let Some(previous) = self.0.insert(closure.proto, &closure.captures) {
            debug_assert_eq!(
                previous, closure.captures,
                "a child proto must have one capture shape within its lexical parent"
            );
        }
    }
}

fn closure_captures_in_stmts(stmts: &[HirStmt]) -> ClosureCaptures<'_> {
    let mut captures = CaptureCollector::default();
    crate::hir::visit::visit_stmts(stmts, &mut captures);
    captures.0
}

pub(super) fn transfer_root_node(
    kind: HirFlowNodeKind<'_>,
    state: &mut RootState,
    captures: &ClosureCaptures<'_>,
    effects: &ModuleEffects,
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
