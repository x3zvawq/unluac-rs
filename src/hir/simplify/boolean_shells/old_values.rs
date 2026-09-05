//! 在同一 HIR 控制流快照上证明死布尔壳的旧值与读取者生命周期。
//!
//! 每个候选 binding/raw home 分别跟踪 `GC-inert / 可承载资源 / 证明不完整`。旧值分类、
//! closure/TBC 观察者和后向 may-live 共用一份 `HirFlowGraph`：label/goto、回边与不可达
//! 分支由图统一解释，本文件仅提供各自的有限单调域和 typed event 写入/观察语义。
//! 例如 `x = nil; goto L; ...; ::L:: if c then x=true else x=false end`，旧值沿实际
//! 到达 L 的路径合流；若任一回边带入对象，shell 必须保留释放旧根的写入职责。
//! 所有不动点完成后才按当前语句路径签发删除计划，不在中间迭代批准删除或重建控制边。
//! 候选 local 按完整 possible-home 集合建立反向索引，写入只更新可能命中的候选；
//! 未知 provenance 仍覆盖 home universe，home-free local 仍接收直接 binding 写入。
//! 数据流节点只投影 observer reads 与 shell 删除判定，不保存供后续重放的整份输入状态。
//! closure/TBC 观察者先完整解析，再把后向 gen 集合投影到候选 binding 与全部 possible-home；
//! 域外 holder 仍可传递候选 capture，不能在观察者 reaching 收敛前按候选过滤它。
//!
//! for initializer、dispatch 和每轮 binding write 各占独立节点；最终 dispatch 的 raw
//! result 写入也更新 home 分类，不能被源码零轮出口或成功 binding 写入掩盖。参数入口
//! home 集合直接来自 promotion，不按 ParamId 重建槽位。没有 shell 形状则不构建图。
//! home-free temp 虽不进入 local/raw-home 集合，仍是需要读取证明的真实候选。
//!
//! 节点先 gen RHS、条件与左值地址读取，再 kill 精确 local/temp 或唯一 possible-home 写入。
//! closure payload 前向 reaching 使用 Temp/Local/Param holder 的确定覆写 kill 旧 instance；
//! 只有当前 reaching closure 被调用、返回或写到外部位置时，其 ByReference cell 才进入
//! observer。ByValue capture 在创建点读取 snapshot。TBC 在标记点激活 home，并由 Close/
//! 函数出口读取后结束。引用捕获和资源协议不会退化成全 proto blanket guard。
//! 值是否 GC-inert 统一消费目标方言安全上下文；本文件不从底层 opcode 重新推断根协议。

use crate::hir::simplify::stmt_plan::{PathComponent, StmtPath, remove_planned_stmts};

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirAssign, HirBlock, HirCaptureMode, HirExpr, HirLValue, HirLocalDecl, HirProto, HirStmt,
    LocalId, ParamId, TempId,
};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::{HomeSlotKey, HomeSlots, ProtoPromotionFacts};

use super::{BooleanShellFacts, OldValueClass};
use crate::hir::simplify::expr_facts::expr_truthiness;
use crate::hir::simplify::lexical_cfg::{
    FlowRefinement, HirFlowGraph, HirFlowNodeKind, HirFlowProtocolId, HirForBindings,
};
use crate::hir::visit::{self, HirVisitor, visit_stmt_header};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct LiveBindingState {
    pub(super) temps: BTreeSet<TempId>,
    pub(super) locals: BTreeSet<LocalId>,
    pub(super) homes: BTreeSet<HomeSlotKey>,
}

impl LiveBindingState {
    fn retain_domain(&mut self, domain: &Self) {
        self.temps.retain(|temp| domain.temps.contains(temp));
        self.locals.retain(|local| domain.locals.contains(local));
        self.homes.retain(|home| domain.homes.contains(home));
    }

    fn union_with(&mut self, other: &Self) -> bool {
        let before = (self.temps.len(), self.locals.len(), self.homes.len());
        self.temps.extend(other.temps.iter().copied());
        self.locals.extend(other.locals.iter().copied());
        self.homes.extend(other.homes.iter().copied());
        before != (self.temps.len(), self.locals.len(), self.homes.len())
    }

    fn without_writes(mut self, writes: &LiveBindingState) -> Self {
        self.temps.retain(|temp| !writes.temps.contains(temp));
        self.locals.retain(|local| !writes.locals.contains(local));
        self.homes.retain(|home| !writes.homes.contains(home));
        self
    }
}

#[derive(Clone, Debug, Default)]
pub(super) struct ShellArmLiveOut {
    pub(super) then_arm: LiveBindingState,
    pub(super) else_arm: LiveBindingState,
}

#[derive(Clone, Debug)]
struct ShellFlowSite<'a> {
    stmt: &'a HirStmt,
    node: usize,
    arm_nodes: [usize; 2],
    live_after: ShellArmLiveOut,
}

#[derive(Default)]
struct ShellFlowFacts<'a> {
    shells: BTreeMap<StmtPath, ShellFlowSite<'a>>,
}

#[derive(Clone, Debug, Default)]
struct LiveCfgNode {
    reads: LiveBindingState,
    writes: LiveBindingState,
    escaped_gen: ClosurePayloadSeed,
    escape_holders: BTreeSet<ClosureHolder>,
    holder_writes: Vec<(ClosureHolder, HolderWrite)>,
    tbc_gen: BTreeSet<HomeSlotKey>,
    close_from: Option<usize>,
    observes_captures: bool,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct ActiveObserverState {
    escaped: ClosurePayload,
    // 缺项表示没有可观察的 capture payload；空 payload 与缺项对 resolve/reads 完全等价。
    // 只保存非空项，避免每个 primitive SSA 写入都扩大后续分支的状态快照。
    holder_values: BTreeMap<ClosureHolder, ClosurePayload>,
    tbc_homes: BTreeSet<HomeSlotKey>,
}

impl ActiveObserverState {
    fn union_with(&mut self, other: &Self) -> bool {
        let mut changed = self.escaped.union_with(&other.escaped);
        let holder_count = self.holder_values.len();
        for (holder, captures) in &other.holder_values {
            changed |= self
                .holder_values
                .entry(*holder)
                .or_default()
                .union_with(captures);
        }
        let tbc_count = self.tbc_homes.len();
        self.tbc_homes.extend(other.tbc_homes.iter().copied());
        changed || holder_count != self.holder_values.len() || tbc_count != self.tbc_homes.len()
    }

    fn apply(&mut self, node: &LiveCfgNode) {
        self.escaped
            .union_with(&node.escaped_gen.resolve(&self.holder_values));
        for holder in &node.escape_holders {
            if let Some(captures) = self.holder_values.get(holder) {
                self.escaped.union_with(captures);
            }
        }
        // 同一赋值所有 RHS 都读取旧 holder；先投影本次写入，再原位更新状态。
        let writes = node
            .holder_writes
            .iter()
            .map(|(holder, write)| {
                (
                    *holder,
                    match write {
                        HolderWrite::Clear => None,
                        HolderWrite::Capture(captures) => {
                            let payload = captures.resolve(&self.holder_values);
                            (!payload.is_empty()).then_some(payload)
                        }
                    },
                )
            })
            .collect::<Vec<_>>();
        for (holder, write) in writes {
            match write {
                None => {
                    self.holder_values.remove(&holder);
                }
                Some(captures) => {
                    self.holder_values.insert(holder, captures);
                }
            }
        }
        self.tbc_homes.extend(node.tbc_gen.iter().copied());
        if let Some(from_reg) = node.close_from {
            self.tbc_homes.retain(|home| home.slot() < from_reg);
        }
    }
}

impl<'a> ShellFlowFacts<'a> {
    fn collect(
        proto: &'a HirProto,
        graph: &HirFlowGraph<'a>,
        promotion_facts: &ProtoPromotionFacts,
        safety: HirExprSafety,
        live_domain: &LiveBindingState,
    ) -> Self {
        let mut nodes = vec![LiveCfgNode::default(); graph.nodes().len()];
        let mut stmt_nodes = BTreeMap::new();
        for (id, flow_node) in graph.nodes().iter().enumerate() {
            match flow_node.kind() {
                HirFlowNodeKind::Stmt(stmt) => {
                    stmt_nodes.insert(std::ptr::from_ref(stmt), id);
                    populate_stmt_live_event(&mut nodes[id], stmt, promotion_facts, safety);
                }
                HirFlowNodeKind::GenericForInit(flow) => {
                    stmt_nodes.insert(std::ptr::from_ref(flow.stmt()), id);
                    populate_stmt_live_event(&mut nodes[id], flow.stmt(), promotion_facts, safety);
                    for (slot, value) in flow.for_stmt().iterator.iter().enumerate() {
                        nodes[id].holder_writes.push((
                            ClosureHolder::GenericFor(flow.protocol(), slot),
                            HolderWrite::Capture(payload_seed_from_expr(
                                value,
                                promotion_facts,
                                safety,
                            )),
                        ));
                    }
                }
                HirFlowNodeKind::RepeatCondition(repeat_stmt) => {
                    populate_expr_live_event(
                        &mut nodes[id],
                        &repeat_stmt.cond,
                        promotion_facts,
                        safety,
                    );
                }
                HirFlowNodeKind::ForBinding(bindings) => match bindings {
                    HirForBindings::Numeric(binding) => {
                        record_for_binding_write(&mut nodes[id], binding, promotion_facts);
                    }
                    HirForBindings::Generic(flow) => {
                        for &binding in &flow.for_stmt().bindings {
                            record_generic_for_binding_projection(&mut nodes[id], binding);
                        }
                    }
                },
                HirFlowNodeKind::GenericForDispatch(flow) => {
                    for result in &flow.for_stmt().dispatch_results {
                        nodes[id].writes.homes.insert(
                            promotion_facts
                                .home_slot(result.result_def)
                                .expect("generic-for result must retain its raw physical home"),
                        );
                    }
                    nodes[id].observes_captures = true;
                    nodes[id].escape_holders.extend(
                        (0..flow.for_stmt().iterator.iter().count())
                            .map(|slot| ClosureHolder::GenericFor(flow.protocol(), slot)),
                    );
                }
                HirFlowNodeKind::UnknownControl => {
                    nodes[id].reads.temps.extend(proto.temps.iter().copied());
                    nodes[id].reads.locals.extend(proto.locals.iter().copied());
                    nodes[id]
                        .reads
                        .homes
                        .extend(promotion_facts.physical_home_universe().iter().copied());
                }
                HirFlowNodeKind::Exit
                | HirFlowNodeKind::FunctionExit
                | HirFlowNodeKind::NumericForDispatch => {}
            }
        }

        graph.solve_forward(
            ActiveObserverState::default(),
            ActiveObserverState::union_with,
            |id, kind, active| {
                let node = &mut nodes[id.index()];
                let is_function_exit = matches!(kind, HirFlowNodeKind::FunctionExit);
                if node.observes_captures || is_function_exit {
                    node.reads.union_with(&observable_payload_reads(
                        &active.escaped,
                        &active.holder_values,
                    ));
                }
                let mut immediate = node.escaped_gen.resolve(&active.holder_values);
                for holder in &node.escape_holders {
                    if let Some(captures) = active.holder_values.get(holder) {
                        immediate.union_with(captures);
                    }
                }
                node.reads
                    .union_with(&observable_payload_reads(&immediate, &active.holder_values));
                if node.close_from.is_some() || is_function_exit {
                    node.reads.homes.extend(active.tbc_homes.iter().copied());
                }
                active.apply(node);
            },
            |_expr, _truthy, _state| FlowRefinement::Unchanged,
        );
        // 观察者 reaching 已收敛；后向 gen/kill 按 binding/home 分量独立，不会从域外
        // 状态生成候选读取。写入仍消费原有精确 kill，不能用 possible-home 当作确定覆写。
        for node in &mut nodes {
            node.reads.retain_domain(live_domain);
        }
        let mut shells = BTreeMap::new();
        collect_shell_sites(&proto.body, &[], &stmt_nodes, &mut shells);
        let mut arm_outputs = shells
            .values_mut()
            .flat_map(|site| {
                [
                    (site.arm_nodes[0], &mut site.live_after.then_arm),
                    (site.arm_nodes[1], &mut site.live_after.else_arm),
                ]
            })
            .collect::<BTreeMap<_, _>>();
        graph.solve_backward(
            LiveBindingState::default(),
            LiveBindingState::union_with,
            |id, _, state| {
                if let Some(output) = arm_outputs.get_mut(&id.index()) {
                    output.clone_from(state);
                }
                let node = &nodes[id.index()];
                *state = std::mem::take(state).without_writes(&node.writes);
                state.union_with(&node.reads);
            },
        );
        Self { shells }
    }
}

fn populate_stmt_live_event(
    node: &mut LiveCfgNode,
    stmt: &HirStmt,
    promotion_facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
) {
    node.reads = reads_in_stmt_header(stmt, promotion_facts);
    node.writes = writes_in_stmt_header(stmt, promotion_facts);
    let observer_effects = closure_observer_effects_in_stmt(stmt, promotion_facts, safety);
    node.escaped_gen = observer_effects.escaped_gen;
    node.escape_holders = observer_effects.escape_holders;
    node.holder_writes = observer_effects.holder_writes;
    node.tbc_gen = tbc_homes_started_by_stmt(stmt, promotion_facts);
    node.close_from = match stmt {
        HirStmt::Close(close) => Some(close.from_reg),
        _ => None,
    };
    node.observes_captures = stmt_header_may_invoke_user_code(stmt, safety);
}

fn record_for_binding_write(
    node: &mut LiveCfgNode,
    binding: LocalId,
    promotion_facts: &ProtoPromotionFacts,
) {
    record_local_write(&mut node.writes, binding, promotion_facts);
    node.holder_writes
        .push((ClosureHolder::Local(binding), HolderWrite::Clear));
}

fn record_generic_for_binding_projection(node: &mut LiveCfgNode, binding: LocalId) {
    // TFORCALL 已在 dispatch 节点覆盖 raw result home；成功边只把同一个结果发布为
    // 源码 binding identity。退出边不会执行这次词法投影。
    node.writes.locals.insert(binding);
    node.holder_writes
        .push((ClosureHolder::Local(binding), HolderWrite::Clear));
}

fn populate_expr_live_event(
    node: &mut LiveCfgNode,
    expr: &HirExpr,
    promotion_facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
) {
    node.reads = reads_in_expr(expr, promotion_facts);
    let observer_effects = closure_observer_effects_in_expr(expr, promotion_facts, safety);
    node.escaped_gen = observer_effects.escaped_gen;
    node.escape_holders = observer_effects.escape_holders;
    node.holder_writes = observer_effects.holder_writes;
    node.observes_captures = expr_may_invoke_user_code(expr, safety);
}

fn reads_in_stmt_header(stmt: &HirStmt, promotion_facts: &ProtoPromotionFacts) -> LiveBindingState {
    let mut collector = LiveReadCollector {
        state: LiveBindingState::default(),
        promotion_facts,
    };
    visit_stmt_header(stmt, &mut collector);
    collector.state
}

fn reads_in_expr(expr: &HirExpr, promotion_facts: &ProtoPromotionFacts) -> LiveBindingState {
    let mut collector = LiveReadCollector {
        state: LiveBindingState::default(),
        promotion_facts,
    };
    visit::visit_expr(expr, &mut collector);
    collector.state
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum ClosureHolder {
    Temp(TempId),
    Local(LocalId),
    Param(ParamId),
    GenericFor(HirFlowProtocolId, usize),
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct ClosurePayload {
    bindings: LiveBindingState,
    captured_holder_cells: BTreeSet<ClosureHolder>,
}

impl ClosurePayload {
    fn is_empty(&self) -> bool {
        self.bindings.temps.is_empty()
            && self.bindings.locals.is_empty()
            && self.bindings.homes.is_empty()
            && self.captured_holder_cells.is_empty()
    }

    fn union_with(&mut self, other: &Self) -> bool {
        let changed = self.bindings.union_with(&other.bindings);
        let cell_count = self.captured_holder_cells.len();
        self.captured_holder_cells
            .extend(other.captured_holder_cells.iter().copied());
        changed || cell_count != self.captured_holder_cells.len()
    }
}

#[derive(Clone, Debug, Default)]
struct ClosurePayloadSeed {
    direct: ClosurePayload,
    sources: BTreeSet<ClosureHolder>,
}

impl ClosurePayloadSeed {
    fn union_with(&mut self, other: &Self) {
        self.direct.union_with(&other.direct);
        self.sources.extend(other.sources.iter().copied());
    }

    fn resolve(&self, holder_values: &BTreeMap<ClosureHolder, ClosurePayload>) -> ClosurePayload {
        let mut payload = self.direct.clone();
        for source in &self.sources {
            if let Some(source_payload) = holder_values.get(source) {
                payload.union_with(source_payload);
            }
        }
        payload
    }
}

fn observable_payload_reads(
    payload: &ClosurePayload,
    holder_values: &BTreeMap<ClosureHolder, ClosurePayload>,
) -> LiveBindingState {
    let mut reads = payload.bindings.clone();
    let mut pending = payload.captured_holder_cells.clone();
    let mut visited = BTreeSet::new();
    while let Some(holder) = pending.pop_first() {
        if !visited.insert(holder) {
            continue;
        }
        if let Some(value) = holder_values.get(&holder) {
            reads.union_with(&value.bindings);
            pending.extend(value.captured_holder_cells.iter().copied());
        }
    }
    reads
}

#[derive(Clone, Debug)]
enum HolderWrite {
    Clear,
    Capture(ClosurePayloadSeed),
}

#[derive(Default)]
struct ClosureObserverEffects {
    escaped_gen: ClosurePayloadSeed,
    escape_holders: BTreeSet<ClosureHolder>,
    holder_writes: Vec<(ClosureHolder, HolderWrite)>,
}

impl ClosureObserverEffects {
    fn record_escape(&mut self, seed: ClosurePayloadSeed) {
        self.escaped_gen.direct.union_with(&seed.direct);
        self.escape_holders.extend(seed.sources);
    }
}

fn closure_observer_effects_in_stmt(
    stmt: &HirStmt,
    promotion_facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
) -> ClosureObserverEffects {
    let mut effects = ClosureObserverEffects::default();
    match stmt {
        HirStmt::LocalDecl(decl) => {
            for (index, local) in decl.bindings.iter().copied().enumerate() {
                let write =
                    value_for_target(&decl.values, index).map_or(HolderWrite::Clear, |value| {
                        HolderWrite::Capture(payload_seed_from_expr(value, promotion_facts, safety))
                    });
                effects
                    .holder_writes
                    .push((ClosureHolder::Local(local), write));
            }
        }
        HirStmt::Assign(assign) => {
            for (index, target) in assign.targets.iter().enumerate() {
                let value = value_for_target(&assign.values, index);
                if let Some(holder) = holder_from_lvalue(target) {
                    let write = value.map_or(HolderWrite::Clear, |value| {
                        HolderWrite::Capture(payload_seed_from_expr(value, promotion_facts, safety))
                    });
                    effects.holder_writes.push((holder, write));
                } else if matches!(
                    target,
                    HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_)
                ) && let Some(value) = value
                {
                    effects.record_escape(payload_seed_from_expr(value, promotion_facts, safety));
                }
                if let HirLValue::TableAccess(access) = target {
                    effects.record_escape(payload_seed_from_expr(
                        &access.base,
                        promotion_facts,
                        safety,
                    ));
                    effects.record_escape(payload_seed_from_expr(
                        &access.key,
                        promotion_facts,
                        safety,
                    ));
                }
            }
        }
        HirStmt::GlobalDecl(decl) => {
            for index in 0..decl.names.len() {
                if let Some(value) = value_for_target(&decl.values, index) {
                    effects.record_escape(payload_seed_from_expr(value, promotion_facts, safety));
                }
            }
        }
        HirStmt::TableSetList(set_list) => {
            for value in &set_list.values {
                effects.record_escape(payload_seed_from_expr(value, promotion_facts, safety));
            }
        }
        HirStmt::Return(ret) => {
            for value in &ret.values {
                effects.record_escape(payload_seed_from_expr(value, promotion_facts, safety));
            }
        }
        HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::If(_)
        | HirStmt::While(_)
        | HirStmt::Repeat(_)
        | HirStmt::NumericFor(_)
        | HirStmt::GenericFor(_)
        | HirStmt::Block(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => {}
    }

    let mut calls = CallEscapeCollector {
        effects: &mut effects,
        promotion_facts,
        safety,
    };
    visit_stmt_header(stmt, &mut calls);
    effects
}

fn closure_observer_effects_in_expr(
    expr: &HirExpr,
    promotion_facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
) -> ClosureObserverEffects {
    let mut effects = ClosureObserverEffects::default();
    let mut calls = CallEscapeCollector {
        effects: &mut effects,
        promotion_facts,
        safety,
    };
    visit::visit_expr(expr, &mut calls);
    effects
}

fn value_for_target(values: &crate::hir::HirValuePack, index: usize) -> Option<&HirExpr> {
    values.fixed.get(index)
}

struct CallEscapeCollector<'a> {
    effects: &'a mut ClosureObserverEffects,
    promotion_facts: &'a ProtoPromotionFacts,
    safety: HirExprSafety,
}

impl HirVisitor for CallEscapeCollector<'_> {
    fn visit_call(&mut self, call: &crate::hir::HirCallExpr) {
        self.effects.record_escape(payload_seed_from_expr(
            &call.callee,
            self.promotion_facts,
            self.safety,
        ));
        for argument in &call.args {
            self.effects.record_escape(payload_seed_from_expr(
                argument,
                self.promotion_facts,
                self.safety,
            ));
        }
    }
}

fn holder_from_lvalue(target: &HirLValue) -> Option<ClosureHolder> {
    match target {
        HirLValue::Temp(temp) => Some(ClosureHolder::Temp(*temp)),
        HirLValue::Local(local) => Some(ClosureHolder::Local(*local)),
        HirLValue::Param(param) => Some(ClosureHolder::Param(*param)),
        HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_) => None,
    }
}

fn holder_from_expr(expr: &HirExpr) -> Option<ClosureHolder> {
    match expr {
        HirExpr::TempRef(temp) => Some(ClosureHolder::Temp(*temp)),
        HirExpr::LocalRef(local) => Some(ClosureHolder::Local(*local)),
        HirExpr::ParamRef(param) => Some(ClosureHolder::Param(*param)),
        _ => None,
    }
}

fn payload_seed_from_expr(
    expr: &HirExpr,
    promotion_facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
) -> ClosurePayloadSeed {
    let mut seed = ClosurePayloadSeed::default();
    match expr {
        HirExpr::TempRef(_) | HirExpr::LocalRef(_) | HirExpr::ParamRef(_) => {
            seed.sources.insert(
                holder_from_expr(expr).expect("binding references are closure holder candidates"),
            );
        }
        HirExpr::Closure(closure) => {
            for capture in &closure.captures {
                match capture.mode {
                    HirCaptureMode::ByReference => {
                        let mut bindings = CapturedBindingCollector {
                            state: &mut seed.direct.bindings,
                            promotion_facts,
                        };
                        visit::visit_expr(&capture.value, &mut bindings);
                        if let Some(holder) = holder_from_expr(&capture.value) {
                            seed.direct.captured_holder_cells.insert(holder);
                        }
                    }
                    HirCaptureMode::ByValue => seed.union_with(&payload_seed_from_expr(
                        &capture.value,
                        promotion_facts,
                        safety,
                    )),
                }
            }
        }
        HirExpr::LogicalAnd(logical) => match expr_truthiness(&logical.lhs, safety) {
            Some(true) => seed.union_with(&payload_seed_from_expr(
                &logical.rhs,
                promotion_facts,
                safety,
            )),
            Some(false) => seed.union_with(&payload_seed_from_expr(
                &logical.lhs,
                promotion_facts,
                safety,
            )),
            None => {
                seed.union_with(&payload_seed_from_expr(
                    &logical.lhs,
                    promotion_facts,
                    safety,
                ));
                seed.union_with(&payload_seed_from_expr(
                    &logical.rhs,
                    promotion_facts,
                    safety,
                ));
            }
        },
        HirExpr::LogicalOr(logical) => match expr_truthiness(&logical.lhs, safety) {
            Some(true) => seed.union_with(&payload_seed_from_expr(
                &logical.lhs,
                promotion_facts,
                safety,
            )),
            Some(false) => seed.union_with(&payload_seed_from_expr(
                &logical.rhs,
                promotion_facts,
                safety,
            )),
            None => {
                seed.union_with(&payload_seed_from_expr(
                    &logical.lhs,
                    promotion_facts,
                    safety,
                ));
                seed.union_with(&payload_seed_from_expr(
                    &logical.rhs,
                    promotion_facts,
                    safety,
                ));
            }
        },
        HirExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    crate::hir::HirTableField::Array(value) => {
                        seed.union_with(&payload_seed_from_expr(value, promotion_facts, safety))
                    }
                    crate::hir::HirTableField::Record(record) => {
                        seed.union_with(&payload_seed_from_expr(
                            &record.key,
                            promotion_facts,
                            safety,
                        ));
                        seed.union_with(&payload_seed_from_expr(
                            &record.value,
                            promotion_facts,
                            safety,
                        ));
                    }
                }
            }
        }
        HirExpr::Decision(decision) => {
            seed.union_with(&decision_payload_seed(decision, promotion_facts, safety));
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
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Unary(_)
        | HirExpr::Binary(_)
        | HirExpr::Call(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => {}
    }
    seed
}

fn decision_payload_seed(
    decision: &crate::hir::HirDecisionExpr,
    promotion_facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
) -> ClosurePayloadSeed {
    let mut seed = ClosurePayloadSeed::default();
    let topology = crate::hir::decision::analyze_decision(decision);
    let mut reachable = vec![false; decision.nodes.len()];
    reachable[decision.entry.index()] = true;
    for node in topology.topological_nodes() {
        if !reachable[node.id.index()] {
            continue;
        }
        let truthiness = expr_truthiness(&node.test, safety);
        for (edge_reachable, target) in [
            (truthiness != Some(false), &node.truthy),
            (truthiness != Some(true), &node.falsy),
        ] {
            if !edge_reachable {
                continue;
            }
            match target {
                crate::hir::HirDecisionTarget::Node(next) => {
                    reachable[next.index()] = true;
                }
                crate::hir::HirDecisionTarget::CurrentValue => {
                    seed.union_with(&payload_seed_from_expr(&node.test, promotion_facts, safety))
                }
                crate::hir::HirDecisionTarget::Expr(value) => {
                    seed.union_with(&payload_seed_from_expr(value, promotion_facts, safety));
                }
            }
        }
    }
    seed
}

struct CapturedBindingCollector<'a> {
    state: &'a mut LiveBindingState,
    promotion_facts: &'a ProtoPromotionFacts,
}

impl HirVisitor for CapturedBindingCollector<'_> {
    fn visit_expr(&mut self, expr: &HirExpr) {
        match expr {
            HirExpr::TempRef(temp) => {
                self.state.temps.insert(*temp);
                self.state.homes.extend(
                    self.promotion_facts
                        .complete_temp_home_slots(*temp)
                        .iter()
                        .copied(),
                );
            }
            HirExpr::LocalRef(local) => {
                self.state.locals.insert(*local);
                self.state.homes.extend(
                    self.promotion_facts
                        .complete_local_home_slots(*local)
                        .iter()
                        .copied(),
                );
            }
            HirExpr::ParamRef(param) => {
                self.state.homes.extend(
                    self.promotion_facts
                        .complete_param_home_slots(*param)
                        .iter()
                        .copied(),
                );
            }
            _ => {}
        }
    }
}

fn tbc_homes_started_by_stmt(
    stmt: &HirStmt,
    promotion_facts: &ProtoPromotionFacts,
) -> BTreeSet<HomeSlotKey> {
    let HirStmt::ToBeClosed(to_be_closed) = stmt else {
        return BTreeSet::new();
    };
    let value_homes = match &to_be_closed.value {
        HirExpr::TempRef(temp) => promotion_facts.complete_temp_home_slots(*temp),
        HirExpr::LocalRef(local) => promotion_facts.complete_local_home_slots(*local),
        HirExpr::ParamRef(param) => promotion_facts.complete_param_home_slots(*param),
        _ => Cow::Owned(BTreeSet::new()),
    };
    promotion_facts.complete_tbc_home_slots(to_be_closed.reg_index, &value_homes)
}

fn stmt_header_may_invoke_user_code(stmt: &HirStmt, safety: HirExprSafety) -> bool {
    let mut collector = UserCodeObserver {
        safety,
        found: false,
    };
    visit_stmt_header(stmt, &mut collector);
    collector.found
}

fn expr_may_invoke_user_code(expr: &HirExpr, safety: HirExprSafety) -> bool {
    let mut collector = UserCodeObserver {
        safety,
        found: false,
    };
    visit::visit_expr(expr, &mut collector);
    collector.found
}

struct UserCodeObserver {
    safety: HirExprSafety,
    found: bool,
}

impl HirVisitor for UserCodeObserver {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        self.found |= matches!(stmt, HirStmt::GlobalDecl(_) | HirStmt::Close(_));
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.found |= matches!(lvalue, HirLValue::Global(_) | HirLValue::TableAccess(_));
    }

    fn visit_call(&mut self, _call: &crate::hir::HirCallExpr) {
        self.found = true;
    }

    fn visit_expr(&mut self, expr: &HirExpr) {
        self.found |= !self.safety.node_is_discard_safe_without_residual(expr);
    }
}

fn writes_in_stmt_header(
    stmt: &HirStmt,
    promotion_facts: &ProtoPromotionFacts,
) -> LiveBindingState {
    let mut writes = LiveBindingState::default();
    match stmt {
        HirStmt::LocalDecl(decl) => {
            for local in &decl.bindings {
                record_local_write(&mut writes, *local, promotion_facts);
            }
        }
        HirStmt::Assign(assign) => {
            for target in &assign.targets {
                record_target_write(&mut writes, target, promotion_facts);
            }
        }
        HirStmt::GlobalDecl(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::If(_)
        | HirStmt::While(_)
        | HirStmt::Repeat(_)
        | HirStmt::NumericFor(_)
        | HirStmt::GenericFor(_)
        | HirStmt::Block(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => {}
    }
    writes
}

fn record_target_write(
    writes: &mut LiveBindingState,
    target: &HirLValue,
    promotion_facts: &ProtoPromotionFacts,
) {
    match target {
        HirLValue::Temp(temp) => {
            writes.temps.insert(*temp);
            record_single_home_write(writes, &promotion_facts.complete_temp_home_slots(*temp));
        }
        HirLValue::Local(local) => record_local_write(writes, *local, promotion_facts),
        HirLValue::Param(param) => {
            record_single_home_write(writes, &promotion_facts.complete_param_home_slots(*param))
        }
        HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_) => {}
    }
}

fn record_local_write(
    writes: &mut LiveBindingState,
    local: LocalId,
    promotion_facts: &ProtoPromotionFacts,
) {
    writes.locals.insert(local);
    record_single_home_write(writes, &promotion_facts.complete_local_home_slots(local));
}

fn record_single_home_write(writes: &mut LiveBindingState, homes: &BTreeSet<HomeSlotKey>) {
    if homes.len() == 1 {
        writes.homes.extend(homes.iter().copied());
    }
}

struct LiveReadCollector<'a> {
    state: LiveBindingState,
    promotion_facts: &'a ProtoPromotionFacts,
}

impl HirVisitor for LiveReadCollector<'_> {
    fn visit_expr(&mut self, expr: &HirExpr) {
        let homes = match expr {
            HirExpr::TempRef(temp) => {
                self.state.temps.insert(*temp);
                None
            }
            HirExpr::LocalRef(local) => {
                self.state.locals.insert(*local);
                Some(self.promotion_facts.complete_local_home_slots(*local))
            }
            HirExpr::ParamRef(param) => {
                Some(self.promotion_facts.complete_param_home_slots(*param))
            }
            _ => None,
        };
        if let Some(homes) = homes {
            self.state.homes.extend(homes.iter().copied());
        }
    }

    fn visit_capture(&mut self, capture: &crate::hir::HirCapture) {
        if capture.mode == HirCaptureMode::ByValue {
            visit::visit_expr(&capture.value, self);
        }
    }
}

fn collect_shell_sites<'a>(
    block: &'a HirBlock,
    prefix: &[PathComponent],
    stmt_nodes: &BTreeMap<*const HirStmt, usize>,
    shells: &mut BTreeMap<StmtPath, ShellFlowSite<'a>>,
) {
    for (index, stmt) in block.stmts.iter().enumerate() {
        let mut path = prefix.to_vec();
        path.push(PathComponent::Stmt(index));
        match stmt {
            HirStmt::If(if_stmt) => {
                if let Some(else_block) = &if_stmt.else_block
                    && super::single_fixed_assign_pattern(&if_stmt.then_block).is_some()
                    && super::single_fixed_assign_pattern(else_block).is_some()
                {
                    let then_stmt = &if_stmt.then_block.stmts[0];
                    let else_stmt = &else_block.stmts[0];
                    shells.insert(
                        path.clone(),
                        ShellFlowSite {
                            stmt,
                            node: stmt_nodes[&std::ptr::from_ref(stmt)],
                            arm_nodes: [
                                stmt_nodes[&std::ptr::from_ref(then_stmt)],
                                stmt_nodes[&std::ptr::from_ref(else_stmt)],
                            ],
                            live_after: ShellArmLiveOut::default(),
                        },
                    );
                }
                let mut then_prefix = path.clone();
                then_prefix.push(PathComponent::Then);
                collect_shell_sites(&if_stmt.then_block, &then_prefix, stmt_nodes, shells);
                if let Some(else_block) = &if_stmt.else_block {
                    let mut else_prefix = path.clone();
                    else_prefix.push(PathComponent::Else);
                    collect_shell_sites(else_block, &else_prefix, stmt_nodes, shells);
                }
            }
            HirStmt::While(while_stmt) => {
                collect_body_shell_sites(&while_stmt.body, &path, stmt_nodes, shells);
            }
            HirStmt::Repeat(repeat_stmt) => {
                collect_body_shell_sites(&repeat_stmt.body, &path, stmt_nodes, shells);
            }
            HirStmt::NumericFor(for_stmt) => {
                collect_body_shell_sites(&for_stmt.body, &path, stmt_nodes, shells);
            }
            HirStmt::GenericFor(for_stmt) => {
                collect_body_shell_sites(&for_stmt.body, &path, stmt_nodes, shells);
            }
            HirStmt::Block(nested) => {
                collect_body_shell_sites(nested, &path, stmt_nodes, shells);
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
}

fn collect_body_shell_sites<'a>(
    body: &'a HirBlock,
    path: &StmtPath,
    stmt_nodes: &BTreeMap<*const HirStmt, usize>,
    shells: &mut BTreeMap<StmtPath, ShellFlowSite<'a>>,
) {
    let mut prefix = path.clone();
    prefix.push(PathComponent::Body);
    collect_shell_sites(body, &prefix, stmt_nodes, shells);
}

#[derive(Default)]
pub(super) struct DeadShellPlan {
    removable: BTreeSet<StmtPath>,
}

impl DeadShellPlan {
    pub(super) fn collect(
        proto: &HirProto,
        facts: &BooleanShellFacts,
        safety: HirExprSafety,
    ) -> Self {
        let promotion_facts = facts.promotion_facts;
        let mut candidates = CandidateValues {
            has_shell: false,
            temps: BTreeSet::new(),
            locals: BTreeSet::new(),
            homes: BTreeSet::new(),
            entry_nil_homes: BTreeSet::new(),
            promotion_facts,
        };
        visit::visit_proto(proto, &mut candidates);
        if !candidates.has_shell {
            return Self::default();
        }
        let Ok(graph) = HirFlowGraph::for_proto(&proto.body, safety) else {
            // 分析停用[SemanticBarrier:ControlFlow]：同一个 label identity 若有多个 owner，
            // 不能签发唯一的 reaching/observer 证明，也不能在 consumer 内猜测目标。
            return Self::default();
        };
        let shell_facts = ShellFlowFacts::collect(
            proto,
            &graph,
            promotion_facts,
            safety,
            &candidates.live_domain(),
        );
        let mut parameter_homes = BTreeSet::new();
        for param in &proto.params {
            parameter_homes.extend(
                promotion_facts
                    .complete_param_home_slots(*param)
                    .iter()
                    .copied(),
            );
        }
        let initial_state = OldValueFacts::initial(&candidates, &parameter_homes);
        let transfer = OldValueTransfer::new(candidates, safety);
        let sites_by_node = shell_facts
            .shells
            .values()
            .map(|site| (site.node, site))
            .collect::<BTreeMap<_, _>>();
        let entries = graph.solve_forward(
            initial_state,
            join_states,
            |id, kind, state| {
                let removable = sites_by_node.get(&id.index()).is_some_and(|site| {
                    super::removable_dead_materialization_shell(
                        site.stmt,
                        facts,
                        None,
                        state,
                        &site.live_after,
                        safety,
                    )
                });
                *state = transfer.apply(kind, std::mem::take(state));
                removable
            },
            |_expr, _truthy, _state| FlowRefinement::Unchanged,
        );
        let removable = shell_facts
            .shells
            .into_iter()
            .filter_map(|(path, site)| entries[site.node].unwrap_or(false).then_some(path))
            .collect();
        Self { removable }
    }

    pub(super) fn apply(self, block: &mut HirBlock) -> bool {
        if self.removable.is_empty() {
            return false;
        }
        remove_planned_stmts(block, &mut Vec::new(), &self.removable);
        true
    }
}

struct CandidateValues<'a> {
    has_shell: bool,
    temps: BTreeSet<TempId>,
    locals: BTreeSet<LocalId>,
    homes: BTreeSet<HomeSlotKey>,
    entry_nil_homes: BTreeSet<HomeSlotKey>,
    promotion_facts: &'a ProtoPromotionFacts,
}

impl CandidateValues<'_> {
    fn live_domain(&self) -> LiveBindingState {
        let mut homes = self.homes.clone();
        for &local in &self.locals {
            homes.extend(
                self.promotion_facts
                    .complete_local_home_slots(local)
                    .iter()
                    .copied(),
            );
        }
        LiveBindingState {
            temps: self.temps.clone(),
            locals: self.locals.clone(),
            homes,
        }
    }
}

impl HirVisitor for CandidateValues<'_> {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        let HirStmt::If(if_stmt) = stmt else {
            return;
        };
        let Some(else_block) = &if_stmt.else_block else {
            return;
        };
        let Some((then_target, _)) = super::single_fixed_assign_pattern(&if_stmt.then_block) else {
            return;
        };
        let Some((else_target, _)) = super::single_fixed_assign_pattern(else_block) else {
            return;
        };
        self.has_shell = true;
        for target in [then_target, else_target] {
            match target {
                HirLValue::Local(local) => {
                    self.locals.insert(*local);
                }
                HirLValue::Temp(temp) => {
                    self.temps.insert(*temp);
                    let homes = self.promotion_facts.complete_temp_home_slots(*temp);
                    self.homes.extend(homes.iter().copied());
                    if homes.len() == 1 && self.promotion_facts.overwrites_entry_nil(*temp) {
                        self.entry_nil_homes.extend(homes.iter().copied());
                    }
                }
                _ => {}
            }
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct OldValueFacts {
    local_classes: BTreeMap<LocalId, OldValueClass>,
    home_classes: BTreeMap<HomeSlotKey, OldValueClass>,
}

impl OldValueFacts {
    fn initial(candidates: &CandidateValues<'_>, parameter_homes: &BTreeSet<HomeSlotKey>) -> Self {
        Self {
            local_classes: candidates
                .locals
                .iter()
                .copied()
                .map(|local| {
                    let class = if candidates
                        .promotion_facts
                        .entry_nil_writes_were_pruned(local)
                    {
                        OldValueClass::GcInert
                    } else if candidates
                        .promotion_facts
                        .local_home_slot(local)
                        .is_some_and(|home| parameter_homes.contains(&home))
                    {
                        OldValueClass::MayCarryResource
                    } else {
                        OldValueClass::Unknown
                    };
                    (local, class)
                })
                .collect(),
            home_classes: candidates
                .homes
                .iter()
                .copied()
                .map(|home| {
                    let class = if parameter_homes.contains(&home) {
                        OldValueClass::MayCarryResource
                    } else if candidates.entry_nil_homes.contains(&home) {
                        OldValueClass::GcInert
                    } else {
                        OldValueClass::Unknown
                    };
                    (home, class)
                })
                .collect(),
        }
    }

    pub(super) fn local(&self, local: LocalId) -> OldValueClass {
        self.local_classes
            .get(&local)
            .copied()
            .unwrap_or(OldValueClass::Unknown)
    }

    pub(super) fn home(&self, home: HomeSlotKey) -> OldValueClass {
        self.home_classes
            .get(&home)
            .copied()
            .unwrap_or(OldValueClass::Unknown)
    }

    fn merge_possible_local_write(&mut self, local: LocalId, written: OldValueClass) {
        let current = self
            .local_classes
            .entry(local)
            .or_insert(OldValueClass::Unknown);
        *current = join_value_classes(*current, written);
    }

    fn merge_possible_home_write(&mut self, home: HomeSlotKey, written: OldValueClass) {
        let current = self
            .home_classes
            .entry(home)
            .or_insert(OldValueClass::Unknown);
        *current = join_value_classes(*current, written);
    }

    fn obscure_physical_homes(mut self) -> Self {
        self.home_classes
            .values_mut()
            .for_each(|class| *class = OldValueClass::MayCarryResource);
        self
    }
}

/// 在共享 CFG typed event 上更新当前候选 binding/home 的旧值分类。
/// 控制边、循环收敛和不可达状态均由图管理；这里只解释实际写入。
struct OldValueTransfer<'a> {
    promotion_facts: &'a ProtoPromotionFacts,
    safety: HirExprSafety,
    locals_by_home: BTreeMap<HomeSlotKey, Vec<(LocalId, bool)>>,
    candidate_homes: BTreeSet<HomeSlotKey>,
}

impl<'a> OldValueTransfer<'a> {
    fn new(candidates: CandidateValues<'a>, safety: HirExprSafety) -> Self {
        let mut locals_by_home = BTreeMap::<_, Vec<_>>::new();
        for local in candidates.locals {
            if let Some(home) = candidates.promotion_facts.trusted_local_home_slot(local) {
                locals_by_home.entry(home).or_default().push((local, true));
            } else {
                let homes = candidates.promotion_facts.complete_local_home_slots(local);
                for home in homes.iter() {
                    locals_by_home
                        .entry(*home)
                        .or_default()
                        .push((local, homes.len() == 1));
                }
            }
        }
        Self {
            promotion_facts: candidates.promotion_facts,
            safety,
            locals_by_home,
            candidate_homes: candidates.homes,
        }
    }
    fn apply(&self, kind: HirFlowNodeKind<'_>, mut state: OldValueFacts) -> OldValueFacts {
        match kind {
            HirFlowNodeKind::Stmt(HirStmt::LocalDecl(decl)) => self.apply_local_decl(decl, state),
            HirFlowNodeKind::Stmt(HirStmt::Assign(assign)) => self.apply_assignment(assign, state),
            HirFlowNodeKind::Stmt(HirStmt::GlobalDecl(_)) => {
                // 该语法节点隐藏 call-result/probe 对 VM scratch 的写入；词法 local
                // 仍独立，raw home 在协议尚未发布精确写事件时不能延续 GC-inert 正证明。
                state.obscure_physical_homes()
            }
            HirFlowNodeKind::ForBinding(HirForBindings::Numeric(binding)) => {
                self.write_local_binding(binding, OldValueClass::GcInert, state)
            }
            HirFlowNodeKind::ForBinding(HirForBindings::Generic(flow)) => {
                for binding in &flow.for_stmt().bindings {
                    state =
                        self.write_local_binding(*binding, OldValueClass::MayCarryResource, state);
                }
                state
            }
            HirFlowNodeKind::GenericForDispatch(flow) => {
                // 最终一次返回 nil 也会执行 dispatch；result home 写入不能等价为仅在
                // 进入 body 后执行的源码 binding 写入。消费 Structure 冻结的 def 身份。
                for result in &flow.for_stmt().dispatch_results {
                    state = self.write_target(
                        &HirLValue::Temp(result.result_def),
                        OldValueClass::MayCarryResource,
                        state,
                    );
                }
                state
            }
            HirFlowNodeKind::UnknownControl => {
                state
                    .local_classes
                    .values_mut()
                    .for_each(|class| *class = OldValueClass::MayCarryResource);
                state.obscure_physical_homes()
            }
            HirFlowNodeKind::Stmt(_)
            | HirFlowNodeKind::GenericForInit(_)
            | HirFlowNodeKind::RepeatCondition(_)
            | HirFlowNodeKind::NumericForDispatch
            | HirFlowNodeKind::Exit
            | HirFlowNodeKind::FunctionExit => state,
        }
    }

    fn apply_assignment(&self, assign: &HirAssign, mut state: OldValueFacts) -> OldValueFacts {
        for (index, target) in assign.targets.iter().enumerate() {
            state = self.write_target(
                target,
                assigned_value_class(assign, index, self.safety),
                state,
            );
        }
        state
    }

    fn apply_local_decl(&self, decl: &HirLocalDecl, mut state: OldValueFacts) -> OldValueFacts {
        for (index, binding) in decl.bindings.iter().enumerate() {
            state = self.write_local_binding(
                *binding,
                declared_value_class(decl, index, self.safety),
                state,
            );
        }
        state
    }

    fn write_local_binding(
        &self,
        binding: LocalId,
        value_class: OldValueClass,
        state: OldValueFacts,
    ) -> OldValueFacts {
        self.write_target(&HirLValue::Local(binding), value_class, state)
    }

    fn write_target(
        &self,
        target: &HirLValue,
        value_class: OldValueClass,
        mut state: OldValueFacts,
    ) -> OldValueFacts {
        let homes = self.target_homes(target);
        let unique_home = homes.len() == 1;
        for home in homes.iter() {
            if self.candidate_homes.contains(home) {
                if unique_home {
                    state.home_classes.insert(*home, value_class);
                } else {
                    state.merge_possible_home_write(*home, value_class);
                }
            }
            if let Some(locals) = self.locals_by_home.get(home) {
                for &(local, unique_local_home) in locals {
                    if unique_home && unique_local_home {
                        state.local_classes.insert(local, value_class);
                    } else {
                        state.merge_possible_local_write(local, value_class);
                    }
                }
            }
        }
        // 直接源码 binding 写入是确定覆盖，即使它的物理 provenance 已合流或为 home-free。
        if let HirLValue::Local(local) = target
            && let Some(class) = state.local_classes.get_mut(local)
        {
            *class = value_class;
        }
        state
    }

    fn target_homes(&self, target: &HirLValue) -> HomeSlots<'_> {
        let trusted = match target {
            HirLValue::Temp(temp) => self.promotion_facts.trusted_temp_home_slot(*temp),
            HirLValue::Local(local) => self.promotion_facts.trusted_local_home_slot(*local),
            HirLValue::Param(param) => self.promotion_facts.trusted_param_home_slot(*param),
            HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_) => {
                return Cow::Owned(BTreeSet::new());
            }
        };
        if let Some(home) = trusted {
            return Cow::Owned(BTreeSet::from([home]));
        }
        match target {
            HirLValue::Temp(temp) => self.promotion_facts.complete_temp_home_slots(*temp),
            HirLValue::Local(local) => self.promotion_facts.complete_local_home_slots(*local),
            HirLValue::Param(param) => self.promotion_facts.complete_param_home_slots(*param),
            _ => unreachable!("external writes have no binding homes"),
        }
    }
}
fn assigned_value_class(
    assign: &HirAssign,
    target_index: usize,
    safety: HirExprSafety,
) -> OldValueClass {
    value_at_class(
        &assign.values.fixed,
        assign.values.tail.is_some(),
        target_index,
        safety,
    )
}

fn declared_value_class(
    decl: &HirLocalDecl,
    binding_index: usize,
    safety: HirExprSafety,
) -> OldValueClass {
    value_at_class(
        &decl.values.fixed,
        decl.values.tail.is_some(),
        binding_index,
        safety,
    )
}

fn value_at_class(
    fixed: &[HirExpr],
    has_tail: bool,
    index: usize,
    safety: HirExprSafety,
) -> OldValueClass {
    let Some(value) = fixed.get(index) else {
        return if has_tail {
            OldValueClass::MayCarryResource
        } else {
            OldValueClass::GcInert
        };
    };
    if safety.result_is_gc_inert(value) {
        return OldValueClass::GcInert;
    }
    match value {
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Vector(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Unary(_)
        | HirExpr::Binary(_)
        | HirExpr::LogicalAnd(_)
        | HirExpr::LogicalOr(_)
        | HirExpr::Decision(_)
        | HirExpr::Call(_)
        | HirExpr::VarArg
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => OldValueClass::MayCarryResource,
    }
}

fn join_states(left: &mut OldValueFacts, right: &OldValueFacts) -> bool {
    let locals_changed = join_class_maps(&mut left.local_classes, &right.local_classes);
    join_class_maps(&mut left.home_classes, &right.home_classes) || locals_changed
}

fn join_class_maps<K: Ord + Copy>(
    left: &mut BTreeMap<K, OldValueClass>,
    right: &BTreeMap<K, OldValueClass>,
) -> bool {
    let mut changed = false;
    for (binding, left_class) in left.iter_mut() {
        let right_class = right
            .get(binding)
            .copied()
            .unwrap_or(OldValueClass::Unknown);
        let merged = join_value_classes(*left_class, right_class);
        changed |= *left_class != merged;
        *left_class = merged;
    }
    for (&binding, &right_class) in right {
        if let std::collections::btree_map::Entry::Vacant(entry) = left.entry(binding) {
            entry.insert(join_value_classes(OldValueClass::Unknown, right_class));
            changed = true;
        }
    }
    changed
}

fn join_value_classes(left: OldValueClass, right: OldValueClass) -> OldValueClass {
    match (left, right) {
        (OldValueClass::GcInert, OldValueClass::GcInert) => OldValueClass::GcInert,
        (OldValueClass::MayCarryResource, _) | (_, OldValueClass::MayCarryResource) => {
            OldValueClass::MayCarryResource
        }
        (OldValueClass::Unknown, _) | (_, OldValueClass::Unknown) => OldValueClass::Unknown,
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use crate::hir::common::LocalId;
    use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

    use super::{CandidateValues, OldValueClass, OldValueFacts};

    #[test]
    fn entry_nil_provenance_seeds_only_proven_candidates_as_gc_inert() {
        let pruned_local = LocalId(0);
        let unknown_local = LocalId(1);
        let entry_nil_home = HomeSlotKey::new(2, 0);
        let unknown_home = HomeSlotKey::new(3, 0);
        let parameter_home = HomeSlotKey::new(0, 0);
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.mark_entry_nil_writes_pruned(pruned_local);
        let candidates = CandidateValues {
            has_shell: true,
            temps: BTreeSet::new(),
            locals: BTreeSet::from([pruned_local, unknown_local]),
            homes: BTreeSet::from([entry_nil_home, unknown_home, parameter_home]),
            entry_nil_homes: BTreeSet::from([entry_nil_home]),
            promotion_facts: &promotion_facts,
        };

        let state = OldValueFacts::initial(&candidates, &BTreeSet::from([parameter_home]));

        assert_eq!(
            state.local_classes.get(&pruned_local),
            Some(&OldValueClass::GcInert)
        );
        assert_eq!(
            state.local_classes.get(&unknown_local),
            Some(&OldValueClass::Unknown)
        );
        assert_eq!(
            state.home_classes.get(&entry_nil_home),
            Some(&OldValueClass::GcInert)
        );
        assert_eq!(
            state.home_classes.get(&unknown_home),
            Some(&OldValueClass::Unknown)
        );
        assert_eq!(
            state.home_classes.get(&parameter_home),
            Some(&OldValueClass::MayCarryResource)
        );
    }
}
