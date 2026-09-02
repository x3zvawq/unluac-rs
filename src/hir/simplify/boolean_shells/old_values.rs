//! 证明 dead local boolean shell 入口的旧值不承载可观察的 GC 生命周期。
//!
//! 分析只消费当前 HIR 已有的结构化控制流与 trusted home。每个状态分别跟踪候选 local
//! 与 raw home 的 `GC-inert / 可承载资源 / 证明不完整`；分支合流保留任一路径上的资源
//! 可能，循环对回边求有限不动点。
//! 分析阶段只记录完整语句路径，验证结束后才一次性应用删除，避免边改边算让 reaching
//! value 漂移。同 block 单调 forward goto 可直接跳到唯一 label；共享 `LexicalCfg` 会把
//! 后置嵌套 island 的自含回环留给嵌套 analyzer，只在当前层存在跨层或回边 goto 时才把
//! 该 block 从资源保守状态重新证明，避免一个非结构化区域停用整个 proto，也避免在线性
//! HIR 上猜 predecessor。
//! dead write 的读取证明消费共享 `HirFlowGraph` 的全 proto topology：label id 统一解析跨
//! block goto，函数出口与未知控制流显式分流，for initializer、dispatch 和每轮 binding write
//! 各占独立节点；本 pass 只在其上附加 binding/home 的 gen-kill 并求后向 may-live 不动点。若
//! proto 没有任何 dead-shell 形状，则不构建这份 owner-wide 图与不动点；home-free temp
//! 虽然不会进入 local/raw-home 集合，仍然是需要分析的真实候选。
//! 节点先 gen RHS、条件与左值地址读取，再 kill 精确 local/temp 或唯一 possible-home 写入。
//! closure payload 另做前向 reaching：Temp/Local/Param holder 的确定覆写 kill 旧 instance，
//! 分支与回边按 may payload 合流；只有当前 reaching closure 被调用、返回或写到外部位置时，
//! 其 ByReference cell 才进入 observer。ByValue capture 仍在创建点读取 snapshot。TBC 同样
//! 在标记点激活 raw home，并由 `Close`/函数出口读取后按 `from_reg` 结束。这样 capture/TBC
//! 的持久观察不会退化成全 proto blanket guard。
//! 值是否 GC-inert 由外层传入的目标方言安全上下文判定，避免 reaching class 与删除证明漂移。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirAssign, HirBlock, HirCaptureMode, HirExpr, HirLValue, HirLocalDecl, HirProto, HirStmt,
    LocalId, ParamId, TempId,
};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

use super::{
    BindingRelation, BooleanShellFacts, DeadShellOldValueFacts, OldValueClass,
    possible_home_relation,
};
use crate::hir::simplify::expr_facts::expr_truthiness;
use crate::hir::simplify::label_refs::count_label_references;
use crate::hir::simplify::lexical_cfg::{
    HirFlowGraph, HirFlowNodeKind, HirFlowProtocolId, HirForBindings, LexicalCfg,
};
use crate::hir::simplify::temp_touch::stmt_contains_nested_nonlocal_control;
use crate::hir::simplify::visit::{self, HirVisitor};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum PathComponent {
    Stmt(usize),
    Then,
    Else,
    Body,
}

type StmtPath = Vec<PathComponent>;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct LiveBindingState {
    pub(super) temps: BTreeSet<TempId>,
    pub(super) locals: BTreeSet<LocalId>,
    pub(super) homes: BTreeSet<HomeSlotKey>,
}

impl LiveBindingState {
    fn union_with(&mut self, other: &Self) {
        self.temps.extend(other.temps.iter().copied());
        self.locals.extend(other.locals.iter().copied());
        self.homes.extend(other.homes.iter().copied());
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

#[derive(Clone, Debug, Default)]
struct LiveAfterFacts {
    shells: BTreeMap<StmtPath, ShellArmLiveOut>,
}

#[derive(Clone, Debug, Default)]
struct LiveCfgNode {
    successors: BTreeSet<usize>,
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
    holder_values: BTreeMap<ClosureHolder, ClosurePayload>,
    tbc_homes: BTreeSet<HomeSlotKey>,
}

impl ActiveObserverState {
    fn union_with(&mut self, other: &Self) {
        self.escaped.union_with(&other.escaped);
        for (holder, captures) in &other.holder_values {
            self.holder_values
                .entry(*holder)
                .or_default()
                .union_with(captures);
        }
        self.tbc_homes.extend(other.tbc_homes.iter().copied());
    }

    fn after(&self, node: &LiveCfgNode) -> Self {
        let mut next = self.clone();
        next.escaped
            .union_with(&node.escaped_gen.resolve(&self.holder_values));
        for holder in &node.escape_holders {
            if let Some(captures) = self.holder_values.get(holder) {
                next.escaped.union_with(captures);
            }
        }
        for (holder, write) in &node.holder_writes {
            match write {
                HolderWrite::Clear => {
                    next.holder_values.remove(holder);
                }
                HolderWrite::Capture(captures) => {
                    next.holder_values
                        .insert(*holder, captures.resolve(&self.holder_values));
                }
            }
        }
        next.tbc_homes.extend(node.tbc_gen.iter().copied());
        if let Some(from_reg) = node.close_from {
            next.tbc_homes.retain(|home| home.slot() < from_reg);
        }
        next
    }
}

impl LiveAfterFacts {
    fn collect(
        proto: &HirProto,
        promotion_facts: &ProtoPromotionFacts,
        safety: HirExprSafety,
    ) -> Self {
        let Ok(graph) = HirFlowGraph::for_proto(&proto.body, safety) else {
            // label identity 不唯一时共享 topology 无法给出唯一事实；空结果会令所有候选
            // 保守拒绝删除，而不是在 consumer 内另建一套猜测边。
            return Self::default();
        };
        let mut nodes = graph
            .nodes()
            .iter()
            .map(|node| LiveCfgNode {
                successors: node
                    .successors()
                    .iter()
                    .map(|successor| successor.index())
                    .collect(),
                ..LiveCfgNode::default()
            })
            .collect::<Vec<_>>();
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

        let entry = graph.entry().index();
        let active_observers = solve_active_observers(&nodes, entry);
        for (id, active) in active_observers.into_iter().enumerate() {
            let is_function_exit =
                matches!(graph.nodes()[id].kind(), HirFlowNodeKind::FunctionExit);
            if nodes[id].observes_captures || is_function_exit {
                nodes[id].reads.union_with(&observable_payload_reads(
                    &active.escaped,
                    &active.holder_values,
                ));
            }
            let mut immediate = nodes[id].escaped_gen.resolve(&active.holder_values);
            for holder in &nodes[id].escape_holders {
                if let Some(captures) = active.holder_values.get(holder) {
                    immediate.union_with(captures);
                }
            }
            nodes[id]
                .reads
                .union_with(&observable_payload_reads(&immediate, &active.holder_values));
            if nodes[id].close_from.is_some() || is_function_exit {
                nodes[id]
                    .reads
                    .homes
                    .extend(active.tbc_homes.iter().copied());
            }
        }
        let live_out = solve_live_out(&nodes);
        let mut shells = BTreeMap::new();
        collect_shell_live_outs(&proto.body, &[], &stmt_nodes, &live_out, &mut shells);
        Self { shells }
    }

    fn shell(&self, path: &StmtPath) -> Option<&ShellArmLiveOut> {
        self.shells.get(path)
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
        counts: LiveBindingCounts::default(),
        promotion_facts,
    };
    visit_stmt_header(stmt, &mut collector);
    let mut reference_captures = ReferenceCaptureReadCollector {
        counts: LiveBindingCounts::default(),
        promotion_facts,
    };
    visit_stmt_header(stmt, &mut reference_captures);
    collector.counts.without(&reference_captures.counts)
}

fn reads_in_expr(expr: &HirExpr, promotion_facts: &ProtoPromotionFacts) -> LiveBindingState {
    let mut collector = LiveReadCollector {
        counts: LiveBindingCounts::default(),
        promotion_facts,
    };
    visit::visit_expr(expr, &mut collector);
    let mut reference_captures = ReferenceCaptureReadCollector {
        counts: LiveBindingCounts::default(),
        promotion_facts,
    };
    visit::visit_expr(expr, &mut reference_captures);
    collector.counts.without(&reference_captures.counts)
}

fn visit_stmt_header(stmt: &HirStmt, visitor: &mut impl HirVisitor) {
    visitor.visit_stmt(stmt);
    match stmt {
        HirStmt::LocalDecl(decl) => {
            for value in &decl.values {
                visit::visit_expr(value, visitor);
            }
        }
        HirStmt::GlobalDecl(decl) => {
            for value in &decl.values {
                visit::visit_expr(value, visitor);
            }
        }
        HirStmt::Assign(assign) => {
            for target in &assign.targets {
                visit::visit_lvalue(target, visitor);
            }
            for value in &assign.values {
                visit::visit_expr(value, visitor);
            }
        }
        HirStmt::TableSetList(set_list) => {
            visit::visit_expr(&set_list.base, visitor);
            for value in &set_list.values {
                visit::visit_expr(value, visitor);
            }
        }
        HirStmt::ErrNil(err_nil) => visit::visit_expr(&err_nil.value, visitor),
        HirStmt::ToBeClosed(to_be_closed) => {
            visit::visit_expr(&to_be_closed.value, visitor);
        }
        HirStmt::CallStmt(call_stmt) => visit::visit_call(&call_stmt.call, visitor),
        HirStmt::Return(ret) => {
            for value in &ret.values {
                visit::visit_expr(value, visitor);
            }
        }
        HirStmt::If(if_stmt) => visit::visit_expr(&if_stmt.cond, visitor),
        HirStmt::While(while_stmt) => visit::visit_expr(&while_stmt.cond, visitor),
        HirStmt::Repeat(repeat_stmt) => visit::visit_expr(&repeat_stmt.cond, visitor),
        HirStmt::NumericFor(for_stmt) => {
            visit::visit_expr(&for_stmt.start, visitor);
            visit::visit_expr(&for_stmt.limit, visitor);
            visit::visit_expr(&for_stmt.step, visitor);
        }
        HirStmt::GenericFor(for_stmt) => {
            for value in &for_stmt.iterator {
                visit::visit_expr(value, visitor);
            }
        }
        HirStmt::Close(_)
        | HirStmt::Block(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => {}
    }
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
    fn union_with(&mut self, other: &Self) {
        self.bindings.union_with(&other.bindings);
        self.captured_holder_cells
            .extend(other.captured_holder_cells.iter().copied());
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
    let mut pending = BTreeSet::from([decision.entry]);
    let mut visited = BTreeSet::new();
    while let Some(node_ref) = pending.pop_first() {
        if !visited.insert(node_ref) {
            continue;
        }
        let Some(node) = decision.nodes.iter().find(|node| node.id == node_ref) else {
            continue;
        };
        let truthiness = expr_truthiness(&node.test, safety);
        for (reachable, target) in [
            (truthiness != Some(false), &node.truthy),
            (truthiness != Some(true), &node.falsy),
        ] {
            if !reachable {
                continue;
            }
            match target {
                crate::hir::HirDecisionTarget::Node(next) => {
                    pending.insert(*next);
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
                self.state
                    .homes
                    .extend(self.promotion_facts.complete_temp_home_slots(*temp));
            }
            HirExpr::LocalRef(local) => {
                self.state.locals.insert(*local);
                self.state
                    .homes
                    .extend(self.promotion_facts.complete_local_home_slots(*local));
            }
            HirExpr::ParamRef(param) => {
                self.state
                    .homes
                    .extend(self.promotion_facts.complete_param_home_slots(*param));
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
        _ => BTreeSet::new(),
    };
    promotion_facts.complete_tbc_home_slots(to_be_closed.reg_index, value_homes)
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
        self.found |= !self.safety.is_discard_safe_without_residual(expr);
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
            record_single_home_write(writes, promotion_facts.complete_temp_home_slots(*temp));
        }
        HirLValue::Local(local) => record_local_write(writes, *local, promotion_facts),
        HirLValue::Param(param) => {
            record_single_home_write(writes, promotion_facts.complete_param_home_slots(*param))
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
    record_single_home_write(writes, promotion_facts.complete_local_home_slots(local));
}

fn record_single_home_write(writes: &mut LiveBindingState, homes: BTreeSet<HomeSlotKey>) {
    if homes.len() == 1 {
        writes.homes.extend(homes);
    }
}

#[derive(Default)]
struct LiveBindingCounts {
    temps: BTreeMap<TempId, usize>,
    locals: BTreeMap<LocalId, usize>,
    homes: BTreeMap<HomeSlotKey, usize>,
}

impl LiveBindingCounts {
    fn without(self, excluded: &Self) -> LiveBindingState {
        LiveBindingState {
            temps: remaining_keys(self.temps, &excluded.temps),
            locals: remaining_keys(self.locals, &excluded.locals),
            homes: remaining_keys(self.homes, &excluded.homes),
        }
    }
}

fn remaining_keys<K: Ord + Copy>(
    total: BTreeMap<K, usize>,
    excluded: &BTreeMap<K, usize>,
) -> BTreeSet<K> {
    total
        .into_iter()
        .filter_map(|(key, count)| {
            (count > excluded.get(&key).copied().unwrap_or(0)).then_some(key)
        })
        .collect()
}

struct LiveReadCollector<'a> {
    counts: LiveBindingCounts,
    promotion_facts: &'a ProtoPromotionFacts,
}

impl HirVisitor for LiveReadCollector<'_> {
    fn visit_expr(&mut self, expr: &HirExpr) {
        record_binding_read(&mut self.counts, expr, self.promotion_facts);
    }
}

struct ReferenceCaptureReadCollector<'a> {
    counts: LiveBindingCounts,
    promotion_facts: &'a ProtoPromotionFacts,
}

impl HirVisitor for ReferenceCaptureReadCollector<'_> {
    fn visit_expr(&mut self, expr: &HirExpr) {
        let HirExpr::Closure(closure) = expr else {
            return;
        };
        for capture in &closure.captures {
            if capture.mode != HirCaptureMode::ByReference {
                continue;
            }
            let mut bindings = CapturedBindingReadCollector {
                counts: &mut self.counts,
                promotion_facts: self.promotion_facts,
            };
            visit::visit_expr(&capture.value, &mut bindings);
        }
    }
}

struct CapturedBindingReadCollector<'a> {
    counts: &'a mut LiveBindingCounts,
    promotion_facts: &'a ProtoPromotionFacts,
}

impl HirVisitor for CapturedBindingReadCollector<'_> {
    fn visit_expr(&mut self, expr: &HirExpr) {
        record_binding_read(self.counts, expr, self.promotion_facts);
    }
}

fn record_binding_read(
    counts: &mut LiveBindingCounts,
    expr: &HirExpr,
    promotion_facts: &ProtoPromotionFacts,
) {
    let homes = match expr {
        HirExpr::TempRef(temp) => {
            *counts.temps.entry(*temp).or_default() += 1;
            None
        }
        HirExpr::LocalRef(local) => {
            *counts.locals.entry(*local).or_default() += 1;
            Some(promotion_facts.complete_local_home_slots(*local))
        }
        HirExpr::ParamRef(param) => Some(promotion_facts.complete_param_home_slots(*param)),
        _ => None,
    };
    for home in homes.into_iter().flatten() {
        *counts.homes.entry(home).or_default() += 1;
    }
}

fn solve_active_observers(nodes: &[LiveCfgNode], entry: usize) -> Vec<ActiveObserverState> {
    let mut predecessors = vec![BTreeSet::new(); nodes.len()];
    for (source, node) in nodes.iter().enumerate() {
        for successor in &node.successors {
            predecessors[*successor].insert(source);
        }
    }
    let mut active_in = vec![ActiveObserverState::default(); nodes.len()];
    let mut active_out = vec![ActiveObserverState::default(); nodes.len()];
    loop {
        let mut changed = false;
        for (id, node) in nodes.iter().enumerate() {
            let mut next_in = ActiveObserverState::default();
            for predecessor in &predecessors[id] {
                next_in.union_with(&active_out[*predecessor]);
            }
            if id != entry && predecessors[id].is_empty() {
                continue;
            }
            let next_out = next_in.after(node);
            changed |= next_in != active_in[id] || next_out != active_out[id];
            active_in[id] = next_in;
            active_out[id] = next_out;
        }
        if !changed {
            return active_in;
        }
    }
}

fn solve_live_out(nodes: &[LiveCfgNode]) -> Vec<LiveBindingState> {
    let mut live_in = vec![LiveBindingState::default(); nodes.len()];
    let mut live_out = vec![LiveBindingState::default(); nodes.len()];
    loop {
        let mut changed = false;
        for (index, node) in nodes.iter().enumerate().rev() {
            let mut next_out = LiveBindingState::default();
            for successor in &node.successors {
                next_out.union_with(&live_in[*successor]);
            }
            let mut next_in = next_out.clone().without_writes(&node.writes);
            next_in.union_with(&node.reads);
            changed |= next_out != live_out[index] || next_in != live_in[index];
            live_out[index] = next_out;
            live_in[index] = next_in;
        }
        if !changed {
            return live_out;
        }
    }
}

fn collect_shell_live_outs(
    block: &HirBlock,
    prefix: &[PathComponent],
    stmt_nodes: &BTreeMap<*const HirStmt, usize>,
    live_out: &[LiveBindingState],
    shells: &mut BTreeMap<StmtPath, ShellArmLiveOut>,
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
                        ShellArmLiveOut {
                            then_arm: live_out[stmt_nodes[&std::ptr::from_ref(then_stmt)]].clone(),
                            else_arm: live_out[stmt_nodes[&std::ptr::from_ref(else_stmt)]].clone(),
                        },
                    );
                }
                let mut then_prefix = path.clone();
                then_prefix.push(PathComponent::Then);
                collect_shell_live_outs(
                    &if_stmt.then_block,
                    &then_prefix,
                    stmt_nodes,
                    live_out,
                    shells,
                );
                if let Some(else_block) = &if_stmt.else_block {
                    let mut else_prefix = path.clone();
                    else_prefix.push(PathComponent::Else);
                    collect_shell_live_outs(else_block, &else_prefix, stmt_nodes, live_out, shells);
                }
            }
            HirStmt::While(while_stmt) => {
                collect_body_shell_live_outs(&while_stmt.body, &path, stmt_nodes, live_out, shells);
            }
            HirStmt::Repeat(repeat_stmt) => {
                collect_body_shell_live_outs(
                    &repeat_stmt.body,
                    &path,
                    stmt_nodes,
                    live_out,
                    shells,
                );
            }
            HirStmt::NumericFor(for_stmt) => {
                collect_body_shell_live_outs(&for_stmt.body, &path, stmt_nodes, live_out, shells);
            }
            HirStmt::GenericFor(for_stmt) => {
                collect_body_shell_live_outs(&for_stmt.body, &path, stmt_nodes, live_out, shells);
            }
            HirStmt::Block(nested) => {
                collect_body_shell_live_outs(nested, &path, stmt_nodes, live_out, shells);
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

fn collect_body_shell_live_outs(
    body: &HirBlock,
    path: &StmtPath,
    stmt_nodes: &BTreeMap<*const HirStmt, usize>,
    live_out: &[LiveBindingState],
    shells: &mut BTreeMap<StmtPath, ShellArmLiveOut>,
) {
    let mut prefix = path.clone();
    prefix.push(PathComponent::Body);
    collect_shell_live_outs(body, &prefix, stmt_nodes, live_out, shells);
}

#[derive(Default)]
pub(super) struct DeadShellPlan {
    removable: BTreeSet<StmtPath>,
    not_removable: BTreeSet<StmtPath>,
}

impl DeadShellPlan {
    pub(super) fn collect(
        proto: &HirProto,
        facts: &BooleanShellFacts,
        promotion_facts: &ProtoPromotionFacts,
        safety: HirExprSafety,
    ) -> Self {
        let mut candidates = CandidateValues {
            has_shell: false,
            locals: BTreeSet::new(),
            homes: BTreeSet::new(),
            entry_nil_homes: BTreeSet::new(),
            promotion_facts,
        };
        visit::visit_proto(proto, &mut candidates);
        if !candidates.has_shell {
            return Self::default();
        }
        let live_after = LiveAfterFacts::collect(proto, promotion_facts, safety);
        let owner_label_refs = count_label_references(&proto.body.stmts);

        let parameter_homes = proto
            .params
            .iter()
            .map(|param| HomeSlotKey::new(param.index(), 0))
            .collect::<BTreeSet<_>>();
        let initial_state = OldValueState::initial(&candidates, &parameter_homes);
        let mut analyzer = OldValueAnalyzer {
            facts,
            promotion_facts,
            safety,
            candidate_locals: candidates.locals,
            candidate_homes: candidates.homes,
            live_after,
            owner_label_refs: &owner_label_refs,
            plan: Self::default(),
        };
        let _ = analyzer.analyze_block(&proto.body, &[], Some(initial_state));
        analyzer.plan
    }

    pub(super) fn apply(self, block: &mut HirBlock) -> bool {
        if self.removable.is_empty() {
            return false;
        }
        apply_block_plan(block, &[], &self.removable);
        true
    }
}

struct CandidateValues<'a> {
    has_shell: bool,
    locals: BTreeSet<LocalId>,
    homes: BTreeSet<HomeSlotKey>,
    entry_nil_homes: BTreeSet<HomeSlotKey>,
    promotion_facts: &'a ProtoPromotionFacts,
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
        if let HirLValue::Local(local) = then_target {
            self.locals.insert(*local);
        }
        if let HirLValue::Temp(temp) = then_target {
            let homes = self.promotion_facts.complete_temp_home_slots(*temp);
            self.homes.extend(homes.iter().copied());
            if homes.len() == 1 && self.promotion_facts.overwrites_entry_nil(*temp) {
                self.entry_nil_homes.extend(homes);
            }
        }
        if let HirLValue::Local(local) = else_target {
            self.locals.insert(*local);
        }
        if let HirLValue::Temp(temp) = else_target {
            let homes = self.promotion_facts.complete_temp_home_slots(*temp);
            self.homes.extend(homes.iter().copied());
            if homes.len() == 1 && self.promotion_facts.overwrites_entry_nil(*temp) {
                self.entry_nil_homes.extend(homes);
            }
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct OldValueState {
    local_classes: BTreeMap<LocalId, OldValueClass>,
    home_classes: BTreeMap<HomeSlotKey, OldValueClass>,
}

impl OldValueState {
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

    fn as_facts(&self) -> DeadShellOldValueFacts {
        DeadShellOldValueFacts {
            locals: self.local_classes.clone(),
            homes: self.home_classes.clone(),
        }
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

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct InertFlow {
    fallthrough: Option<OldValueState>,
    breaks: Option<OldValueState>,
    continues: Option<OldValueState>,
}

impl InertFlow {
    fn fallthrough(state: Option<OldValueState>) -> Self {
        Self {
            fallthrough: state,
            ..Self::default()
        }
    }
}

struct OldValueAnalyzer<'a> {
    facts: &'a BooleanShellFacts,
    promotion_facts: &'a ProtoPromotionFacts,
    safety: HirExprSafety,
    candidate_locals: BTreeSet<LocalId>,
    candidate_homes: BTreeSet<HomeSlotKey>,
    live_after: LiveAfterFacts,
    owner_label_refs: &'a BTreeMap<crate::hir::HirLabelId, usize>,
    plan: DeadShellPlan,
}

impl OldValueAnalyzer<'_> {
    fn analyze_block(
        &mut self,
        block: &HirBlock,
        prefix: &[PathComponent],
        mut state: Option<OldValueState>,
    ) -> InertFlow {
        let Ok(cfg) = LexicalCfg::analyze(&block.stmts, self.owner_label_refs, self.safety) else {
            return self.analyze_unstructured_block(block, prefix);
        };
        let Some(label_indices) = cfg.linear_forward_labels() else {
            return self.analyze_unstructured_block(block, prefix);
        };
        let mut breaks = None;
        let mut continues = None;
        let mut index = 0;
        while let Some(stmt) = block.stmts.get(index) {
            if state.is_none() {
                break;
            }
            if let HirStmt::Goto(goto) = stmt {
                index = *label_indices
                    .get(&goto.target)
                    .expect("validated forward goto must retain its local label");
                continue;
            }
            let mut path = prefix.to_vec();
            path.push(PathComponent::Stmt(index));
            let flow = self.analyze_stmt(stmt, &path, state.expect("reachable state checked"));
            state = flow.fallthrough;
            breaks = join_optional_states(breaks, flow.breaks);
            continues = join_optional_states(continues, flow.continues);
            index += 1;
        }
        InertFlow {
            fallthrough: state,
            breaks,
            continues,
        }
    }

    fn analyze_unstructured_block(
        &mut self,
        block: &HirBlock,
        prefix: &[PathComponent],
    ) -> InertFlow {
        let conservative = OldValueState {
            local_classes: self
                .candidate_locals
                .iter()
                .copied()
                .map(|local| (local, OldValueClass::MayCarryResource))
                .collect(),
            home_classes: self
                .candidate_homes
                .iter()
                .copied()
                .map(|home| (home, OldValueClass::MayCarryResource))
                .collect(),
        };
        let mut state = Some(conservative.clone());
        for (index, stmt) in block.stmts.iter().enumerate() {
            let mut path = prefix.to_vec();
            path.push(PathComponent::Stmt(index));
            if stmt_contains_nested_nonlocal_control(stmt) {
                self.analyze_unstructured_children(stmt, &path);
                // 分析停用[SemanticBarrier:ControlFlow]：label/goto 可绕过此前写入，回边还
                // 会带入上一轮值；`::L:: shell(x); x = {}; goto L` 的第二轮旧值可承载资源。
                state = Some(conservative.clone());
                continue;
            }
            let Some(incoming) = state.take() else {
                continue;
            };
            state = self.analyze_stmt(stmt, &path, incoming).fallthrough;
        }
        InertFlow {
            fallthrough: Some(conservative.clone()),
            breaks: Some(conservative.clone()),
            continues: Some(conservative),
        }
    }

    fn analyze_unstructured_children(&mut self, stmt: &HirStmt, path: &StmtPath) {
        match stmt {
            HirStmt::If(if_stmt) => {
                let mut then_prefix = path.clone();
                then_prefix.push(PathComponent::Then);
                let _ = self.analyze_unstructured_block(&if_stmt.then_block, &then_prefix);
                if let Some(else_block) = &if_stmt.else_block {
                    let mut else_prefix = path.clone();
                    else_prefix.push(PathComponent::Else);
                    let _ = self.analyze_unstructured_block(else_block, &else_prefix);
                }
            }
            HirStmt::While(while_stmt) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                let _ = self.analyze_unstructured_block(&while_stmt.body, &body_prefix);
            }
            HirStmt::Repeat(repeat_stmt) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                let _ = self.analyze_unstructured_block(&repeat_stmt.body, &body_prefix);
            }
            HirStmt::NumericFor(for_stmt) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                let _ = self.analyze_unstructured_block(&for_stmt.body, &body_prefix);
            }
            HirStmt::GenericFor(for_stmt) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                let _ = self.analyze_unstructured_block(&for_stmt.body, &body_prefix);
            }
            HirStmt::Block(nested) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                let _ = self.analyze_unstructured_block(nested, &body_prefix);
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

    fn analyze_stmt(&mut self, stmt: &HirStmt, path: &StmtPath, state: OldValueState) -> InertFlow {
        match stmt {
            HirStmt::LocalDecl(decl) => {
                InertFlow::fallthrough(Some(self.apply_local_decl(decl, state)))
            }
            HirStmt::Assign(assign) => {
                InertFlow::fallthrough(Some(self.apply_assignment(assign, state)))
            }
            HirStmt::If(if_stmt) => {
                let old_values = state.as_facts();
                let removable = self.live_after.shell(path).is_some_and(|live_after| {
                    super::removable_dead_materialization_shell(
                        stmt,
                        self.facts,
                        None,
                        &old_values,
                        live_after,
                        self.safety,
                    )
                });
                if matches!(
                    stmt,
                    HirStmt::If(if_stmt)
                        if if_stmt.else_block.as_ref().is_some_and(|else_block| {
                            super::single_fixed_assign_pattern(&if_stmt.then_block).is_some()
                                && super::single_fixed_assign_pattern(else_block).is_some()
                        })
                ) {
                    self.plan.observe(path, removable);
                }

                let mut then_prefix = path.clone();
                then_prefix.push(PathComponent::Then);
                let then_flow = if expr_truthiness(&if_stmt.cond, self.safety) == Some(false) {
                    InertFlow::default()
                } else {
                    self.analyze_block(&if_stmt.then_block, &then_prefix, Some(state.clone()))
                };
                let else_flow = if expr_truthiness(&if_stmt.cond, self.safety) == Some(true) {
                    InertFlow::default()
                } else if let Some(else_block) = &if_stmt.else_block {
                    let mut else_prefix = path.clone();
                    else_prefix.push(PathComponent::Else);
                    self.analyze_block(else_block, &else_prefix, Some(state))
                } else {
                    InertFlow::fallthrough(Some(state))
                };
                join_flows(then_flow, else_flow)
            }
            HirStmt::Block(block) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                self.analyze_block(block, &body_prefix, Some(state))
            }
            HirStmt::While(while_stmt) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                self.analyze_while(&while_stmt.body, &while_stmt.cond, &body_prefix, state)
            }
            HirStmt::Repeat(repeat_stmt) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                self.analyze_repeat(&repeat_stmt.body, &repeat_stmt.cond, &body_prefix, state)
            }
            HirStmt::NumericFor(for_stmt) => {
                let zero_exit = state.clone();
                let body_state =
                    self.write_local_binding(for_stmt.binding, OldValueClass::GcInert, state);
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                self.analyze_zero_or_more(
                    &for_stmt.body,
                    &body_prefix,
                    zero_exit,
                    body_state,
                    &[(for_stmt.binding, OldValueClass::GcInert)],
                )
            }
            HirStmt::GenericFor(for_stmt) => {
                let zero_exit = state.clone();
                let mut body_state = state;
                let binding_values = for_stmt
                    .bindings
                    .iter()
                    .copied()
                    .map(|binding| (binding, OldValueClass::MayCarryResource))
                    .collect::<Vec<_>>();
                for (binding, value_class) in &binding_values {
                    body_state = self.write_local_binding(*binding, *value_class, body_state);
                }
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                self.analyze_zero_or_more(
                    &for_stmt.body,
                    &body_prefix,
                    zero_exit,
                    body_state,
                    &binding_values,
                )
            }
            HirStmt::Return(_) => InertFlow::default(),
            HirStmt::Goto(_) => {
                unreachable!("block analyzer must consume validated forward gotos")
            }
            HirStmt::Break => InertFlow {
                breaks: Some(state),
                ..InertFlow::default()
            },
            HirStmt::Continue => InertFlow {
                continues: Some(state),
                ..InertFlow::default()
            },
            HirStmt::GlobalDecl(_) => {
                // The syntax node hides call-result/probe writes to raw VM slots, so home facts
                // cannot cross it. Lexical locals remain distinct bindings; reference-captured
                // locals are already rejected by the enclosing boolean-shell facts.
                InertFlow::fallthrough(Some(state.obscure_physical_homes()))
            }
            HirStmt::TableSetList(_)
            | HirStmt::ErrNil(_)
            | HirStmt::ToBeClosed(_)
            | HirStmt::Close(_)
            | HirStmt::CallStmt(_)
            | HirStmt::Label(_) => InertFlow::fallthrough(Some(state)),
        }
    }

    fn analyze_while(
        &mut self,
        body: &HirBlock,
        condition: &HirExpr,
        body_prefix: &[PathComponent],
        incoming: OldValueState,
    ) -> InertFlow {
        let truthiness = expr_truthiness(condition, self.safety);
        let mut entries = incoming.clone();
        let mut break_exits = None;
        loop {
            let body_flow = if truthiness == Some(false) {
                InertFlow::default()
            } else {
                self.analyze_block(body, body_prefix, Some(entries.clone()))
            };
            let back_edges = join_optional_states(body_flow.fallthrough, body_flow.continues);
            let next_entries = join_optional_states(Some(incoming.clone()), back_edges)
                .expect("loop entry always includes incoming state");
            let next_break_exits = join_optional_states(break_exits.clone(), body_flow.breaks);
            if next_entries == entries && next_break_exits == break_exits {
                let normal_exits = (truthiness != Some(true)).then_some(entries);
                return InertFlow::fallthrough(join_optional_states(normal_exits, break_exits));
            }
            entries = next_entries;
            break_exits = next_break_exits;
        }
    }

    fn analyze_repeat(
        &mut self,
        body: &HirBlock,
        condition: &HirExpr,
        body_prefix: &[PathComponent],
        incoming: OldValueState,
    ) -> InertFlow {
        let truthiness = expr_truthiness(condition, self.safety);
        let mut entries = incoming.clone();
        let mut break_exits = None;
        loop {
            let body_flow = self.analyze_block(body, body_prefix, Some(entries.clone()));
            let condition_states = join_optional_states(body_flow.fallthrough, body_flow.continues);
            let back_edges = if truthiness == Some(true) {
                None
            } else {
                condition_states.clone()
            };
            let next_entries = join_optional_states(Some(incoming.clone()), back_edges)
                .expect("repeat entry always includes incoming state");
            let next_break_exits = join_optional_states(break_exits.clone(), body_flow.breaks);
            if next_entries == entries && next_break_exits == break_exits {
                let normal_exits = if truthiness == Some(false) {
                    None
                } else {
                    condition_states
                };
                return InertFlow::fallthrough(join_optional_states(normal_exits, break_exits));
            }
            entries = next_entries;
            break_exits = next_break_exits;
        }
    }

    fn analyze_zero_or_more(
        &mut self,
        body: &HirBlock,
        body_prefix: &[PathComponent],
        zero_exit: OldValueState,
        initial_body_entry: OldValueState,
        bindings: &[(LocalId, OldValueClass)],
    ) -> InertFlow {
        let mut entries = initial_body_entry.clone();
        let mut break_exits = None;
        loop {
            let body_flow = self.analyze_block(body, body_prefix, Some(entries.clone()));
            let iteration_exits = join_optional_states(body_flow.fallthrough, body_flow.continues);
            let back_edges = iteration_exits.clone().map(|mut state| {
                for (binding, value_class) in bindings {
                    state = self.write_local_binding(*binding, *value_class, state);
                }
                state
            });
            let next_entries = join_optional_states(Some(initial_body_entry.clone()), back_edges)
                .expect("for body entry always includes first iteration");
            let next_break_exits = join_optional_states(break_exits.clone(), body_flow.breaks);
            if next_entries == entries && next_break_exits == break_exits {
                return InertFlow::fallthrough(join_optional_states(
                    join_optional_states(Some(zero_exit), iteration_exits),
                    break_exits,
                ));
            }
            entries = next_entries;
            break_exits = next_break_exits;
        }
    }

    fn apply_assignment(&self, assign: &HirAssign, mut state: OldValueState) -> OldValueState {
        for (index, target) in assign.targets.iter().enumerate() {
            state = self.write_target(
                target,
                assigned_value_class(assign, index, self.safety),
                state,
            );
        }
        state
    }

    fn apply_local_decl(&self, decl: &HirLocalDecl, mut state: OldValueState) -> OldValueState {
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
        state: OldValueState,
    ) -> OldValueState {
        self.write_target(&HirLValue::Local(binding), value_class, state)
    }

    fn write_target(
        &self,
        target: &HirLValue,
        value_class: OldValueClass,
        mut state: OldValueState,
    ) -> OldValueState {
        for candidate in &self.candidate_locals {
            match self.local_binding_relation(target, *candidate) {
                BindingRelation::None => {}
                BindingRelation::Possible => {
                    // `Possible` 表示该写可能命中 candidate，也可能完全不命中；后态必须
                    // 合流“保留旧值”和“写入新值”，不能用 Unknown 覆盖两端事实。
                    state.merge_possible_local_write(*candidate, value_class);
                }
                BindingRelation::Definite => {
                    state.local_classes.insert(*candidate, value_class);
                }
            }
        }
        for candidate in &self.candidate_homes {
            match self.home_binding_relation(target, *candidate) {
                BindingRelation::None => {}
                BindingRelation::Possible => {
                    state.merge_possible_home_write(*candidate, value_class);
                }
                BindingRelation::Definite => {
                    state.home_classes.insert(*candidate, value_class);
                }
            }
        }
        state
    }

    fn local_binding_relation(&self, target: &HirLValue, candidate: LocalId) -> BindingRelation {
        let candidate_home = self.promotion_facts.trusted_local_home_slot(candidate);
        let candidate_homes = self.promotion_facts.complete_local_home_slots(candidate);
        match target {
            HirLValue::Local(local) if *local == candidate => BindingRelation::Definite,
            HirLValue::Local(local) => possible_home_relation(
                candidate_home,
                Some(&candidate_homes),
                self.promotion_facts.trusted_local_home_slot(*local),
                Some(&self.promotion_facts.complete_local_home_slots(*local)),
            ),
            HirLValue::Param(param) => possible_home_relation(
                candidate_home,
                Some(&candidate_homes),
                self.promotion_facts.trusted_param_home_slot(*param),
                Some(&self.promotion_facts.complete_param_home_slots(*param)),
            ),
            HirLValue::Temp(temp) => possible_home_relation(
                candidate_home,
                Some(&candidate_homes),
                self.promotion_facts.trusted_temp_home_slot(*temp),
                Some(&self.promotion_facts.complete_temp_home_slots(*temp)),
            ),
            HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_) => {
                BindingRelation::None
            }
        }
    }

    fn home_binding_relation(&self, target: &HirLValue, candidate: HomeSlotKey) -> BindingRelation {
        match target {
            HirLValue::Temp(temp) => possible_home_relation(
                Some(candidate),
                None,
                self.promotion_facts.trusted_temp_home_slot(*temp),
                Some(&self.promotion_facts.complete_temp_home_slots(*temp)),
            ),
            HirLValue::Param(param) => possible_home_relation(
                Some(candidate),
                None,
                self.promotion_facts.trusted_param_home_slot(*param),
                Some(&self.promotion_facts.complete_param_home_slots(*param)),
            ),
            HirLValue::Local(local) => possible_home_relation(
                Some(candidate),
                None,
                self.promotion_facts.trusted_local_home_slot(*local),
                Some(&self.promotion_facts.complete_local_home_slots(*local)),
            ),
            HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_) => {
                BindingRelation::None
            }
        }
    }
}

impl DeadShellPlan {
    fn observe(&mut self, path: &StmtPath, removable: bool) {
        if removable && !self.not_removable.contains(path) {
            self.removable.insert(path.clone());
        } else if !removable {
            self.removable.remove(path);
            self.not_removable.insert(path.clone());
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

fn join_states(mut left: OldValueState, right: OldValueState) -> OldValueState {
    join_class_maps(&mut left.local_classes, right.local_classes);
    join_class_maps(&mut left.home_classes, right.home_classes);
    left
}

fn join_class_maps<K: Ord>(
    left: &mut BTreeMap<K, OldValueClass>,
    right: BTreeMap<K, OldValueClass>,
) {
    for (binding, left_class) in left.iter_mut() {
        let right_class = right
            .get(binding)
            .copied()
            .unwrap_or(OldValueClass::Unknown);
        *left_class = join_value_classes(*left_class, right_class);
    }
    for (binding, right_class) in right {
        left.entry(binding)
            .or_insert_with(|| join_value_classes(OldValueClass::Unknown, right_class));
    }
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

fn join_optional_states(
    left: Option<OldValueState>,
    right: Option<OldValueState>,
) -> Option<OldValueState> {
    match (left, right) {
        (Some(left), Some(right)) => Some(join_states(left, right)),
        (Some(state), None) | (None, Some(state)) => Some(state),
        (None, None) => None,
    }
}

fn join_flows(left: InertFlow, right: InertFlow) -> InertFlow {
    InertFlow {
        fallthrough: join_optional_states(left.fallthrough, right.fallthrough),
        breaks: join_optional_states(left.breaks, right.breaks),
        continues: join_optional_states(left.continues, right.continues),
    }
}

fn apply_block_plan(block: &mut HirBlock, prefix: &[PathComponent], plan: &BTreeSet<StmtPath>) {
    let mut remove = Vec::new();
    for (index, stmt) in block.stmts.iter_mut().enumerate() {
        let mut path = prefix.to_vec();
        path.push(PathComponent::Stmt(index));
        match stmt {
            HirStmt::If(if_stmt) => {
                let mut then_prefix = path.clone();
                then_prefix.push(PathComponent::Then);
                apply_block_plan(&mut if_stmt.then_block, &then_prefix, plan);
                if let Some(else_block) = &mut if_stmt.else_block {
                    let mut else_prefix = path.clone();
                    else_prefix.push(PathComponent::Else);
                    apply_block_plan(else_block, &else_prefix, plan);
                }
            }
            HirStmt::While(while_stmt) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                apply_block_plan(&mut while_stmt.body, &body_prefix, plan);
            }
            HirStmt::Repeat(repeat_stmt) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                apply_block_plan(&mut repeat_stmt.body, &body_prefix, plan);
            }
            HirStmt::NumericFor(for_stmt) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                apply_block_plan(&mut for_stmt.body, &body_prefix, plan);
            }
            HirStmt::GenericFor(for_stmt) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                apply_block_plan(&mut for_stmt.body, &body_prefix, plan);
            }
            HirStmt::Block(nested) => {
                let mut body_prefix = path.clone();
                body_prefix.push(PathComponent::Body);
                apply_block_plan(nested, &body_prefix, plan);
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
        if plan.contains(&path) {
            remove.push(index);
        }
    }
    for index in remove.into_iter().rev() {
        block.stmts.remove(index);
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use crate::hir::common::LocalId;
    use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

    use super::{CandidateValues, OldValueClass, OldValueState};

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
            locals: BTreeSet::from([pruned_local, unknown_local]),
            homes: BTreeSet::from([entry_nil_home, unknown_home, parameter_home]),
            entry_nil_homes: BTreeSet::from([entry_nil_home]),
            promotion_facts: &promotion_facts,
        };

        let state = OldValueState::initial(&candidates, &BTreeSet::from([parameter_home]));

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
