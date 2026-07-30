//! 这个文件承载 HIR 内部给 simplify 使用的 promotion facts。
//!
//! `locals` pass 只看 HIR 语法本身时，能判断“哪些 temp 正在沿别名链流动”，却不知道
//! “这个 temp 最早来自哪个词法槽位”。一旦某个 local 已经被 closure reference capture，
//! 后续同一词法槽位的新 def 就不该再长成新的 local，而应继续写回原绑定；按值 capture
//! 只保存当前快照，不激活这条 sticky 身份。`close` 之后复用同一个寄存器号已经是新的
//! 词法槽位，不能继续沿用旧 upvalue 的 local。
//!
//! 这里专门把那份“temp -> home slot”事实从 analyze 阶段带给 simplify：
//! - 它依赖 Dataflow 已经给出的 fixed def/reg 与 phi incoming 身份，以及
//!   Transformer 保留下来的 `close from rX` 词法边界
//! - 它不会重新做结构恢复，也不会把事实暴露成公开 HIR API
//! - 例子：`t0(slot 0, epoch 0)` 被闭包 capture 之后，后续同 epoch 的
//!   `t7(slot 0, epoch 0)` 与同槽 phi 会被 locals 认成同一个源码 local 的写回；
//!   若中间经过 `close from r0`，后续 `t8(slot 0, epoch 1)` 会被视为新的词法槽位

use crate::hir::common::{
    HirBlock, HirExpr, HirLValue, HirStmt, HirTableField, HirTableKey, TempId,
};
use crate::structure::{
    BlockRef, Cfg, DataflowFacts, GraphFacts, PhiId, PhiIncomingDisposition, SsaValue,
    StructurePlan,
};
use crate::transformer::{CaptureSource, InstrRef, LowInstr, LoweredProto, Reg};
use std::collections::{BTreeSet, VecDeque};

/// temp promotion 使用的词法槽位身份。
///
/// Lua VM 会在 `close from rX` 之后复用同一个寄存器号。单独用 `slot` 作为 local 身份
/// 会把已关闭 upvalue 和后续普通临时值混成同一个绑定，因此这里额外带上 close epoch。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(super) struct HomeSlotKey {
    slot: usize,
    epoch: usize,
}

/// capture / promotion 共用的物理槽词法 epoch。
///
/// `Close` 只结束经过该 CFG 路径的 upvalue。这里把 close 当作槽位身份的 SSA 定义，
/// 在 dominance frontier 建 merge epoch，再沿支配树给指令标注进入点身份；不能按线性
/// PC 给所有后缀指令累加边界，否则 break/continue cleanup 会污染 sibling 路径。
pub(super) struct SlotEpochFacts {
    epochs_by_reg: Vec<Option<SlotEpochFlow>>,
}

struct SlotEpochFlow {
    at_instr: Vec<usize>,
    spans_entry: bool,
}

impl SlotEpochFacts {
    pub(super) fn analyze(
        proto: &LoweredProto,
        cfg: &Cfg,
        graph: &GraphFacts,
        dataflow: &DataflowFacts,
    ) -> Self {
        let captured_regs = proto
            .instrs
            .iter()
            .filter_map(|instr| match instr {
                LowInstr::Closure(closure) => Some(&closure.captures),
                _ => None,
            })
            .flatten()
            .filter_map(|capture| match capture.source {
                CaptureSource::ByReference(reg) => Some(reg),
                CaptureSource::ByValue(_) | CaptureSource::Upvalue(_) => None,
            })
            .collect::<BTreeSet<_>>();
        let reg_count = captured_regs
            .iter()
            .map(|reg| reg.index() + 1)
            .max()
            .unwrap_or_default()
            .max(usize::from(proto.frame.max_stack_size));
        let mut epochs_by_reg = (0..reg_count).map(|_| None).collect::<Vec<_>>();
        for reg in captured_regs {
            epochs_by_reg[reg.index()] = Some(analyze_slot_epoch(proto, cfg, graph, dataflow, reg));
        }
        Self { epochs_by_reg }
    }

    pub(super) fn epoch_at(&self, reg: Reg, instr: InstrRef) -> usize {
        self.epochs_by_reg
            .get(reg.index())
            .and_then(Option::as_ref)
            .and_then(|flow| flow.at_instr.get(instr.index()))
            .copied()
            .unwrap_or_default()
    }

    pub(super) fn spans_entry(&self, reg: Reg) -> bool {
        self.epochs_by_reg
            .get(reg.index())
            .and_then(Option::as_ref)
            .is_none_or(|flow| flow.spans_entry)
    }

    pub(super) fn tracks_reference_capture(&self, reg: Reg) -> bool {
        self.epochs_by_reg
            .get(reg.index())
            .is_some_and(Option::is_some)
    }
}

fn analyze_slot_epoch(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph: &GraphFacts,
    dataflow: &DataflowFacts,
    reg: Reg,
) -> SlotEpochFlow {
    let close_blocks = proto
        .instrs
        .iter()
        .enumerate()
        .filter_map(|(instr_index, instr)| {
            let LowInstr::Close(close) = instr else {
                return None;
            };
            let block = cfg.instr_to_block[instr_index];
            (close.from.index() <= reg.index() && cfg.reachable_blocks.contains(&block))
                .then_some(block)
        })
        .collect::<BTreeSet<_>>();
    let merge_blocks = place_epoch_merges(cfg, graph, &close_blocks);
    let mut at_instr = vec![0; proto.instrs.len()];
    let mut stack = vec![0];
    let mut events = vec![EpochRenameEvent::Enter(cfg.entry_block)];

    while let Some(event) = events.pop() {
        match event {
            EpochRenameEvent::Exit(count) => stack.truncate(stack.len() - count),
            EpochRenameEvent::Enter(block) => {
                let mut pushed = 0;
                if merge_blocks.contains(&block) {
                    stack.push(1 + proto.instrs.len() + block.index());
                    pushed += 1;
                }
                let range = cfg.blocks[block.index()].instrs;
                for (instr_index, epoch) in at_instr
                    .iter_mut()
                    .enumerate()
                    .take(range.end())
                    .skip(range.start.index())
                {
                    *epoch = *stack.last().expect("epoch stack has entry identity");
                    if matches!(
                        proto.instrs[instr_index],
                        LowInstr::Close(close) if close.from.index() <= reg.index()
                    ) {
                        stack.push(1 + instr_index);
                        pushed += 1;
                    }
                }

                events.push(EpochRenameEvent::Exit(pushed));
                for child in graph.dominator_tree.children[block.index()].iter().rev() {
                    events.push(EpochRenameEvent::Enter(*child));
                }
            }
        }
    }

    let defs_span_entry = dataflow
        .defs
        .iter()
        .filter(|def| def.reg == reg)
        .all(|def| at_instr[def.instr.index()] == 0);
    let captures_span_entry = proto.instrs.iter().enumerate().all(|(instr_index, instr)| {
        let LowInstr::Closure(closure) = instr else {
            return true;
        };
        !closure
            .captures
            .iter()
            .any(|capture| capture.source == CaptureSource::ByReference(reg))
            || at_instr[instr_index] == 0
    });

    SlotEpochFlow {
        at_instr,
        spans_entry: defs_span_entry && captures_span_entry,
    }
}

fn place_epoch_merges(
    cfg: &Cfg,
    graph: &GraphFacts,
    close_blocks: &BTreeSet<BlockRef>,
) -> BTreeSet<BlockRef> {
    // loop 内的 Close 会先在 header 的 dominance frontier 合成 epoch，但 header
    // 可能同时支配下一轮 body 和循环外 continuation。循环外物理槽已经越过 cleanup，
    // 因此真实 exit target 也必须显式开始一个 merge epoch，不能继续继承 header 身份。
    let mut placed = graph
        .natural_loops
        .iter()
        .filter(|natural_loop| !natural_loop.blocks.is_disjoint(close_blocks))
        .flat_map(|natural_loop| {
            natural_loop.blocks.iter().flat_map(|block| {
                cfg.succs[block.index()].iter().filter_map(|edge_ref| {
                    let target = cfg.edges[edge_ref.index()].to;
                    (!natural_loop.blocks.contains(&target)
                        && cfg.reachable_blocks.contains(&target))
                    .then_some(target)
                })
            })
        })
        .collect::<BTreeSet<_>>();
    let mut pending = close_blocks.iter().copied().collect::<VecDeque<_>>();
    pending.extend(placed.iter().copied());
    while let Some(block) = pending.pop_front() {
        for frontier in graph.dominance_frontier_blocks(block) {
            if placed.insert(frontier) && !close_blocks.contains(&frontier) {
                pending.push_back(frontier);
            }
        }
    }

    if graph.natural_loops.iter().any(|natural_loop| {
        natural_loop.header == cfg.entry_block
            && natural_loop
                .blocks
                .iter()
                .any(|block| close_blocks.contains(block))
    }) {
        placed.insert(cfg.entry_block);
    }
    placed
}

enum EpochRenameEvent {
    Enter(BlockRef),
    Exit(usize),
}

impl HomeSlotKey {
    pub(super) const fn new(slot: usize, epoch: usize) -> Self {
        Self { slot, epoch }
    }
}

#[derive(Debug, Clone, Copy, Default, Eq, PartialEq)]
enum HomeSlotResolution {
    #[default]
    Unknown,
    Known(HomeSlotKey),
    Conflict,
}

/// 单个 proto 的 temp promotion 辅助事实。
#[derive(Debug, Clone, Default)]
pub(super) struct ProtoPromotionFacts {
    temp_home_slots: Vec<Option<HomeSlotKey>>,
    local_home_slots: Vec<HomeSlotResolution>,
    compact_home_slots: bool,
}

impl ProtoPromotionFacts {
    /// 从 canonical def 与最终 value plan 提取当前 proto 的 temp -> home slot 对照表。
    pub(super) fn from_plan(
        dataflow: &DataflowFacts,
        plan: &StructurePlan,
        slot_epochs: &SlotEpochFacts,
    ) -> Self {
        let total_temps = dataflow.defs.len() + plan.phis().len();
        let mut temp_home_slots = vec![None; total_temps];

        fill_fixed_def_home_slots(dataflow, slot_epochs, &mut temp_home_slots);
        fill_phi_home_slots(dataflow, plan, &mut temp_home_slots);

        Self {
            temp_home_slots,
            local_home_slots: Vec::new(),
            compact_home_slots: false,
        }
    }

    /// 返回某个 temp 对应的原始寄存器槽位。
    pub(super) fn home_slot(&self, temp: TempId) -> Option<HomeSlotKey> {
        self.temp_home_slots.get(temp.index()).copied().flatten()
    }

    pub(super) fn home_slot_definition_count(&self) -> usize {
        self.temp_home_slots.iter().flatten().count()
    }

    /// 返回 temp 提升后 local 仍对应的原始词法槽位。
    ///
    /// 同一 local 若吸收过不同槽位会永久标为 conflict；后续 pass 不能再把它作为
    /// 跨 region 合并的物理身份依据。
    pub(super) fn local_home_slot(
        &self,
        local: crate::hir::common::LocalId,
    ) -> Option<HomeSlotKey> {
        match self.local_home_slots.get(local.index()) {
            Some(HomeSlotResolution::Known(slot)) => Some(*slot),
            Some(HomeSlotResolution::Unknown | HomeSlotResolution::Conflict) | None => None,
        }
    }

    pub(super) fn record_local_home_slot(
        &mut self,
        local: crate::hir::common::LocalId,
        home_slot: HomeSlotKey,
    ) {
        if self.local_home_slots.len() <= local.index() {
            self.local_home_slots
                .resize(local.index() + 1, HomeSlotResolution::Unknown);
        }
        let resolution = &mut self.local_home_slots[local.index()];
        *resolution =
            merge_home_slot_resolutions(*resolution, HomeSlotResolution::Known(home_slot));
    }

    pub(super) fn enable_home_slot_compaction(&mut self) {
        self.compact_home_slots = true;
    }

    pub(super) const fn compacts_home_slots(&self) -> bool {
        self.compact_home_slots
    }

    /// 把当前语句里所有 closure capture 观察到的 home slot 收集进集合。
    pub(super) fn collect_captured_home_slots_in_stmt(
        &self,
        stmt: &HirStmt,
        slots: &mut BTreeSet<HomeSlotKey>,
    ) {
        match stmt {
            HirStmt::LocalDecl(local_decl) => {
                for value in &local_decl.values {
                    self.collect_captured_home_slots_in_expr(value, slots);
                }
            }
            HirStmt::Assign(assign) => {
                for target in &assign.targets {
                    if let HirLValue::TableAccess(access) = target {
                        self.collect_captured_home_slots_in_expr(&access.base, slots);
                        self.collect_captured_home_slots_in_expr(&access.key, slots);
                    }
                }
                for value in &assign.values {
                    self.collect_captured_home_slots_in_expr(value, slots);
                }
            }
            HirStmt::TableSetList(set_list) => {
                self.collect_captured_home_slots_in_expr(&set_list.base, slots);
                for value in &set_list.values {
                    self.collect_captured_home_slots_in_expr(value, slots);
                }
            }
            HirStmt::ErrNil(err_nil) => {
                self.collect_captured_home_slots_in_expr(&err_nil.value, slots);
            }
            HirStmt::ToBeClosed(to_be_closed) => {
                self.collect_captured_home_slots_in_expr(&to_be_closed.value, slots);
            }
            HirStmt::CallStmt(call_stmt) => {
                self.collect_captured_home_slots_in_expr(&call_stmt.call.callee, slots);
                for arg in &call_stmt.call.args {
                    self.collect_captured_home_slots_in_expr(arg, slots);
                }
            }
            HirStmt::Return(ret) => {
                for value in &ret.values {
                    self.collect_captured_home_slots_in_expr(value, slots);
                }
            }
            HirStmt::If(if_stmt) => {
                self.collect_captured_home_slots_in_expr(&if_stmt.cond, slots);
                self.collect_captured_home_slots_in_block(&if_stmt.then_block, slots);
                if let Some(else_block) = &if_stmt.else_block {
                    self.collect_captured_home_slots_in_block(else_block, slots);
                }
            }
            HirStmt::While(while_stmt) => {
                self.collect_captured_home_slots_in_expr(&while_stmt.cond, slots);
                self.collect_captured_home_slots_in_block(&while_stmt.body, slots);
            }
            HirStmt::Repeat(repeat_stmt) => {
                self.collect_captured_home_slots_in_block(&repeat_stmt.body, slots);
                self.collect_captured_home_slots_in_expr(&repeat_stmt.cond, slots);
            }
            HirStmt::NumericFor(numeric_for) => {
                self.collect_captured_home_slots_in_expr(&numeric_for.start, slots);
                self.collect_captured_home_slots_in_expr(&numeric_for.limit, slots);
                self.collect_captured_home_slots_in_expr(&numeric_for.step, slots);
                self.collect_captured_home_slots_in_block(&numeric_for.body, slots);
            }
            HirStmt::GenericFor(generic_for) => {
                for iterator in &generic_for.iterator {
                    self.collect_captured_home_slots_in_expr(iterator, slots);
                }
                self.collect_captured_home_slots_in_block(&generic_for.body, slots);
            }
            HirStmt::Block(block) => self.collect_captured_home_slots_in_block(block, slots),
            HirStmt::Break
            | HirStmt::Close(_)
            | HirStmt::Continue
            | HirStmt::Goto(_)
            | HirStmt::Label(_) => {}
        }
    }

    /// 只收集在进入嵌套 block 之前就会执行到的 capture。
    pub(super) fn collect_prefix_captured_home_slots_in_stmt(
        &self,
        stmt: &HirStmt,
        slots: &mut BTreeSet<HomeSlotKey>,
    ) {
        match stmt {
            HirStmt::If(if_stmt) => self.collect_captured_home_slots_in_expr(&if_stmt.cond, slots),
            HirStmt::While(while_stmt) => {
                self.collect_captured_home_slots_in_expr(&while_stmt.cond, slots);
            }
            HirStmt::NumericFor(numeric_for) => {
                self.collect_captured_home_slots_in_expr(&numeric_for.start, slots);
                self.collect_captured_home_slots_in_expr(&numeric_for.limit, slots);
                self.collect_captured_home_slots_in_expr(&numeric_for.step, slots);
            }
            HirStmt::GenericFor(generic_for) => {
                for iterator in &generic_for.iterator {
                    self.collect_captured_home_slots_in_expr(iterator, slots);
                }
            }
            HirStmt::LocalDecl(_)
            | HirStmt::Assign(_)
            | HirStmt::TableSetList(_)
            | HirStmt::ErrNil(_)
            | HirStmt::ToBeClosed(_)
            | HirStmt::CallStmt(_)
            | HirStmt::Return(_)
            | HirStmt::Repeat(_)
            | HirStmt::Block(_)
            | HirStmt::Break
            | HirStmt::Close(_)
            | HirStmt::Continue
            | HirStmt::Goto(_)
            | HirStmt::Label(_) => {}
        }
    }

    fn collect_captured_home_slots_in_block(
        &self,
        block: &HirBlock,
        slots: &mut BTreeSet<HomeSlotKey>,
    ) {
        for stmt in &block.stmts {
            self.collect_captured_home_slots_in_stmt(stmt, slots);
        }
    }

    fn collect_captured_home_slots_in_expr(
        &self,
        expr: &HirExpr,
        slots: &mut BTreeSet<HomeSlotKey>,
    ) {
        match expr {
            HirExpr::TableAccess(access) => {
                self.collect_captured_home_slots_in_expr(&access.base, slots);
                self.collect_captured_home_slots_in_expr(&access.key, slots);
            }
            HirExpr::Unary(unary) => self.collect_captured_home_slots_in_expr(&unary.expr, slots),
            HirExpr::Binary(binary) => {
                self.collect_captured_home_slots_in_expr(&binary.lhs, slots);
                self.collect_captured_home_slots_in_expr(&binary.rhs, slots);
            }
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                self.collect_captured_home_slots_in_expr(&logical.lhs, slots);
                self.collect_captured_home_slots_in_expr(&logical.rhs, slots);
            }
            HirExpr::Decision(decision) => {
                for node in &decision.nodes {
                    self.collect_captured_home_slots_in_expr(&node.test, slots);
                    self.collect_captured_home_slots_in_decision_target(&node.truthy, slots);
                    self.collect_captured_home_slots_in_decision_target(&node.falsy, slots);
                }
            }
            HirExpr::Call(call) => {
                self.collect_captured_home_slots_in_expr(&call.callee, slots);
                for arg in &call.args {
                    self.collect_captured_home_slots_in_expr(arg, slots);
                }
            }
            HirExpr::TableConstructor(table) => {
                for field in &table.fields {
                    match field {
                        HirTableField::Array(value) => {
                            self.collect_captured_home_slots_in_expr(value, slots);
                        }
                        HirTableField::Record(field) => {
                            if let HirTableKey::Expr(key) = &field.key {
                                self.collect_captured_home_slots_in_expr(key, slots);
                            }
                            self.collect_captured_home_slots_in_expr(&field.value, slots);
                        }
                    }
                }
                if let Some(trailing) = &table.trailing_multivalue {
                    self.collect_captured_home_slots_in_expr(trailing.as_expr(), slots);
                }
            }
            HirExpr::Closure(closure) => {
                for capture in &closure.captures {
                    if capture.mode == crate::hir::common::HirCaptureMode::ByReference {
                        self.collect_temp_home_slots_in_expr(&capture.value, slots);
                    }
                    self.collect_captured_home_slots_in_expr(&capture.value, slots);
                }
            }
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
            | HirExpr::VarArg
            | HirExpr::Unresolved(_) => {}
        }
    }

    fn collect_captured_home_slots_in_decision_target(
        &self,
        target: &crate::hir::common::HirDecisionTarget,
        slots: &mut BTreeSet<HomeSlotKey>,
    ) {
        if let crate::hir::common::HirDecisionTarget::Expr(expr) = target {
            self.collect_captured_home_slots_in_expr(expr, slots);
        }
    }

    fn collect_temp_home_slots_in_expr(&self, expr: &HirExpr, slots: &mut BTreeSet<HomeSlotKey>) {
        match expr {
            HirExpr::TempRef(temp) => {
                if let Some(slot) = self.home_slot(*temp) {
                    slots.insert(slot);
                }
            }
            HirExpr::TableAccess(access) => {
                self.collect_temp_home_slots_in_expr(&access.base, slots);
                self.collect_temp_home_slots_in_expr(&access.key, slots);
            }
            HirExpr::Unary(unary) => self.collect_temp_home_slots_in_expr(&unary.expr, slots),
            HirExpr::Binary(binary) => {
                self.collect_temp_home_slots_in_expr(&binary.lhs, slots);
                self.collect_temp_home_slots_in_expr(&binary.rhs, slots);
            }
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                self.collect_temp_home_slots_in_expr(&logical.lhs, slots);
                self.collect_temp_home_slots_in_expr(&logical.rhs, slots);
            }
            HirExpr::Decision(decision) => {
                for node in &decision.nodes {
                    self.collect_temp_home_slots_in_expr(&node.test, slots);
                    self.collect_temp_home_slots_in_decision_target(&node.truthy, slots);
                    self.collect_temp_home_slots_in_decision_target(&node.falsy, slots);
                }
            }
            HirExpr::Call(call) => {
                self.collect_temp_home_slots_in_expr(&call.callee, slots);
                for arg in &call.args {
                    self.collect_temp_home_slots_in_expr(arg, slots);
                }
            }
            HirExpr::TableConstructor(table) => {
                for field in &table.fields {
                    match field {
                        HirTableField::Array(value) => {
                            self.collect_temp_home_slots_in_expr(value, slots);
                        }
                        HirTableField::Record(field) => {
                            if let HirTableKey::Expr(key) = &field.key {
                                self.collect_temp_home_slots_in_expr(key, slots);
                            }
                            self.collect_temp_home_slots_in_expr(&field.value, slots);
                        }
                    }
                }
                if let Some(trailing) = &table.trailing_multivalue {
                    self.collect_temp_home_slots_in_expr(trailing.as_expr(), slots);
                }
            }
            HirExpr::Closure(closure) => {
                for capture in &closure.captures {
                    self.collect_temp_home_slots_in_expr(&capture.value, slots);
                }
            }
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
            | HirExpr::GlobalRef(_)
            | HirExpr::VarArg
            | HirExpr::Unresolved(_) => {}
        }
    }

    fn collect_temp_home_slots_in_decision_target(
        &self,
        target: &crate::hir::common::HirDecisionTarget,
        slots: &mut BTreeSet<HomeSlotKey>,
    ) {
        if let crate::hir::common::HirDecisionTarget::Expr(expr) = target {
            self.collect_temp_home_slots_in_expr(expr, slots);
        }
    }
}

fn fill_fixed_def_home_slots(
    dataflow: &DataflowFacts,
    slot_epochs: &SlotEpochFacts,
    temp_home_slots: &mut [Option<HomeSlotKey>],
) {
    for def in &dataflow.defs {
        let epoch = slot_epochs.epoch_at(def.reg, def.instr);
        temp_home_slots[def.id.index()] = Some(HomeSlotKey::new(def.reg.index(), epoch));
    }
}

fn fill_phi_home_slots(
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    temp_home_slots: &mut [Option<HomeSlotKey>],
) {
    let phi_count = plan.phis().len();
    let mut resolutions = vec![HomeSlotResolution::Unknown; phi_count];
    let mut consumers = vec![Vec::<PhiId>::new(); phi_count];
    let mut pending = VecDeque::<(PhiId, HomeSlotResolution)>::new();

    for phi in plan.phis() {
        let mut resolution = HomeSlotResolution::Unknown;
        for incoming in &phi.incomings {
            match incoming.disposition {
                PhiIncomingDisposition::Dead => continue,
                PhiIncomingDisposition::DiagnosticUnresolved => {
                    resolution = HomeSlotResolution::Conflict;
                    continue;
                }
                PhiIncomingDisposition::RegionInput(_)
                | PhiIncomingDisposition::RegionResult(_)
                | PhiIncomingDisposition::LoopCarried(_)
                | PhiIncomingDisposition::EdgeCopy => {}
            }
            if let SsaValue::Phi(source) = incoming.value {
                if let Some(source_consumers) = consumers.get_mut(source.index()) {
                    source_consumers.push(phi.phi);
                }
                continue;
            }
            resolution = merge_home_slot_resolutions(
                resolution,
                home_slot_resolution_for_leaf(incoming.value, temp_home_slots),
            );
        }
        let Some(slot) = resolutions.get_mut(phi.phi.index()) else {
            continue;
        };
        *slot = resolution;
        if !matches!(resolution, HomeSlotResolution::Unknown) {
            pending.push_back((phi.phi, resolution));
        }
    }

    // resolution 只会 Unknown -> Known -> Conflict，每条依赖边最多处理两次。
    while let Some((phi_id, source_resolution)) = pending.pop_front() {
        let Some(phi_consumers) = consumers.get(phi_id.index()) else {
            continue;
        };
        for consumer in phi_consumers {
            let Some(resolution) = resolutions.get_mut(consumer.index()) else {
                continue;
            };
            let merged = merge_home_slot_resolutions(*resolution, source_resolution);
            if merged != *resolution {
                *resolution = merged;
                pending.push_back((*consumer, merged));
            }
        }
    }

    // 纯 phi 环没有已知 leaf；依赖该环的后续 phi 也不能只凭其它 incoming
    // 继承 home slot。在反向索引上做一次闭包，避免重新扫描 incoming。
    let mut unresolved = VecDeque::new();
    let mut invalid = vec![false; phi_count];
    for (index, resolution) in resolutions.iter().enumerate() {
        if matches!(resolution, HomeSlotResolution::Unknown) {
            invalid[index] = true;
            unresolved.push_back(PhiId(index));
        }
    }
    while let Some(phi_id) = unresolved.pop_front() {
        let Some(phi_consumers) = consumers.get(phi_id.index()) else {
            continue;
        };
        for consumer in phi_consumers {
            let Some(is_invalid) = invalid.get_mut(consumer.index()) else {
                continue;
            };
            if *is_invalid {
                continue;
            }
            *is_invalid = true;
            if let Some(resolution) = resolutions.get_mut(consumer.index()) {
                *resolution = HomeSlotResolution::Conflict;
            }
            unresolved.push_back(*consumer);
        }
    }

    let phi_temp_offset = dataflow.defs.len();
    for (phi_index, resolution) in resolutions.into_iter().enumerate() {
        if let HomeSlotResolution::Known(slot) = resolution
            && let Some(home_slot) = temp_home_slots.get_mut(phi_temp_offset + phi_index)
        {
            *home_slot = Some(slot);
        }
    }
}

fn home_slot_resolution_for_leaf(
    value: SsaValue,
    temp_home_slots: &[Option<HomeSlotKey>],
) -> HomeSlotResolution {
    match value {
        SsaValue::Entry(reg) => HomeSlotResolution::Known(HomeSlotKey::new(reg.index(), 0)),
        SsaValue::Def(def) => temp_home_slots
            .get(def.index())
            .copied()
            .flatten()
            .map_or(HomeSlotResolution::Unknown, HomeSlotResolution::Known),
        SsaValue::Phi(_) => HomeSlotResolution::Unknown,
    }
}

fn merge_home_slot_resolutions(
    left: HomeSlotResolution,
    right: HomeSlotResolution,
) -> HomeSlotResolution {
    match (left, right) {
        (HomeSlotResolution::Conflict, _) | (_, HomeSlotResolution::Conflict) => {
            HomeSlotResolution::Conflict
        }
        (HomeSlotResolution::Unknown, known) | (known, HomeSlotResolution::Unknown) => known,
        (HomeSlotResolution::Known(left), HomeSlotResolution::Known(right)) if left == right => {
            HomeSlotResolution::Known(left)
        }
        (HomeSlotResolution::Known(_), HomeSlotResolution::Known(_)) => {
            HomeSlotResolution::Conflict
        }
    }
}
