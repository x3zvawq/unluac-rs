//! 轻量 Close-Epoch 槽位模型 + Pruned SSA 构建与 Def-Use 索引。
//!
//! 区分 Pinned 具名槽（按引用捕获、`<close>`、源码 debug local）与普通 SSA 临时值；
//! 不模拟 VM 物理残值或死栈槽 GC 生命周期。

use std::collections::{BTreeMap, BTreeSet};

use crate::transformer::{
    AccessBase, AccessKey, BranchSubject, CaptureSource, CloseKind, CondOperand, InstrRef,
    LowInstr, LoweredProto, Reg, ResultPack, ValueOperand, ValuePack,
};

use super::cfg::{BlockId, Cfg, EdgeId};
use super::graph_facts::GraphFacts;

/// 寄存器 + Close-Epoch 构成的词法槽位身份。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SlotKey {
    pub reg: Reg,
    pub epoch: u32,
}

/// SSA 值唯一编号。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ValueId(pub usize);

impl ValueId {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// Phi 节点唯一编号。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PhiId(pub usize);

impl PhiId {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// SSA 值来源。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SsaDef {
    /// 函数形参（0..num_params）。
    Param { index: usize, reg: Reg },
    /// 入口隐式变参表寄存器（Lua 5.1 `arg` 或 Lua 5.5 具名变参）。
    VarArgParam { reg: Reg },
    /// 入口未初始化槽位（安全兜底为 nil）。
    Undef { reg: Reg },
    /// 指令定值。
    Instr {
        instr: InstrRef,
        block: BlockId,
        reg: Reg,
        /// 在多结果指令中的偏移（0 为首个结果）。
        result_index: usize,
        slot: SlotKey,
    },
    /// 控制流汇合 Phi。
    Phi { phi: PhiId, block: BlockId, slot: SlotKey },
}

/// 值使用点。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UseSite {
    Instr { instr: InstrRef, block: BlockId },
    Phi { phi: PhiId, edge: EdgeId },
}

/// SSA Phi 节点。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PhiNode {
    pub id: PhiId,
    pub block: BlockId,
    pub reg: Reg,
    pub slot: SlotKey,
    pub value: ValueId,
    pub incomings: Vec<(EdgeId, ValueId)>,
}

/// 单个 proto 的完整 SSA 与槽位信息。
#[derive(Debug, Clone)]
pub struct SsaForm {
    pub max_reg: usize,
    /// 每条指令处的寄存器 Close-Epoch 映射（只记录被显式 CLOSE 影响的寄存器递增）。
    pub instr_epoch_base: Vec<Vec<u32>>,
    /// 需保留独立变量身份的槽位（按引用捕获、`<close>`）。
    pub pinned_slots: BTreeSet<SlotKey>,
    /// 精确到 SSA 值粒度的 pinned 集合（仅包含真正被按引用捕获/`<close>` 的值及其写回/Phi 连通分量，
    /// 不误杀在捕获变量声明之前借用同一物理寄存器的无关前序临时值）。
    pub pinned_values: BTreeSet<ValueId>,
    /// 被按引用捕获的槽位集合。
    pub ref_captured_slots: BTreeSet<SlotKey>,
    /// 标记了 `<close>` 的槽位集合。
    pub tbc_slots: BTreeSet<SlotKey>,
    /// 精确到 SSA 值粒度的 `<close>` 绑定集合（不误标同槽关闭后复用的普通变量）。
    pub tbc_values: BTreeSet<ValueId>,
    /// 所有 SSA 值的定义信息（按 ValueId 索引）。
    pub defs: Vec<SsaDef>,
    /// 每个 SSA 值的使用点集合（按 ValueId 索引）。
    pub uses: Vec<Vec<UseSite>>,
    /// 所有 Phi 节点（按 PhiId 索引）。
    pub phis: Vec<PhiNode>,
    /// 每个基本块入口处的 Phi 列表。
    pub block_phis: Vec<Vec<PhiId>>,
    /// 每条指令产出的固定 SSA 值（按结果顺序）。
    pub instr_defs: Vec<Vec<(Reg, ValueId)>>,
    /// 每条指令读取的寄存器 -> SSA 值映射。
    pub instr_uses: Vec<Vec<(Reg, ValueId)>>,
    /// 入口参数对应的 SSA 值。
    pub param_values: Vec<ValueId>,
    /// Lua 5.1 `arg` 或 Lua 5.5 具名变参槽的入口 SSA 值。
    pub vararg_param_value: Option<(Reg, ValueId)>,
}

impl SsaForm {
    pub fn slot_at(&self, instr: InstrRef, reg: Reg) -> SlotKey {
        let epoch = self
            .instr_epoch_base
            .get(instr.index())
            .and_then(|row| row.get(reg.index()))
            .copied()
            .unwrap_or(0);
        SlotKey { reg, epoch }
    }

    pub fn use_count(&self, value: ValueId) -> usize {
        self.uses[value.index()].len()
    }

    pub fn def_of(&self, value: ValueId) -> SsaDef {
        self.defs[value.index()]
    }

    pub fn instr_use_value(&self, instr: InstrRef, reg: Reg) -> Option<ValueId> {
        self.instr_uses[instr.index()]
            .iter()
            .find(|(r, _)| *r == reg)
            .map(|(_, v)| *v)
    }

    pub fn instr_def_value(&self, instr: InstrRef, reg: Reg) -> Option<ValueId> {
        self.instr_defs[instr.index()]
            .iter()
            .find(|(r, _)| *r == reg)
            .map(|(_, v)| *v)
    }
}

/// 计算指令读取的寄存器集合（含开放多值包前缀槽 `consume_start..=link.start`）。
pub(crate) fn instr_reads_with_open(
    iref: InstrRef,
    instr: &LowInstr,
    open_pack_by_consumer: &BTreeMap<InstrRef, super::dataflow::OpenPackLink>,
    out: &mut Vec<Reg>,
) {
    out.clear();
    let push_val = |v: ValueOperand, out: &mut Vec<Reg>| {
        if let ValueOperand::Reg(r) = v {
            out.push(r);
        }
    };
    let push_cond = |c: CondOperand, out: &mut Vec<Reg>| {
        if let CondOperand::Reg(r) = c {
            out.push(r);
        }
    };
    let push_base = |b: AccessBase, out: &mut Vec<Reg>| {
        if let AccessBase::Reg(r) = b {
            out.push(r);
        }
    };
    let push_key = |k: AccessKey, out: &mut Vec<Reg>| {
        if let AccessKey::Reg(r) = k {
            out.push(r);
        }
    };
    let push_pack = |pack: ValuePack, out: &mut Vec<Reg>| match pack {
        ValuePack::Fixed(range) => {
            for offset in 0..range.len {
                out.push(Reg(range.start.index() + offset));
            }
        }
        ValuePack::Open(consume_start) => {
            // 开放多值包覆盖 consume_start..link.start 的全部固定前缀寄存器 + link.start 开放尾包！
            if let Some(link) = open_pack_by_consumer.get(&iref)
                && link.start.index() >= consume_start.index()
            {
                for r in consume_start.index()..=link.start.index() {
                    out.push(Reg(r));
                }
            } else {
                out.push(consume_start);
            }
        }
    };

    match instr {
        LowInstr::Move(i) => out.push(i.src),
        LowInstr::UnaryOp(i) => out.push(i.src),
        LowInstr::BinaryOp(i) => {
            push_val(i.lhs, out);
            push_val(i.rhs, out);
        }
        LowInstr::Concat(i) => {
            for offset in 0..i.src.len {
                out.push(Reg(i.src.start.index() + offset));
            }
        }
        LowInstr::SetUpvalue(i) => push_val(i.src, out),
        LowInstr::GetTable(i) => {
            push_base(i.base, out);
            push_key(i.key, out);
        }
        LowInstr::SetTable(i) => {
            push_base(i.base, out);
            push_key(i.key, out);
            push_val(i.value, out);
        }
        LowInstr::ErrNil(i) => out.push(i.subject),
        LowInstr::TypeGuard(i) => out.push(i.subject),
        LowInstr::SetList(i) => {
            out.push(i.base);
            push_pack(i.values, out);
        }
        LowInstr::Call(i) => {
            out.push(i.callee);
            push_pack(i.args, out);
        }
        LowInstr::TailCall(i) => {
            out.push(i.callee);
            push_pack(i.args, out);
        }
        LowInstr::Return(i) => push_pack(i.values, out),
        LowInstr::Closure(i) => {
            for cap in &i.captures {
                match cap.source {
                    // 自捕获（`CAPTURE VAL/REF dst`，如 Luau 递归 `local function f() ... f() end`）
                    // 读取的是本条 `Closure` 刚写入 `i.dst` 的新值，绝不能按指令前旧寄存器值计为读操作！
                    CaptureSource::ByValue(r) | CaptureSource::ByReference(r) if r != i.dst => {
                        out.push(r)
                    }
                    CaptureSource::ByValue(_)
                    | CaptureSource::ByReference(_)
                    | CaptureSource::Upvalue(_) => {}
                }
            }
        }
        LowInstr::Tbc(i) => out.push(i.reg),
        LowInstr::NumericForInit(i) => {
            out.push(i.index);
            out.push(i.limit);
            out.push(i.step);
        }
        LowInstr::NumericForLoop(i) => {
            out.push(i.index);
            out.push(i.limit);
            out.push(i.step);
        }
        LowInstr::GenericForPrep(i) => {
            out.push(i.iterator);
            out.push(i.state);
            out.push(i.control_source);
            out.push(i.closing_source);
        }
        LowInstr::GenericForCall(i) => {
            out.push(i.iterator);
            out.push(i.state);
            out.push(i.control);
        }
        LowInstr::GenericForLoop(i) => {
            for offset in 0..i.bindings.len {
                out.push(Reg(i.bindings.start.index() + offset));
            }
        }
        LowInstr::Branch(i) => match i.cond.subject {
            BranchSubject::Truthy(op) => push_cond(op, out),
            BranchSubject::Compare { lhs, rhs, .. } => {
                push_cond(lhs, out);
                push_cond(rhs, out);
            }
        },
        LowInstr::LoadNil(_)
        | LowInstr::LoadBool(_)
        | LowInstr::LoadConst(_)
        | LowInstr::LoadInteger(_)
        | LowInstr::LoadNumber(_)
        | LowInstr::GetUpvalue(_)
        | LowInstr::NewTable(_)
        | LowInstr::VarArg(_)
        | LowInstr::Close(_)
        | LowInstr::Jump(_) => {}
    }
}

/// 计算指令写入的寄存器集合。
pub(crate) fn instr_fixed_defs(instr: &LowInstr, out: &mut Vec<Reg>) {
    out.clear();
    let push_results = |pack: ResultPack, out: &mut Vec<Reg>| match pack {
        ResultPack::Fixed(range) => {
            for offset in 0..range.len {
                out.push(Reg(range.start.index() + offset));
            }
        }
        ResultPack::Open(start) => out.push(start),
        ResultPack::Ignore => {}
    };

    match instr {
        LowInstr::Move(i) => out.push(i.dst),
        LowInstr::LoadNil(i) => {
            for offset in 0..i.dst.len {
                out.push(Reg(i.dst.start.index() + offset));
            }
        }
        LowInstr::LoadBool(i) => out.push(i.dst),
        LowInstr::LoadConst(i) => out.push(i.dst),
        LowInstr::LoadInteger(i) => out.push(i.dst),
        LowInstr::LoadNumber(i) => out.push(i.dst),
        LowInstr::UnaryOp(i) => out.push(i.dst),
        LowInstr::BinaryOp(i) => out.push(i.dst),
        LowInstr::Concat(i) => out.push(i.dst),
        LowInstr::GetUpvalue(i) => out.push(i.dst),
        LowInstr::GetTable(i) => out.push(i.dst),
        LowInstr::NewTable(i) => out.push(i.dst),
        LowInstr::Call(i) => push_results(i.results, out),
        LowInstr::VarArg(i) => push_results(i.results, out),
        LowInstr::Closure(i) => out.push(i.dst),
        LowInstr::TypeGuard(i) if i.kind.normalizes_subject() => out.push(i.subject),
        LowInstr::NumericForInit(i) => {
            out.push(i.index);
            if i.binding != i.index {
                out.push(i.binding);
            }
        }
        LowInstr::NumericForLoop(i) => {
            out.push(i.index);
            if i.binding != i.index {
                out.push(i.binding);
            }
        }
        LowInstr::GenericForPrep(i) => {
            out.push(i.control_target);
            if i.closing_target != i.control_target {
                out.push(i.closing_target);
            }
        }
        LowInstr::GenericForCall(i) => push_results(i.results, out),
        LowInstr::GenericForLoop(i) => {
            // Lua 5.5 中 `TFORCALL` 直接把首循环变量写入控制槽（`control_target == bindings.start`），
            // `TFORLOOP` 本身仅判断非 nil 跳转而不写入新值；跳过重复定值避免循环体读到脱离 `GenericForCall` 的新 SSA 版本！
            if i.bindings.len == 0 || i.control_target != i.bindings.start {
                out.push(i.control_target);
            }
        }
        LowInstr::SetUpvalue(_)
        | LowInstr::SetTable(_)
        | LowInstr::ErrNil(_)
        | LowInstr::TypeGuard(_)
        | LowInstr::SetList(_)
        | LowInstr::TailCall(_)
        | LowInstr::Return(_)
        | LowInstr::Close(_)
        | LowInstr::Tbc(_)
        | LowInstr::Jump(_)
        | LowInstr::Branch(_) => {}
    }
}

/// 构建单个 proto 的 Pruned SSA 形式。
pub(crate) fn build_ssa(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph: &GraphFacts,
    open_pack_by_consumer: &BTreeMap<InstrRef, super::dataflow::OpenPackLink>,
) -> SsaForm {
    let mut max_reg = usize::from(proto.frame.max_stack_size).max(usize::from(proto.signature.num_params));
    if proto.signature.has_vararg_param_reg {
        max_reg = max_reg.max(usize::from(proto.signature.num_params) + 1);
    }
    let mut reads_buf = Vec::new();
    let mut defs_buf = Vec::new();
    for (idx, instr) in proto.instrs.iter().enumerate() {
        instr_reads_with_open(InstrRef(idx), instr, open_pack_by_consumer, &mut reads_buf);
        instr_fixed_defs(instr, &mut defs_buf);
        for &r in reads_buf.iter().chain(defs_buf.iter()) {
            max_reg = max_reg.max(r.index() + 1);
        }
    }

    // 1. 计算 Close-Epoch（去回边 DAG 上的 3 态格前向传播：Unseen / Open(e) / Closed(e)）。
    //    - 仅沿非回边传播显式 CLOSE，确保分支内 `if stop then break end` 的 CLOSE 不污染兄弟路径；
    //    - 同时保证循环退出点（`Unseen ⊔ Closed(e) = Closed(e)`）在循环结束后推进 epoch，
    //      使循环外复用物理槽的局部变量与循环内被捕获变量彻底隔离。
    let mut instr_epoch_base = vec![vec![0u32; max_reg]; proto.instrs.len()];
    let mut has_ref_capture_reg = vec![false; max_reg];
    for instr in &proto.instrs {
        match instr {
            LowInstr::Closure(c) => {
                for cap in &c.captures {
                    if let CaptureSource::ByReference(r) = cap.source {
                        has_ref_capture_reg[r.index()] = true;
                    }
                }
            }
            LowInstr::Tbc(t) => {
                has_ref_capture_reg[t.reg.index()] = true;
            }
            _ => {}
        }
    }
    if has_ref_capture_reg.iter().any(|&v| v) {
        #[derive(Clone, Copy, PartialEq, Eq)]
        enum EpochState {
            Unseen,
            Open(u32),
            Closed(u32),
        }
        impl EpochState {
            fn epoch(self) -> u32 {
                match self {
                    Self::Unseen => 0,
                    Self::Open(e) | Self::Closed(e) => e,
                }
            }
            fn join(self, other: Self) -> Self {
                match (self, other) {
                    (Self::Unseen, x) | (x, Self::Unseen) => x,
                    (Self::Open(a), Self::Open(b)) => Self::Open(a.min(b)),
                    (Self::Open(e), Self::Closed(_)) | (Self::Closed(_), Self::Open(e)) => {
                        Self::Open(e)
                    }
                    (Self::Closed(a), Self::Closed(b)) => Self::Closed(a.max(b)),
                }
            }
        }

        // 为每条显式 Close 指令分配唯一固定的递增 epoch 编号（保证单调收敛）
        let mut close_epoch_id = vec![0u32; proto.instrs.len()];
        let mut next_close_id = 1u32;
        for &block in &cfg.block_order {
            for iref in cfg.blocks[block.index()].instrs.iter() {
                if let LowInstr::Close(close) = &proto.instrs[iref.index()]
                    && close.kind == CloseKind::Explicit
                {
                    close_epoch_id[iref.index()] = next_close_id;
                    next_close_id = next_close_id.saturating_add(1);
                }
            }
        }

        // 为每个循环（含自然循环与 `NumericFor`/`GenericFor` 协议循环）预计算循环体内显式 CLOSE
        // 对每个寄存器的最大 close_epoch_id：若循环体内关闭了循环私有捕获槽（进入循环头时非 `Open`），
        // 离开该循环的退出边必须推进 epoch，避免循环后复用同一物理寄存器的无关捕获变量撞成同一 `SlotKey`！
        let block_count = cfg.blocks.len();
        let mut loop_regions: Vec<(BlockId, BTreeSet<BlockId>)> = graph
            .natural_loops
            .iter()
            .map(|nl| (nl.header, nl.blocks.iter().copied().collect()))
            .collect();
        if !cfg.loop_protocols.is_empty() {
            // 一次构建支配树子表，按 `body_entry` 子树精确收集协议循环体，消除 O(L × B) 全图扫描。
            let mut dom_children: Vec<Vec<BlockId>> = vec![Vec::new(); block_count];
            for (b_idx, parent_opt) in graph.dom.parent.iter().enumerate() {
                if let Some(parent) = *parent_opt
                    && parent.index() != b_idx
                {
                    dom_children[parent.index()].push(BlockId(b_idx));
                }
            }
            let collect_dom_subtree = |root: BlockId| -> BTreeSet<BlockId> {
                let mut blocks = BTreeSet::new();
                if graph.dom.preorder_index.get(root.index()).copied().flatten().is_none() {
                    return blocks;
                }
                let mut stack = vec![root];
                while let Some(b) = stack.pop() {
                    if blocks.insert(b) {
                        stack.extend(dom_children[b.index()].iter().copied());
                    }
                }
                blocks
            };
            for hint in &cfg.loop_protocols {
                match hint {
                    super::cfg::LoopProtocolHint::NumericFor { body_entry, .. } => {
                        let blocks = collect_dom_subtree(*body_entry);
                        if !blocks.is_empty() {
                            loop_regions.push((*body_entry, blocks));
                        }
                    }
                    super::cfg::LoopProtocolHint::GenericFor {
                        header_block,
                        body_entry,
                        ..
                    } => {
                        let mut blocks = collect_dom_subtree(*body_entry);
                        blocks.insert(*header_block);
                        loop_regions.push((*header_block, blocks));
                    }
                }
            }
        }
        let mut loop_close_max: Vec<Vec<u32>> = vec![vec![0u32; max_reg]; loop_regions.len()];
        let mut block_loops: Vec<Vec<usize>> = vec![Vec::new(); block_count];
        for (li, (_, blocks)) in loop_regions.iter().enumerate() {
            for &b in blocks {
                block_loops[b.index()].push(li);
                for iref in cfg.blocks[b.index()].instrs.iter() {
                    if let LowInstr::Close(close) = &proto.instrs[iref.index()]
                        && close.kind == CloseKind::Explicit
                    {
                        let cid = close_epoch_id[iref.index()];
                        for r in close.from.index()..max_reg {
                            if has_ref_capture_reg[r] {
                                loop_close_max[li][r] = loop_close_max[li][r].max(cid);
                            }
                        }
                    }
                }
            }
        }

        let mut in_state: Vec<Vec<EpochState>> =
            vec![vec![EpochState::Unseen; max_reg]; block_count];
        let mut out_state: Vec<Vec<EpochState>> =
            vec![vec![EpochState::Unseen; max_reg]; block_count];
        for &block in &cfg.block_order {
            let bi = block.index();
            let mut cur = vec![EpochState::Unseen; max_reg];
            for pred in cfg.reachable_preds(block) {
                // 不沿循环回边把循环尾的 CLOSE 传回循环头
                if graph.dominates(block, pred.from) {
                    continue;
                }
                let p_out = &out_state[pred.from.index()];
                for r in 0..max_reg {
                    if has_ref_capture_reg[r] {
                        cur[r] = cur[r].join(p_out[r]);
                    }
                }
                // 若 pred.from -> block 离开某个循环 L，把 L 内部关闭循环私有槽的 epoch 推进到退出块
                for &li in &block_loops[pred.from.index()] {
                    let (header, ref blocks) = loop_regions[li];
                    if !blocks.contains(&block) {
                        let header_in = &in_state[header.index()];
                        for r in 0..max_reg {
                            let cid = loop_close_max[li][r];
                            if cid > 0 && !matches!(header_in[r], EpochState::Open(_)) {
                                cur[r] = cur[r].join(EpochState::Closed(cid));
                            }
                        }
                    }
                }
            }
            in_state[bi] = cur.clone();

            for iref in cfg.blocks[bi].instrs.iter() {
                for r in 0..max_reg {
                    if has_ref_capture_reg[r] {
                        instr_epoch_base[iref.index()][r] = cur[r].epoch();
                    }
                }
                match &proto.instrs[iref.index()] {
                    LowInstr::Closure(c) => {
                        for cap in &c.captures {
                            if let CaptureSource::ByReference(r) = cap.source {
                                let ri = r.index();
                                cur[ri] = match cur[ri] {
                                    EpochState::Unseen => EpochState::Open(0),
                                    EpochState::Closed(e) | EpochState::Open(e) => {
                                        EpochState::Open(e)
                                    }
                                };
                            }
                        }
                    }
                    LowInstr::Tbc(t) => {
                        let ri = t.reg.index();
                        cur[ri] = match cur[ri] {
                            EpochState::Unseen => EpochState::Open(0),
                            EpochState::Closed(e) | EpochState::Open(e) => EpochState::Open(e),
                        };
                    }
                    LowInstr::Close(close) if close.kind == CloseKind::Explicit => {
                        let cid = close_epoch_id[iref.index()];
                        for r in close.from.index()..max_reg {
                            if has_ref_capture_reg[r] {
                                cur[r] = EpochState::Closed(cid);
                            }
                        }
                    }
                    _ => {}
                }
            }
            out_state[bi] = cur;
        }
    }

    // 2. 收集 Pinned 槽位（按引用捕获、`<close>`）
    let mut ref_captured_slots = BTreeSet::new();
    let mut tbc_slots = BTreeSet::new();
    let mut pinned_slots = BTreeSet::new();
    for &block in &cfg.block_order {
        for iref in cfg.blocks[block.index()].instrs.iter() {
            match &proto.instrs[iref.index()] {
                LowInstr::Closure(c) => {
                    for cap in &c.captures {
                        if let CaptureSource::ByReference(r) = cap.source {
                            let slot = SlotKey {
                                reg: r,
                                epoch: instr_epoch_base[iref.index()][r.index()],
                            };
                            ref_captured_slots.insert(slot);
                            pinned_slots.insert(slot);
                        }
                    }
                }
                LowInstr::Tbc(t) => {
                    let slot = SlotKey {
                        reg: t.reg,
                        epoch: instr_epoch_base[iref.index()][t.reg.index()],
                    };
                    tbc_slots.insert(slot);
                    pinned_slots.insert(slot);
                }
                _ => {}
            }
        }
    }

    // 3. 计算基本块级 Def / Use 与活跃性（Pruned SSA 基础）
    let block_count = cfg.blocks.len();
    let mut block_use = vec![vec![false; max_reg]; block_count];
    let mut block_def = vec![vec![false; max_reg]; block_count];
    let mut def_blocks_by_reg: Vec<Vec<BlockId>> = vec![Vec::new(); max_reg];

    for &block in &cfg.block_order {
        let bi = block.index();
        for iref in cfg.blocks[bi].instrs.iter() {
            let instr = &proto.instrs[iref.index()];
            instr_reads_with_open(iref, instr, open_pack_by_consumer, &mut reads_buf);
            for &r in &reads_buf {
                if !block_def[bi][r.index()] {
                    block_use[bi][r.index()] = true;
                }
            }
            instr_fixed_defs(instr, &mut defs_buf);
            for &r in &defs_buf {
                if !block_def[bi][r.index()] {
                    block_def[bi][r.index()] = true;
                    def_blocks_by_reg[r.index()].push(block);
                }
            }
        }
    }
    // 入口块隐式定义形参寄存器
    for p in 0..usize::from(proto.signature.num_params) {
        if !block_def[cfg.entry_block.index()][p] {
            def_blocks_by_reg[p].push(cfg.entry_block);
        }
    }
    if proto.signature.has_vararg_param_reg {
        let vr = usize::from(proto.signature.num_params);
        if vr < max_reg && !block_def[cfg.entry_block.index()][vr] {
            def_blocks_by_reg[vr].push(cfg.entry_block);
        }
    }

    // 后向迭代计算 live_in / live_out
    let mut live_in = vec![vec![false; max_reg]; block_count];
    let mut live_out = vec![vec![false; max_reg]; block_count];
    let mut changed = true;
    while changed {
        changed = false;
        for &block in cfg.block_order.iter().rev() {
            let bi = block.index();
            for r in 0..max_reg {
                let mut out_r = false;
                for succ in cfg.succ_blocks(block) {
                    if live_in[succ.index()][r] {
                        out_r = true;
                        break;
                    }
                }
                if out_r != live_out[bi][r] {
                    live_out[bi][r] = out_r;
                    changed = true;
                }
                let in_r = block_use[bi][r] || (out_r && !block_def[bi][r]);
                if in_r != live_in[bi][r] {
                    live_in[bi][r] = in_r;
                    changed = true;
                }
            }
        }
    }

    // 4. Cytron 支配边界插入 Pruned Phi
    let mut phis: Vec<PhiNode> = Vec::new();
    let mut block_phis: Vec<Vec<PhiId>> = vec![Vec::new(); block_count];
    let mut defs: Vec<SsaDef> = Vec::new();

    for (reg_idx, def_blocks) in def_blocks_by_reg.iter().enumerate() {
        let mut has_phi = vec![false; block_count];
        let mut in_worklist = vec![false; block_count];
        let mut worklist = Vec::new();
        for &b in def_blocks {
            if !in_worklist[b.index()] {
                in_worklist[b.index()] = true;
                worklist.push(b);
            }
        }
        while let Some(b) = worklist.pop() {
            for &df_block in &graph.dom_frontier[b.index()] {
                if df_block == cfg.exit_block || has_phi[df_block.index()] {
                    continue;
                }
                if !live_in[df_block.index()][reg_idx] {
                    continue;
                }
                has_phi[df_block.index()] = true;
                let phi_id = PhiId(phis.len());
                let val_id = ValueId(defs.len());
                let epoch = cfg.blocks[df_block.index()]
                    .instrs
                    .iter()
                    .next()
                    .map(|ir| instr_epoch_base[ir.index()][reg_idx])
                    .unwrap_or(0);
                let slot = SlotKey {
                    reg: Reg(reg_idx),
                    epoch,
                };
                defs.push(SsaDef::Phi {
                    phi: phi_id,
                    block: df_block,
                    slot,
                });
                phis.push(PhiNode {
                    id: phi_id,
                    block: df_block,
                    reg: Reg(reg_idx),
                    slot,
                    value: val_id,
                    incomings: Vec::new(),
                });
                block_phis[df_block.index()].push(phi_id);
                if !in_worklist[df_block.index()] {
                    in_worklist[df_block.index()] = true;
                    worklist.push(df_block);
                }
            }
        }
    }

    // 5. 支配树显式栈重命名
    let mut param_values = Vec::with_capacity(usize::from(proto.signature.num_params));
    let mut stacks: Vec<Vec<ValueId>> = vec![Vec::new(); max_reg];

    for (p, stack) in stacks.iter_mut().enumerate().take(usize::from(proto.signature.num_params)) {
        let v = ValueId(defs.len());
        defs.push(SsaDef::Param {
            index: p,
            reg: Reg(p),
        });
        param_values.push(v);
        stack.push(v);
    }
    let vararg_param_value = if proto.signature.has_vararg_param_reg {
        let vr = Reg(usize::from(proto.signature.num_params));
        let v = ValueId(defs.len());
        defs.push(SsaDef::VarArgParam { reg: vr });
        stacks[vr.index()].push(v);
        Some((vr, v))
    } else {
        None
    };

    let mut undef_by_reg: Vec<Option<ValueId>> = vec![None; max_reg];
    let mut instr_defs = vec![Vec::new(); proto.instrs.len()];
    let mut instr_uses = vec![Vec::new(); proto.instrs.len()];

    enum RenameEvent {
        Enter(BlockId),
        Leave(Vec<usize>),
    }

    let mut work = vec![RenameEvent::Enter(cfg.entry_block)];
    while let Some(event) = work.pop() {
        match event {
            RenameEvent::Leave(pushed_regs) => {
                for r in pushed_regs {
                    stacks[r].pop();
                }
            }
            RenameEvent::Enter(block) => {
                let mut pushed_regs = Vec::new();
                // 1) 压入本块 Phi 定值
                for &phi_id in &block_phis[block.index()] {
                    let phi = &phis[phi_id.index()];
                    stacks[phi.reg.index()].push(phi.value);
                    pushed_regs.push(phi.reg.index());
                }

                // 2) 重命名本块指令
                for iref in cfg.blocks[block.index()].instrs.iter() {
                    let instr = &proto.instrs[iref.index()];
                    instr_reads_with_open(iref, instr, open_pack_by_consumer, &mut reads_buf);
                    let mut urow = Vec::with_capacity(reads_buf.len());
                    for &r in &reads_buf {
                        let v = if let Some(&top) = stacks[r.index()].last() {
                            top
                        } else {
                            *undef_by_reg[r.index()].get_or_insert_with(|| {
                                let id = ValueId(defs.len());
                                defs.push(SsaDef::Undef { reg: r });
                                id
                            })
                        };
                        urow.push((r, v));
                    }
                    instr_uses[iref.index()] = urow;

                    instr_fixed_defs(instr, &mut defs_buf);
                    let mut drow = Vec::with_capacity(defs_buf.len());
                    for (result_index, &r) in defs_buf.iter().enumerate() {
                        let id = ValueId(defs.len());
                        let slot = SlotKey {
                            reg: r,
                            epoch: instr_epoch_base[iref.index()][r.index()],
                        };
                        defs.push(SsaDef::Instr {
                            instr: iref,
                            block,
                            reg: r,
                            result_index,
                            slot,
                        });
                        stacks[r.index()].push(id);
                        pushed_regs.push(r.index());
                        drow.push((r, id));
                    }
                    instr_defs[iref.index()] = drow;
                }

                // 3) 回填后继块 Phi 的 incoming 边
                for &eid in &cfg.succs[block.index()] {
                    let succ = cfg.edges[eid.index()].to;
                    for &phi_id in &block_phis[succ.index()] {
                        let reg = phis[phi_id.index()].reg;
                        let v = if let Some(&top) = stacks[reg.index()].last() {
                            top
                        } else {
                            *undef_by_reg[reg.index()].get_or_insert_with(|| {
                                let id = ValueId(defs.len());
                                defs.push(SsaDef::Undef { reg });
                                id
                            })
                        };
                        phis[phi_id.index()].incomings.push((eid, v));
                    }
                }

                // 4) 先压入 Leave，再逆序压入支配树子节点
                work.push(RenameEvent::Leave(pushed_regs));
                for &child in graph.dom.children[block.index()].iter().rev() {
                    work.push(RenameEvent::Enter(child));
                }
            }
        }
    }

    // 6. 构建精确 Def-Use 索引
    let mut uses = vec![Vec::new(); defs.len()];
    for &block in &cfg.block_order {
        for iref in cfg.blocks[block.index()].instrs.iter() {
            for &(_, v) in &instr_uses[iref.index()] {
                uses[v.index()].push(UseSite::Instr {
                    instr: iref,
                    block,
                });
            }
        }
    }
    for phi in &phis {
        for &(edge, v) in &phi.incomings {
            uses[v.index()].push(UseSite::Phi { phi: phi.id, edge });
        }
    }

    // 7. 计算精确 SSA 值级 `pinned_values`：
    //    仅覆盖真正被 ByReference 捕获 / <close> 的值、其 Phi 连通分量、以及捕获之后同 SlotKey 下的后续写回，
    //    绝不把捕获变量声明之前借用同一物理寄存器的无关临时表达式误标为 pinned！
    let mut pinned_values: BTreeSet<ValueId> = BTreeSet::new();
    let mut tbc_values: BTreeSet<ValueId> = BTreeSet::new();
    let mut capture_sites_by_slot: BTreeMap<SlotKey, Vec<(BlockId, InstrRef)>> = BTreeMap::new();
    for &block in &cfg.block_order {
        for iref in cfg.blocks[block.index()].instrs.iter() {
            match &proto.instrs[iref.index()] {
                LowInstr::Closure(c) => {
                    for cap in &c.captures {
                        match cap.source {
                            CaptureSource::ByReference(r) => {
                                let slot = SlotKey {
                                    reg: r,
                                    epoch: instr_epoch_base[iref.index()][r.index()],
                                };
                                if let Some((_, uv)) =
                                    instr_uses[iref.index()].iter().find(|(ur, _)| *ur == r)
                                {
                                    pinned_values.insert(*uv);
                                }
                                if c.dst == r
                                    && let Some((_, dv)) =
                                        instr_defs[iref.index()].iter().find(|(dr, _)| *dr == r)
                                {
                                    pinned_values.insert(*dv);
                                }
                                capture_sites_by_slot
                                    .entry(slot)
                                    .or_default()
                                    .push((block, iref));
                            }
                            // Luau 递归自按值捕获 `CAPTURE VAL dst`：闭包自身必须物化为具名局部，绝不能匿名内联！
                            CaptureSource::ByValue(r) if r == c.dst => {
                                if let Some((_, dv)) =
                                    instr_defs[iref.index()].iter().find(|(dr, _)| *dr == r)
                                {
                                    pinned_values.insert(*dv);
                                }
                            }
                            CaptureSource::ByValue(_) | CaptureSource::Upvalue(_) => {}
                        }
                    }
                }
                LowInstr::Tbc(t) => {
                    // `<close>` 变量在 Lua 5.4/5.5 中是只读 const：只固定其初始化定义值，
                    // 绝不把后续复用了该寄存器的无关写入合并进 `<close>` 变量！
                    if let Some((_, uv)) = instr_uses[iref.index()]
                        .iter()
                        .find(|(ur, _)| *ur == t.reg)
                    {
                        pinned_values.insert(*uv);
                        tbc_values.insert(*uv);
                    }
                }
                _ => {}
            }
        }
    }

    // 7a) 从每个捕获点正向搜索同 SlotKey（未跨 Close-Epoch）的后续写回定值。
    // 同块内多次捕获同一槽位只需从该块最早的捕获指令扫描一次，消除大块海量闭包上的 Θ(S × K) 退化！
    for (&slot, sites) in &capture_sites_by_slot {
        let mut earliest_by_block: BTreeMap<BlockId, InstrRef> = BTreeMap::new();
        for &(start_block, start_iref) in sites {
            earliest_by_block
                .entry(start_block)
                .and_modify(|cur| {
                    if start_iref.index() < cur.index() {
                        *cur = start_iref;
                    }
                })
                .or_insert(start_iref);
        }
        let mut visited_blocks: BTreeSet<BlockId> = BTreeSet::new();
        let mut work_blocks: Vec<BlockId> = Vec::new();
        for (start_block, start_iref) in earliest_by_block {
            // 同块内位于最早捕获点之后的同槽定值
            let range = cfg.blocks[start_block.index()].instrs;
            let mut still_same_epoch = true;
            for idx in (start_iref.index() + 1)..range.end() {
                let iref = InstrRef(idx);
                if instr_epoch_base[iref.index()][slot.reg.index()] != slot.epoch {
                    still_same_epoch = false;
                    break;
                }
                if let Some((_, dv)) = instr_defs[iref.index()]
                    .iter()
                    .find(|(dr, _)| *dr == slot.reg)
                {
                    pinned_values.insert(*dv);
                }
            }
            if still_same_epoch {
                for succ in cfg.succ_blocks(start_block) {
                    if succ != cfg.exit_block && visited_blocks.insert(succ) {
                        work_blocks.push(succ);
                    }
                }
            }
        }
        while let Some(b) = work_blocks.pop() {
            let mut still_same_epoch = true;
            for iref in cfg.blocks[b.index()].instrs.iter() {
                if instr_epoch_base[iref.index()][slot.reg.index()] != slot.epoch {
                    still_same_epoch = false;
                    break;
                }
                if let Some((_, dv)) = instr_defs[iref.index()]
                    .iter()
                    .find(|(dr, _)| *dr == slot.reg)
                {
                    pinned_values.insert(*dv);
                }
            }
            if still_same_epoch {
                for succ in cfg.succ_blocks(b) {
                    if succ != cfg.exit_block && visited_blocks.insert(succ) {
                        work_blocks.push(succ);
                    }
                }
            }
        }
    }

    // 7b) 沿同槽 Phi 双向闭包扩展 pinned_values
    loop {
        let mut expanded = false;
        for phi in &phis {
            if !pinned_slots.contains(&phi.slot) {
                continue;
            }
            let touches = pinned_values.contains(&phi.value)
                || phi
                    .incomings
                    .iter()
                    .any(|&(_, v)| pinned_values.contains(&v));
            if touches {
                if pinned_values.insert(phi.value) {
                    expanded = true;
                }
                for &(_, v) in &phi.incomings {
                    if !matches!(defs[v.index()], SsaDef::Undef { .. }) && pinned_values.insert(v) {
                        expanded = true;
                    }
                }
            }
        }
        if !expanded {
            break;
        }
    }

    SsaForm {
        max_reg,
        instr_epoch_base,
        pinned_slots,
        pinned_values,
        ref_captured_slots,
        tbc_slots,
        tbc_values,
        defs,
        uses,
        phis,
        block_phis,
        instr_defs,
        instr_uses,
        param_values,
        vararg_param_value,
    }
}

/// 便捷查询：从 DebugLocal 事实收集寄存器对应的源码名称提示映射。
pub(crate) fn collect_debug_slot_hints(
    proto: &LoweredProto,
    cfg: &Cfg,
    ssa: &SsaForm,
) -> BTreeMap<SlotKey, String> {
    let mut hints = BTreeMap::new();
    for local in proto.debug_locals.iter() {
        if !local.is_source() {
            continue;
        }
        let Ok(name) = std::str::from_utf8(&local.name.bytes) else {
            continue;
        };
        if name.is_empty() || name.starts_with('(') {
            continue;
        }
        let iref = proto
            .lowering_map
            .low_instr_at_or_after_pc(local.start_pc)
            .filter(|ir| cfg.block_of_instr.get(ir.index()).copied().flatten().is_some());
        let slot = iref
            .map(|ir| ssa.slot_at(ir, local.reg))
            .unwrap_or(SlotKey {
                reg: local.reg,
                epoch: 0,
            });
        hints.entry(slot).or_insert_with(|| name.to_owned());
    }
    hints
}
