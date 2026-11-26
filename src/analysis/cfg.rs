//! 从统一 Low-IR 构建规范化 CFG，并标注显式 VM 循环与布尔加载模式。
//!
//! 产出的 `Cfg` 与 `CfgGraph` 既服务于图论/SSA/结构化分析，也直接投影给 Web 工作区视图。

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::transformer::{InstrRef, LowInstr, LoweredProto, Reg, RegRange};

use super::AnalysisError;

/// CFG 基本块 ID。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct BlockId(pub usize);

impl BlockId {
    pub const fn index(self) -> usize {
        self.0
    }
}

impl fmt::Display for BlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "B{}", self.0)
    }
}

/// CFG 边 ID。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct EdgeId(pub usize);

impl EdgeId {
    pub const fn index(self) -> usize {
        self.0
    }
}

impl fmt::Display for EdgeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "E{}", self.0)
    }
}

/// 基本块角色。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BlockKind {
    Entry,
    Normal,
    Exit,
}

impl BlockKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Entry => "entry",
            Self::Normal => "normal",
            Self::Exit => "exit",
        }
    }
}

/// CFG 边类型。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EdgeKind {
    Fallthrough,
    Jump,
    BranchTrue,
    BranchFalse,
    LoopBody,
    LoopExit,
    Return,
    TailCall,
}

impl EdgeKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Fallthrough => "fallthrough",
            Self::Jump => "jump",
            Self::BranchTrue => "branch-true",
            Self::BranchFalse => "branch-false",
            Self::LoopBody => "loop-body",
            Self::LoopExit => "loop-exit",
            Self::Return => "return",
            Self::TailCall => "tail-call",
        }
    }
}

/// 基本块覆盖的 Low-IR 指令半开区间。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InstrRange {
    pub start: InstrRef,
    pub len: usize,
}

impl Default for InstrRange {
    fn default() -> Self {
        Self {
            start: InstrRef(0),
            len: 0,
        }
    }
}

impl InstrRange {
    pub const fn new(start: InstrRef, len: usize) -> Self {
        Self { start, len }
    }

    pub const fn is_empty(self) -> bool {
        self.len == 0
    }

    pub const fn end(self) -> usize {
        self.start.0 + self.len
    }

    pub fn last(self) -> Option<InstrRef> {
        self.len.checked_sub(1).map(|off| InstrRef(self.start.0 + off))
    }

    pub fn iter(self) -> impl DoubleEndedIterator<Item = InstrRef> {
        (self.start.0..self.end()).map(InstrRef)
    }
}

/// 单个基本块。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BasicBlock {
    pub id: BlockId,
    pub kind: BlockKind,
    pub instrs: InstrRange,
}

/// 单条有向边。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Edge {
    pub id: EdgeId,
    pub from: BlockId,
    pub to: BlockId,
    pub kind: EdgeKind,
}

/// 显式 VM 循环协议提示。
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LoopProtocolHint {
    NumericFor {
        init_block: BlockId,
        init_instr: InstrRef,
        body_entry: BlockId,
        exit_block: BlockId,
        latch_blocks: Vec<BlockId>,
        index: Reg,
        limit: Reg,
        step: Reg,
        binding: Reg,
    },
    GenericFor {
        prep_block: Option<BlockId>,
        header_block: BlockId,
        call_instr: InstrRef,
        loop_instr: InstrRef,
        body_entry: BlockId,
        exit_block: BlockId,
        iterator: Reg,
        state: Reg,
        control: Reg,
        bindings: RegRange,
    },
}

/// 纯布尔字面量加载块（用于识别 PUC/LuaJIT `CMP/TEST + LOADBOOL false/true` 布尔物化）。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BoolLoadBlock {
    pub block: BlockId,
    pub instr: InstrRef,
    pub dst: Reg,
    pub value: bool,
    pub next: BlockId,
}

/// 单个 proto 的控制流图。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Cfg {
    pub blocks: Vec<BasicBlock>,
    pub edges: Vec<Edge>,
    pub preds: Vec<Vec<EdgeId>>,
    pub succs: Vec<Vec<EdgeId>>,
    pub entry_block: BlockId,
    pub exit_block: BlockId,
    /// 可达基本块的逆后序（RPO，不含孤立不可达块；若 exit_block 可达则位于末尾）。
    pub block_order: Vec<BlockId>,
    pub reachable: Vec<bool>,
    pub block_of_instr: Vec<Option<BlockId>>,
    pub loop_protocols: Vec<LoopProtocolHint>,
    pub bool_load_blocks: BTreeMap<BlockId, BoolLoadBlock>,
}

/// 匹配 proto 嵌套树的 CFG 树（供 WASM/Web 视图直接投影）。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CfgGraph {
    pub cfg: Cfg,
    pub children: Vec<CfgGraph>,
}

impl Cfg {
    pub fn is_reachable(&self, block: BlockId) -> bool {
        self.reachable.get(block.index()).copied().unwrap_or(false)
    }

    pub fn succ_blocks(&self, block: BlockId) -> impl Iterator<Item = BlockId> + '_ {
        self.succs[block.index()]
            .iter()
            .map(|&e| self.edges[e.index()].to)
    }

    pub fn pred_blocks(&self, block: BlockId) -> impl Iterator<Item = BlockId> + '_ {
        self.preds[block.index()]
            .iter()
            .map(|&e| self.edges[e.index()].from)
    }

    pub fn reachable_preds(&self, block: BlockId) -> impl Iterator<Item = Edge> + '_ {
        self.preds[block.index()]
            .iter()
            .map(|&e| self.edges[e.index()])
            .filter(|edge| self.is_reachable(edge.from))
    }

    pub fn branch_edges(&self, block: BlockId) -> Option<(EdgeId, EdgeId)> {
        let mut true_edge = None;
        let mut false_edge = None;
        for &edge_id in &self.succs[block.index()] {
            match self.edges[edge_id.index()].kind {
                EdgeKind::BranchTrue => true_edge = Some(edge_id),
                EdgeKind::BranchFalse => false_edge = Some(edge_id),
                _ => {}
            }
        }
        Some((true_edge?, false_edge?))
    }

    pub fn terminator<'a>(&self, proto: &'a LoweredProto, block: BlockId) -> Option<&'a LowInstr> {
        let last = self.blocks[block.index()].instrs.last()?;
        proto.instrs.get(last.index())
    }

    pub fn is_empty_jump_block(&self, proto: &LoweredProto, block: BlockId) -> Option<BlockId> {
        if block == self.entry_block || block == self.exit_block {
            return None;
        }
        let info = &self.blocks[block.index()];
        if info.instrs.len != 1 {
            return None;
        }
        if !matches!(proto.instrs.get(info.instrs.start.index()), Some(LowInstr::Jump(_))) {
            return None;
        }
        let [edge_id] = self.succs[block.index()].as_slice() else {
            return None;
        };
        let target = self.edges[edge_id.index()].to;
        (target != block).then_some(target)
    }
}

/// 构建并规范化单个 proto 的 CFG。
pub(crate) fn build_cfg(proto_id: usize, proto: &LoweredProto) -> Result<Cfg, AnalysisError> {
    let instr_count = proto.instrs.len();
    let mut leaders = BTreeSet::new();
    if instr_count > 0 {
        leaders.insert(0usize);
    }

    let validate_target = |instr_idx: usize, target: InstrRef| -> Result<usize, AnalysisError> {
        if target.index() < instr_count {
            Ok(target.index())
        } else {
            Err(AnalysisError::InvalidJumpTarget {
                proto: proto_id,
                instr: instr_idx,
                target: target.index(),
            })
        }
    };

    for (idx, instr) in proto.instrs.iter().enumerate() {
        match instr {
            LowInstr::Jump(j) => {
                leaders.insert(validate_target(idx, j.target)?);
                if idx + 1 < instr_count {
                    leaders.insert(idx + 1);
                }
            }
            LowInstr::Branch(b) => {
                leaders.insert(validate_target(idx, b.then_target)?);
                leaders.insert(validate_target(idx, b.else_target)?);
                if idx + 1 < instr_count {
                    leaders.insert(idx + 1);
                }
            }
            LowInstr::NumericForInit(f) => {
                leaders.insert(validate_target(idx, f.body_target)?);
                leaders.insert(validate_target(idx, f.exit_target)?);
                if idx + 1 < instr_count {
                    leaders.insert(idx + 1);
                }
            }
            LowInstr::NumericForLoop(f) => {
                leaders.insert(validate_target(idx, f.body_target)?);
                leaders.insert(validate_target(idx, f.exit_target)?);
                if idx + 1 < instr_count {
                    leaders.insert(idx + 1);
                }
            }
            LowInstr::GenericForLoop(f) => {
                leaders.insert(validate_target(idx, f.body_target)?);
                leaders.insert(validate_target(idx, f.exit_target)?);
                if idx + 1 < instr_count {
                    leaders.insert(idx + 1);
                }
            }
            LowInstr::Return(_) | LowInstr::TailCall(_) if idx + 1 < instr_count => {
                leaders.insert(idx + 1);
            }
            _ => {}
        }
    }

    let leader_list: Vec<usize> = leaders.into_iter().collect();
    let mut blocks = Vec::with_capacity(leader_list.len() + 2);
    let mut block_of_instr = vec![None; instr_count];
    let mut block_by_start = BTreeMap::new();

    if leader_list.is_empty() {
        blocks.push(BasicBlock {
            id: BlockId(0),
            kind: BlockKind::Entry,
            instrs: InstrRange::new(InstrRef(0), 0),
        });
    } else {
        for (bi, &start) in leader_list.iter().enumerate() {
            let end = leader_list.get(bi + 1).copied().unwrap_or(instr_count);
            let id = BlockId(bi);
            let kind = if bi == 0 {
                BlockKind::Entry
            } else {
                BlockKind::Normal
            };
            blocks.push(BasicBlock {
                id,
                kind,
                instrs: InstrRange::new(InstrRef(start), end - start),
            });
            block_by_start.insert(start, id);
            for slot in &mut block_of_instr[start..end] {
                *slot = Some(id);
            }
        }
    }

    let exit_block = BlockId(blocks.len());
    blocks.push(BasicBlock {
        id: exit_block,
        kind: BlockKind::Exit,
        instrs: InstrRange::new(InstrRef(instr_count), 0),
    });

    let entry_block = BlockId(0);
    let mut edges = Vec::new();
    let mut add_edge = |from: BlockId, to: BlockId, kind: EdgeKind| {
        let id = EdgeId(edges.len());
        edges.push(Edge { id, from, to, kind });
    };

    if leader_list.is_empty() {
        add_edge(entry_block, exit_block, EdgeKind::Fallthrough);
    } else {
        for (bi, block) in blocks.iter().enumerate().take(leader_list.len()) {
            let block_id = BlockId(bi);
            let range = block.instrs;
            let Some(last) = range.last() else {
                add_edge(block_id, exit_block, EdgeKind::Fallthrough);
                continue;
            };
            match &proto.instrs[last.index()] {
                LowInstr::Jump(j) => {
                    let target = block_by_start[&j.target.index()];
                    add_edge(block_id, target, EdgeKind::Jump);
                }
                LowInstr::Branch(b) => {
                    let then_b = block_by_start[&b.then_target.index()];
                    let else_b = block_by_start[&b.else_target.index()];
                    add_edge(block_id, then_b, EdgeKind::BranchTrue);
                    add_edge(block_id, else_b, EdgeKind::BranchFalse);
                }
                LowInstr::NumericForInit(f) => {
                    let body_b = block_by_start[&f.body_target.index()];
                    let exit_b = block_by_start[&f.exit_target.index()];
                    add_edge(block_id, body_b, EdgeKind::LoopBody);
                    add_edge(block_id, exit_b, EdgeKind::LoopExit);
                }
                LowInstr::NumericForLoop(f) => {
                    let body_b = block_by_start[&f.body_target.index()];
                    let exit_b = block_by_start[&f.exit_target.index()];
                    add_edge(block_id, body_b, EdgeKind::LoopBody);
                    add_edge(block_id, exit_b, EdgeKind::LoopExit);
                }
                LowInstr::GenericForLoop(f) => {
                    let body_b = block_by_start[&f.body_target.index()];
                    let exit_b = block_by_start[&f.exit_target.index()];
                    add_edge(block_id, body_b, EdgeKind::LoopBody);
                    add_edge(block_id, exit_b, EdgeKind::LoopExit);
                }
                LowInstr::Return(_) => {
                    add_edge(block_id, exit_block, EdgeKind::Return);
                }
                LowInstr::TailCall(_) => {
                    add_edge(block_id, exit_block, EdgeKind::TailCall);
                }
                _ => {
                    let next = block_by_start
                        .get(&range.end())
                        .copied()
                        .unwrap_or(exit_block);
                    add_edge(block_id, next, EdgeKind::Fallthrough);
                }
            }
        }
    }

    let mut cfg = Cfg {
        preds: vec![Vec::new(); blocks.len()],
        succs: vec![Vec::new(); blocks.len()],
        blocks,
        edges,
        entry_block,
        exit_block,
        block_order: Vec::new(),
        reachable: Vec::new(),
        block_of_instr,
        loop_protocols: Vec::new(),
        bool_load_blocks: BTreeMap::new(),
    };
    rebuild_indices_and_rpo(&mut cfg);
    collapse_empty_jump_trampolines(&mut cfg, proto);
    detect_loop_protocols(&mut cfg, proto);
    detect_bool_load_blocks(&mut cfg, proto);
    Ok(cfg)
}

fn rebuild_indices_and_rpo(cfg: &mut Cfg) {
    let n = cfg.blocks.len();
    cfg.preds = vec![Vec::new(); n];
    cfg.succs = vec![Vec::new(); n];
    for edge in &cfg.edges {
        cfg.succs[edge.from.index()].push(edge.id);
        cfg.preds[edge.to.index()].push(edge.id);
    }

    let dfs = super::graph::depth_first(
        n,
        cfg.entry_block,
        BlockId::index,
        |_| true,
        |b| {
            cfg.succs[b.index()]
                .iter()
                .map(|&e| cfg.edges[e.index()].to)
                .collect::<Vec<_>>()
        },
    );

    cfg.reachable = vec![false; n];
    for &b in &dfs.postorder {
        cfg.reachable[b.index()] = true;
    }

    let mut rpo = dfs.postorder;
    rpo.reverse();
    // 保证虚拟 exit_block 始终排在 block_order 末尾，方便结构化与展示。
    if let Some(pos) = rpo.iter().position(|&b| b == cfg.exit_block) {
        rpo.remove(pos);
        rpo.push(cfg.exit_block);
    }
    cfg.block_order = rpo;
}

/// 折叠纯 `Jump` 跳板块，消除编译器多级跳转噪声。
/// 保留自环块（`while true do end`）与入口块。
fn collapse_empty_jump_trampolines(cfg: &mut Cfg, proto: &LoweredProto) {
    let n = cfg.blocks.len();
    let mut direct_target = vec![None; n];
    for (bi, slot) in direct_target.iter_mut().enumerate() {
        let block = BlockId(bi);
        if cfg.is_reachable(block) {
            *slot = cfg.is_empty_jump_block(proto, block);
        }
    }

    let resolve = |start: BlockId| -> BlockId {
        let mut current = start;
        let mut visited = BTreeSet::new();
        visited.insert(current);
        while let Some(next) = direct_target[current.index()] {
            if !visited.insert(next) {
                break;
            }
            current = next;
        }
        current
    };

    let mut changed = false;
    for edge in &mut cfg.edges {
        if !cfg.reachable[edge.from.index()] {
            continue;
        }
        let resolved = resolve(edge.to);
        if resolved != edge.to {
            edge.to = resolved;
            changed = true;
        }
    }

    if changed {
        rebuild_indices_and_rpo(cfg);
    }
}

fn detect_loop_protocols(cfg: &mut Cfg, proto: &LoweredProto) {
    // 按 `(body_entry, index, limit, step, binding)` 建索引，消除大量顺序 numeric-for 的 O(L²) 配对。
    let mut numeric_loops_by_key: BTreeMap<
        (BlockId, Reg, Reg, Reg, Reg),
        Vec<BlockId>,
    > = BTreeMap::new();
    for &block in &cfg.block_order {
        if let Some(LowInstr::NumericForLoop(loop_instr)) = cfg.terminator(proto, block)
            && let Some(body_entry) = cfg
                .block_of_instr
                .get(loop_instr.body_target.index())
                .copied()
                .flatten()
        {
            numeric_loops_by_key
                .entry((
                    body_entry,
                    loop_instr.index,
                    loop_instr.limit,
                    loop_instr.step,
                    loop_instr.binding,
                ))
                .or_default()
                .push(block);
        }
    }

    for &block in &cfg.block_order {
        let Some(last_ref) = cfg.blocks[block.index()].instrs.last() else {
            continue;
        };
        match &proto.instrs[last_ref.index()] {
            LowInstr::NumericForInit(init) => {
                let mut body_entry = None;
                let mut exit_block = None;
                for &eid in &cfg.succs[block.index()] {
                    let edge = cfg.edges[eid.index()];
                    match edge.kind {
                        EdgeKind::LoopBody => body_entry = Some(edge.to),
                        EdgeKind::LoopExit => exit_block = Some(edge.to),
                        _ => {}
                    }
                }
                if let (Some(body_entry), Some(exit_block)) = (body_entry, exit_block) {
                    let latch_blocks = numeric_loops_by_key
                        .get(&(body_entry, init.index, init.limit, init.step, init.binding))
                        .cloned()
                        .unwrap_or_default();
                    cfg.loop_protocols.push(LoopProtocolHint::NumericFor {
                        init_block: block,
                        init_instr: last_ref,
                        body_entry,
                        exit_block,
                        latch_blocks,
                        index: init.index,
                        limit: init.limit,
                        step: init.step,
                        binding: init.binding,
                    });
                }
            }
            LowInstr::GenericForLoop(gloop) => {
                let range = cfg.blocks[block.index()].instrs;
                let call_pair = range
                    .iter()
                    .rev()
                    .skip(1)
                    .find_map(|iref| match &proto.instrs[iref.index()] {
                        LowInstr::GenericForCall(call) => Some((iref, *call)),
                        _ => None,
                    });
                let Some((call_instr, call)) = call_pair else {
                    continue;
                };
                let mut body_entry = None;
                let mut exit_block = None;
                for &eid in &cfg.succs[block.index()] {
                    let edge = cfg.edges[eid.index()];
                    match edge.kind {
                        EdgeKind::LoopBody => body_entry = Some(edge.to),
                        EdgeKind::LoopExit => exit_block = Some(edge.to),
                        _ => {}
                    }
                }
                let Some((body_entry, exit_block)) = body_entry.zip(exit_block) else {
                    continue;
                };
                // 查找前驱中的 GenericForPrep（Lua 5.4/5.5/LuaJIT 常见）
                let prep_block = cfg.reachable_preds(block).find_map(|edge| {
                    let prange = cfg.blocks[edge.from.index()].instrs;
                    prange
                        .iter()
                        .any(|ir| matches!(proto.instrs[ir.index()], LowInstr::GenericForPrep(_)))
                        .then_some(edge.from)
                });
                cfg.loop_protocols.push(LoopProtocolHint::GenericFor {
                    prep_block,
                    header_block: block,
                    call_instr,
                    loop_instr: last_ref,
                    body_entry,
                    exit_block,
                    iterator: call.iterator,
                    state: call.state,
                    control: gloop.control_target,
                    bindings: gloop.bindings,
                });
            }
            _ => {}
        }
    }
}

fn detect_bool_load_blocks(cfg: &mut Cfg, proto: &LoweredProto) {
    for &block in &cfg.block_order {
        if block == cfg.entry_block || block == cfg.exit_block {
            continue;
        }
        let range = cfg.blocks[block.index()].instrs;
        let [edge_id] = cfg.succs[block.index()].as_slice() else {
            continue;
        };
        let next = cfg.edges[edge_id.index()].to;
        if next == block {
            continue;
        }
        let instrs: Vec<InstrRef> = range.iter().collect();
        let matched = match instrs.as_slice() {
            [first] => match &proto.instrs[first.index()] {
                LowInstr::LoadBool(lb) => Some((*first, lb.dst, lb.value)),
                _ => None,
            },
            [first, second] => match (&proto.instrs[first.index()], &proto.instrs[second.index()])
            {
                (LowInstr::LoadBool(lb), LowInstr::Jump(_)) => Some((*first, lb.dst, lb.value)),
                _ => None,
            },
            _ => None,
        };
        if let Some((instr, dst, value)) = matched {
            cfg.bool_load_blocks.insert(
                block,
                BoolLoadBlock {
                    block,
                    instr,
                    dst,
                    value,
                    next,
                },
            );
        }
    }
}
