//! 在指定控制域内证明物理 home 的无观察覆盖前沿。
//!
//! 消费最终 ValueDecision owner 与 Dataflow，发布可共享的原 Def 覆盖事实。

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use super::{BlockRef, Cfg, DataflowFacts, DefId};
use crate::transformer::Reg;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct FrontierRef(usize);

#[derive(Debug, Clone, PartialEq, Eq)]
enum FrontierNode {
    Leaf(DefId),
    Join(Vec<FrontierRef>),
}

/// 同一作用域、同一 home 的共享前沿；查得证书不等于允许移动当前 HIR 求值。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RootOverwriteFrontiers {
    home: Reg,
    by_def: BTreeMap<DefId, FrontierRef>,
    nodes: Vec<FrontierNode>,
}

/// 借用冻结快照的前沿，避免把局部 arena 身份误用于另一作用域。
#[derive(Clone, Copy)]
pub struct RootOverwriteFrontier<'a> {
    facts: &'a RootOverwriteFrontiers,
    root: FrontierRef,
}

impl RootOverwriteFrontier<'_> {
    pub fn home(self) -> Reg {
        self.facts.home
    }

    /// 按需枚举精确覆盖 Def；共享尾只访问一次，不枚举控制路径。
    pub fn endpoints(self) -> impl Iterator<Item = DefId> {
        let mut pending = vec![self.root];
        let mut visited = BTreeSet::new();
        std::iter::from_fn(move || {
            while let Some(node) = pending.pop() {
                if !visited.insert(node) {
                    continue;
                }
                match &self.facts.nodes[node.0] {
                    FrontierNode::Leaf(def) => return Some(*def),
                    FrontierNode::Join(children) => pending.extend(children.iter().rev().copied()),
                }
            }
            None
        })
    }
}

impl RootOverwriteFrontiers {
    pub fn for_def(&self, def: DefId) -> Option<RootOverwriteFrontier<'_>> {
        self.by_def
            .get(&def)
            .map(|&root| RootOverwriteFrontier { facts: self, root })
    }

    pub(crate) fn build(
        data: &DataflowFacts,
        cfg: &Cfg,
        home: Reg,
        blocks: &[BlockRef],
        candidates: &[DefId],
    ) -> Self {
        let mut facts = Self {
            home,
            by_def: BTreeMap::new(),
            nodes: Vec::new(),
        };
        if candidates.is_empty() {
            return facts;
        }
        // 仅按调用方已选的域分配，不为每个 plan 分配整个 proto 的 block 表。
        let indices = blocks
            .iter()
            .enumerate()
            .map(|(i, &block)| (block, i))
            .collect::<BTreeMap<_, _>>();
        let mut users = vec![Vec::new(); blocks.len()];
        let mut waiting = vec![0usize; blocks.len()];
        let mut failed = vec![false; blocks.len()];
        let mut inputs = vec![Vec::new(); blocks.len()];
        let mut entries = vec![None; blocks.len()];
        let mut ready = VecDeque::new();
        let mut leaves = BTreeMap::new();
        for (index, &block) in blocks.iter().enumerate() {
            let range = cfg.blocks[block.index()].instrs;
            match range_end(data, home, range.start.index()..range.end()) {
                RangeEnd::Overwrite(def) => {
                    entries[index] = Some(facts.leaf(def, &mut leaves));
                    ready.push_back(index);
                }
                RangeEnd::Rejected => ready.push_back(index),
                RangeEnd::Forward => {
                    let successors = cfg.reachable_successors(block);
                    if successors.is_empty()
                        || successors.iter().any(|next| !indices.contains_key(next))
                    {
                        ready.push_back(index);
                        continue;
                    }
                    waiting[index] = successors.len();
                    for next in successors {
                        users[indices[&next]].push(index);
                    }
                }
            }
        }
        while let Some(child) = ready.pop_front() {
            for &parent in &users[child] {
                if let Some(frontier) = entries[child] {
                    inputs[parent].push(frontier);
                } else {
                    failed[parent] = true;
                }
                waiting[parent] -= 1;
                if waiting[parent] == 0 {
                    if !failed[parent] {
                        entries[parent] = facts.join(std::mem::take(&mut inputs[parent]));
                    }
                    ready.push_back(parent);
                }
            }
        }
        // 未退休的依赖含无覆盖循环。即使另一路有覆盖，也不能证明循环路径必定到达它。
        let mut exits = BTreeMap::new();
        for &def in candidates {
            let Some((block, actual_home, start)) = data.root_suffix_after_last_use(def, cfg)
            else {
                continue;
            };
            if actual_home != home || !indices.contains_key(&block) {
                continue;
            }
            let end = cfg.blocks[block.index()].instrs.end();
            let frontier = match range_end(data, home, start..end) {
                RangeEnd::Overwrite(overwrite) => Some(facts.leaf(overwrite, &mut leaves)),
                RangeEnd::Rejected => None,
                RangeEnd::Forward => *exits.entry(block).or_insert_with(|| {
                    let successors = cfg.reachable_successors(block);
                    let children = successors
                        .iter()
                        .map(|next| indices.get(next).and_then(|&index| entries[index]))
                        .collect::<Option<Vec<_>>>()?;
                    facts.join(children)
                }),
            };
            if let Some(frontier) = frontier {
                facts.by_def.insert(def, frontier);
            }
        }
        facts
    }

    fn leaf(&mut self, def: DefId, leaves: &mut BTreeMap<DefId, FrontierRef>) -> FrontierRef {
        *leaves.entry(def).or_insert_with(|| {
            let id = FrontierRef(self.nodes.len());
            self.nodes.push(FrontierNode::Leaf(def));
            id
        })
    }

    fn join(&mut self, mut children: Vec<FrontierRef>) -> Option<FrontierRef> {
        children.sort_unstable();
        children.dedup();
        match children.as_slice() {
            [] => None,
            [only] => Some(*only),
            _ => {
                let id = FrontierRef(self.nodes.len());
                self.nodes.push(FrontierNode::Join(children));
                Some(id)
            }
        }
    }
}

pub(super) enum RangeEnd {
    Overwrite(DefId),
    Forward,
    Rejected,
}

pub(super) fn range_end(
    data: &DataflowFacts,
    home: Reg,
    range: std::ops::Range<usize>,
) -> RangeEnd {
    if let Some(overwrite) = data.first_must_write_in_range(home, range.clone()) {
        if !data
            .root_intervals
            .has_observation(range.start..overwrite.index() + 1)
            && let Some(def) = data.instr_def_for_reg(overwrite, home)
        {
            return RangeEnd::Overwrite(def);
        }
        return RangeEnd::Rejected;
    }
    if data.root_intervals.has_observation(range) {
        RangeEnd::Rejected
    } else {
        RangeEnd::Forward
    }
}
