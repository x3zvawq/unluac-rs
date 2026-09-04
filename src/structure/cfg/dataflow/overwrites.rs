//! 保存固定定义写入前的物理值身份，独立于 pruned SSA 的表达式 use graph。
//!
//! SSA 入口快照是已有 canonical 身份的边界；缺失的 dead-in 槽按 `(block, reg)`
//! 建共享查询图，所有路径一致才发布旧值，不为物理覆盖增加表达式 phi/use。
//! 例如循环后穿过几个不读状态的分支再 `state = nil`，仍能关联原 carried phi；
//! 不同旧值合流或 open result 覆盖则未知。这里只证明覆盖关系，不分配 HIR local。
//!
//! 指令按块扫描一次，查询节点最多从未到达到已知、再到未知，各边最多传播两次；
//! 多个定义共用入口查询，不按定义反复回扫指令前缀或整个 CFG。

use std::collections::{BTreeMap, VecDeque};

use super::super::common::SsaRegMap;
use super::{BlockRef, Cfg, Def, DefId, InstrEffect, InstrRef, Reg, SsaValue};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Value {
    Known(SsaValue),
    Unknown,
}

impl Value {
    fn known(self) -> Option<SsaValue> {
        match self {
            Self::Known(value) => Some(value),
            Self::Unknown => None,
        }
    }
}

#[derive(Default)]
struct BlockWrites {
    fixed: BTreeMap<Reg, (InstrRef, DefId)>,
    // 起点与 PC 都递增；新 open 写会淘汰所有不小于其起点的旧边界。
    open: BTreeMap<Reg, InstrRef>,
}

impl BlockWrites {
    fn last_value(&self, reg: Reg) -> Option<Value> {
        let fixed = self.fixed.get(&reg);
        if let Some((_, open)) = self.open.range(..=reg).next_back()
            && fixed.is_none_or(|(instr, _)| open >= instr)
        {
            return Some(Value::Unknown);
        }
        fixed.map(|(_, def)| Value::Known(SsaValue::Def(*def)))
    }
}

#[derive(Default)]
struct EntryQueries {
    ids: BTreeMap<(BlockRef, Reg), usize>,
    keys: Vec<(BlockRef, Reg)>,
    values: Vec<Option<Value>>,
    users: Vec<Vec<usize>>,
}

impl EntryQueries {
    fn entry(&mut self, block: BlockRef, reg: Reg) -> usize {
        *self.ids.entry((block, reg)).or_insert_with(|| {
            let id = self.keys.len();
            self.keys.push((block, reg));
            self.values.push(None);
            self.users.push(Vec::new());
            id
        })
    }

    fn join(&mut self, id: usize, incoming: Value) -> bool {
        let value = &mut self.values[id];
        let next = match *value {
            None => incoming,
            Some(current) if current == incoming => return false,
            Some(Value::Unknown) => return false,
            Some(_) => Value::Unknown,
        };
        *value = Some(next);
        true
    }

    fn solve(&mut self, cfg: &Cfg, entries: &[SsaRegMap], writes: &[BlockWrites]) {
        let mut id = 0;
        while id < self.keys.len() {
            let (block, reg) = self.keys[id];
            if let Some(value) = entries[block.index()].get(reg) {
                self.join(id, Value::Known(value));
            } else {
                if block == cfg.entry_block {
                    self.join(id, Value::Known(SsaValue::Entry(reg)));
                }
                for pred in cfg.reachable_predecessors(block) {
                    if let Some(value) = writes[pred.index()].last_value(reg) {
                        self.join(id, value);
                    } else {
                        let source = self.entry(pred, reg);
                        self.users[source].push(id);
                    }
                }
            }
            id += 1;
        }
        let mut pending = self
            .values
            .iter()
            .enumerate()
            .filter_map(|(id, value)| value.is_some().then_some(id))
            .collect::<VecDeque<_>>();
        while let Some(source) = pending.pop_front() {
            let Some(value) = self.values[source] else {
                continue;
            };
            for index in 0..self.users[source].len() {
                let user = self.users[source][index];
                if self.join(user, value) {
                    pending.push_back(user);
                }
            }
        }
    }
}

pub(super) fn analyze_overwritten_values(
    cfg: &Cfg,
    effects: &[InstrEffect],
    defs: &[Def],
    instr_defs: &[Vec<DefId>],
    entries: &[SsaRegMap],
) -> Vec<Option<SsaValue>> {
    let mut overwritten = vec![None; defs.len()];
    let mut writes = (0..cfg.blocks.len())
        .map(|_| BlockWrites::default())
        .collect::<Vec<_>>();
    let mut queries = EntryQueries::default();
    let mut pending_defs = Vec::new();
    for &block in &cfg.block_order {
        let current = &mut writes[block.index()];
        let range = cfg.blocks[block.index()].instrs;
        for index in range.start.index()..range.end() {
            for &def in &instr_defs[index] {
                let reg = defs[def.index()].reg;
                match current.last_value(reg) {
                    Some(value) => overwritten[def.index()] = value.known(),
                    None => pending_defs.push((def, queries.entry(block, reg))),
                }
                current.fixed.insert(reg, (InstrRef(index), def));
            }
            if let Some(start) = effects[index].open_must_def {
                current.open.split_off(&start);
                current.open.insert(start, InstrRef(index));
            }
        }
    }
    queries.solve(cfg, entries, &writes);
    for (def, query) in pending_defs {
        overwritten[def.index()] = queries.values[query].and_then(Value::known);
    }
    overwritten
}
