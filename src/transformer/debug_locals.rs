//! 归一化 debug local 的槽位身份，并冻结按寄存器查询活动 source scope 的边界。
//!
//! 原始调试表的顺序决定 PUC Lua/LuaJIT 活动局部的寄存器 rank；Luau 显式槽位不重推。
//! scope 身份始终是归一化表下标，重叠项仍返回表中第一个 source scope，不改成最近声明。
//! 例如同一寄存器的 scope#0=[2,8)、scope#1=[4,10)，查询 6 返回 #0，查询 8 返回 #1。
//! 下游只读该集合；名字解码、SSA 归属和最终源码命名不属于这里。

use std::{
    collections::{BTreeMap, BTreeSet},
    ops::Deref,
};

use crate::parser::{RawLocalVar, RawProto};

use super::common::{DebugLocalFact, DebugLocalKind, Reg};

/// 原顺序 debug 事实与同一快照的活动查询索引；只读 slice 访问不会使索引失效。
#[derive(Debug, Clone, PartialEq, Default)]
pub struct DebugLocals {
    entries: Vec<DebugLocalFact>,
    source_boundaries: BTreeMap<Reg, Vec<(u32, Option<usize>)>>,
}

impl Deref for DebugLocals {
    type Target = [DebugLocalFact];

    fn deref(&self) -> &Self::Target {
        &self.entries
    }
}

impl DebugLocals {
    /// 是否存在该寄存器的非空 source scope；不重扫原调试表。
    pub(crate) fn has_source_scope(&self, reg: Reg) -> bool {
        self.source_boundaries.contains_key(&reg)
    }

    /// 返回该位置首个活动 source scope，保留原始半开区间与表顺序优先级。
    pub fn source_at(&self, reg: Reg, pc: u32) -> Option<(usize, &DebugLocalFact)> {
        let boundaries = self.source_boundaries.get(&reg)?;
        let end = boundaries.partition_point(|&(start, _)| start <= pc);
        let scope = boundaries.get(end.checked_sub(1)?)?.1?;
        Some((scope, &self.entries[scope]))
    }

    /// 一条 low 指令映射的任一 PC 是否处于 source scope；无 PC 时不证明不可见。
    pub(crate) fn source_visible_at(&self, reg: Reg, pcs: &[u32]) -> bool {
        if pcs.is_empty() {
            self.has_source_scope(reg)
        } else {
            pcs.iter().any(|pc| self.source_at(reg, *pc).is_some())
        }
    }

    fn new(entries: Vec<DebugLocalFact>) -> Self {
        let mut events_by_reg = BTreeMap::<Reg, Vec<(u32, bool, usize)>>::new();
        for (scope, local) in entries.iter().enumerate() {
            if local.is_source() && local.start_pc < local.end_pc {
                let events = events_by_reg.entry(local.reg).or_default();
                events.push((local.start_pc, true, scope));
                events.push((local.end_pc, false, scope));
            }
        }
        let source_boundaries = events_by_reg
            .into_iter()
            .map(|(reg, mut events)| {
                events.sort_unstable();
                let mut active = BTreeSet::new();
                let mut boundaries = Vec::new();
                let mut previous = None;
                let mut cursor = 0;
                while cursor < events.len() {
                    let pc = events[cursor].0;
                    while cursor < events.len() && events[cursor].0 == pc {
                        let (_, entering, scope) = events[cursor];
                        if entering {
                            active.insert(scope);
                        } else {
                            active.remove(&scope);
                        }
                        cursor += 1;
                    }
                    let current = active.first().copied();
                    if current != previous {
                        boundaries.push((pc, current));
                        previous = current;
                    }
                }
                (reg, boundaries)
            })
            .collect();
        Self {
            entries,
            source_boundaries,
        }
    }
}

/// 非 Luau 格式的第 N 个活动局部对应寄存器 N，同起点仍按原表顺序排槽。
/// 无有效区间且没有显式槽位的项保持丢弃；显式 Luau 表的长度不符时沿用推导规则。
pub(crate) fn normalize_debug_locals(raw: &RawProto) -> DebugLocals {
    let locals = &raw.common.debug_info.common.local_vars;
    let explicit_regs = raw
        .common
        .debug_info
        .extra
        .luau()
        .map(|extra| extra.local_regs.as_slice())
        .filter(|regs| regs.len() == locals.len());
    let registers = explicit_regs.map_or_else(
        || inferred_registers(locals),
        |regs| regs.iter().map(|&reg| Some(usize::from(reg))).collect(),
    );
    let entries = locals
        .iter()
        .zip(registers)
        .filter_map(|(local, reg)| {
            let reg = Reg(reg?);
            let kind = if local.name.bytes.starts_with(b"(for ") && local.name.bytes.ends_with(b")")
            {
                DebugLocalKind::CompilerInternal
            } else {
                DebugLocalKind::Source
            };
            Some(DebugLocalFact {
                name: local.name.clone(),
                reg,
                start_pc: local.start_pc,
                end_pc: local.end_pc,
                kind,
            })
        })
        .collect();
    DebugLocals::new(entries)
}

fn inferred_registers(locals: &[RawLocalVar]) -> Vec<Option<usize>> {
    let mut events = Vec::with_capacity(locals.len() * 2);
    for (index, local) in locals.iter().enumerate() {
        if local.start_pc < local.end_pc {
            events.push((local.start_pc, true, index));
            events.push((local.end_pc, false, index));
        }
    }
    // 离域事件先于同 PC 入口；入口按原表下标处理，rank 只数此前仍活动的表项。
    events.sort_unstable();
    let mut active = ActiveLocalRanks(vec![0; locals.len() + 1]);
    let mut registers = vec![None; locals.len()];
    for (_, entering, index) in events {
        if entering {
            registers[index] = Some(active.before(index));
        }
        active.set(index, entering);
    }
    registers
}

/// 原表索引上的活动计数 Fenwick tree；每次声明/离域和前缀 rank 查询均为 O(log N)。
struct ActiveLocalRanks(Vec<usize>);

impl ActiveLocalRanks {
    fn set(&mut self, index: usize, active: bool) {
        let mut cursor = index + 1;
        while cursor < self.0.len() {
            if active {
                self.0[cursor] += 1;
            } else {
                self.0[cursor] -= 1;
            }
            cursor += cursor & cursor.wrapping_neg();
        }
    }

    fn before(&self, index: usize) -> usize {
        let mut cursor = index;
        let mut count = 0;
        while cursor != 0 {
            count += self.0[cursor];
            cursor -= cursor & cursor.wrapping_neg();
        }
        count
    }
}
