//! 将源码调试 local 生命周期映射到 canonical SSA；依赖 lowering map 与数据流，不负责 HIR 命名；例如在初始化指令后找到唯一 local 候选。

use super::*;

/// 将源码 local 的生命周期入口锚定到 canonical SSA。
///
/// debug 的 `start_pc` 通常位于初始化完成之后；若改用 producer 位置查询，table/closure
/// 这类多指令初始化会错过名称。多个源码 scope 若落到同一 SSA，说明 debug 布局无法
/// 唯一裁决身份，此处保留冲突证据但不向 HIR 发布候选。
pub(super) fn analyze_debug_bindings(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
) -> DebugBindingFacts {
    let mut by_value = BTreeMap::<super::super::SsaValue, Vec<usize>>::new();
    for (scope, local) in proto
        .debug_locals
        .iter()
        .enumerate()
        .filter(|(_, local)| local.is_source())
    {
        let Some(instr) = proto.lowering_map.low_instr_at_or_after_pc(local.start_pc) else {
            continue;
        };
        let value =
            ssa_value_at_debug_scope_entry(proto, cfg, dataflow, instr, local.reg, local.start_pc);
        by_value.entry(value).or_default().push(scope);
    }

    let mut facts = DebugBindingFacts::default();
    for (value, scopes) in by_value {
        if let [scope] = scopes.as_slice() {
            let local = &proto.debug_locals[*scope];
            facts.accepted.push(DebugBindingFact {
                scope: *scope,
                reg: local.reg,
                start_pc: local.start_pc,
                end_pc: local.end_pc,
                end_instr: proto.lowering_map.low_instr_at_or_after_pc(local.end_pc),
                value,
            });
        } else {
            facts.conflicts.push(DebugBindingConflict { value, scopes });
        }
    }
    facts
}

pub(super) fn ssa_value_at_debug_scope_entry(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    instr: InstrRef,
    reg: crate::transformer::Reg,
    start_pc: u32,
) -> super::super::SsaValue {
    let block = cfg.instr_to_block[instr.index()];
    let start = cfg.blocks[block.index()].instrs.start.index();
    let mut value = dataflow
        .last_fixed_def_in_range(reg, start..instr.index())
        .map_or_else(
            || dataflow.block_entry_value(block, reg),
            super::super::SsaValue::Def,
        );
    // Luau 等格式可把 local.start_pc 直接指向初始化指令；这时作用域入口看到的是
    // 该指令完成后的值。PUC Lua 常把 start_pc 放在初始化之后，或像 SETLIST 一样
    // 指向不重定义 binding 的最后一步，两种情况都继续使用上面的 reaching value。
    if proto
        .lowering_map
        .pc_map()
        .get(instr.index())
        .is_some_and(|pcs| pcs.contains(&start_pc))
        && let Some(def) = dataflow.instr_def_for_reg(instr, reg)
    {
        value = super::super::SsaValue::Def(def);
    }
    value
}
