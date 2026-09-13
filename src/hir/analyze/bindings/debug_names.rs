//! 查询指令、块入口和区域内寄存器的 debug local 名称；借用 debug scope 并查询 Structure 的 SSA 身份，不负责分配 LocalId；例如为唯一活跃 scope 提供命名 hint。

//! 名称仅在最终写入 HIR 提示时解码；屏障与存在性查询不构造 String。

use super::*;

pub(super) fn target_for_slot(
    reg: Reg,
    instr_index: usize,
    epochs: &SlotEpochFacts,
    captured_slots: &CapturedSlotTargets,
) -> Option<LocalId> {
    captured_slots.target_at(reg, InstrRef(instr_index), epochs)
}

pub(super) fn debug_local_name_for_reg_at_instr(
    proto: &LoweredProto,
    reg: Reg,
    instr: InstrRef,
) -> Option<String> {
    debug_local_hint_for_reg_at_instr(proto, reg, instr).map(|hint| decode_raw_string(hint.name))
}

pub(super) fn debug_local_hint_for_reg_at_instr(
    proto: &LoweredProto,
    reg: Reg,
    instr: InstrRef,
) -> Option<DebugBindingHint<'_>> {
    let pc = proto
        .lowering_map
        .pc_map()
        .get(instr.index())?
        .first()
        .copied()?;
    debug_local_hint_for_reg_at_pc(proto, reg, pc)
}

pub(super) fn debug_local_name_for_reg_at_block_entry(
    proto: &LoweredProto,
    cfg: &Cfg,
    block: crate::structure::BlockRef,
    reg: Reg,
) -> Option<String> {
    debug_local_hint_for_reg_at_block_entry(proto, cfg, block, reg)
        .map(|hint| decode_raw_string(hint.name))
}

pub(super) fn debug_local_hint_for_reg_at_block_entry<'a>(
    proto: &'a LoweredProto,
    cfg: &Cfg,
    block: crate::structure::BlockRef,
    reg: Reg,
) -> Option<DebugBindingHint<'a>> {
    let instrs = cfg.blocks[block.index()].instrs;
    if instrs.is_empty() {
        return None;
    }
    let instr = instrs.start;
    debug_local_hint_for_reg_at_instr(proto, reg, instr)
}

pub(super) fn debug_local_name_for_reg_in_blocks(
    proto: &LoweredProto,
    cfg: &Cfg,
    blocks: &[BlockRef],
    reg: Reg,
) -> Option<String> {
    blocks
        .iter()
        .copied()
        .filter_map(|block| {
            let instr = cfg.blocks[block.index()].instrs.start;
            let pc = proto
                .lowering_map
                .pc_map()
                .get(instr.index())?
                .first()
                .copied()?;
            Some((pc, block))
        })
        .min_by_key(|(pc, block)| (*pc, *block))
        .and_then(|(_, block)| debug_local_name_for_reg_at_block_entry(proto, cfg, block, reg))
}

pub(super) fn debug_local_name_for_reg_at_pc(
    proto: &LoweredProto,
    reg: Reg,
    pc: u32,
) -> Option<String> {
    debug_local_hint_for_reg_at_pc(proto, reg, pc).map(|hint| decode_raw_string(hint.name))
}

pub(super) fn debug_local_hint_for_reg_at_pc(
    proto: &LoweredProto,
    reg: Reg,
    pc: u32,
) -> Option<DebugBindingHint<'_>> {
    proto
        .debug_locals
        .source_at(reg, pc)
        .map(|(scope, local)| DebugBindingHint {
            scope,
            name: &local.name,
        })
}

pub(super) fn debug_local_hint_for_ssa<'a>(
    proto: &'a LoweredProto,
    structure: &ReadyStructureFacts,
    value: SsaValue,
) -> Option<DebugBindingHint<'a>> {
    let fact = structure.debug_bindings().for_value(value)?;
    let local = proto.debug_locals.get(fact.scope)?;
    local.is_source().then_some(DebugBindingHint {
        scope: fact.scope,
        name: &local.name,
    })
}
