//! 查询指令、块入口和区域内寄存器的 debug local 名称；依赖 debug scope 与 SSA 名称索引，不负责分配 LocalId；例如为唯一活跃 scope 提供命名 hint。

use super::*;

pub(super) fn target_for_slot(
    reg: Reg,
    instr_index: usize,
    epochs: &SlotEpochFacts,
    captured_slots: &CapturedSlotTargets,
) -> Option<BoundSlotTarget> {
    captured_slots
        .slot_targets
        .get(&CapturedSlotKey::new(
            reg.index(),
            epochs.epoch_at(reg, InstrRef(instr_index)),
        ))
        .filter(|binding| instr_index >= binding.start_instr)
        .map(|binding| binding.target)
}

pub(super) fn debug_local_name_for_reg_at_instr(
    proto: &LoweredProto,
    reg: Reg,
    instr: InstrRef,
) -> Option<String> {
    debug_local_hint_for_reg_at_instr(proto, reg, instr).map(|hint| hint.name)
}

pub(super) fn debug_local_hint_for_reg_at_instr(
    proto: &LoweredProto,
    reg: Reg,
    instr: InstrRef,
) -> Option<DebugBindingHint> {
    let pc = proto
        .lowering_map
        .pc_map
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
    debug_local_hint_for_reg_at_block_entry(proto, cfg, block, reg).map(|hint| hint.name)
}

pub(super) fn debug_local_hint_for_reg_at_block_entry(
    proto: &LoweredProto,
    cfg: &Cfg,
    block: crate::structure::BlockRef,
    reg: Reg,
) -> Option<DebugBindingHint> {
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
                .pc_map
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
    debug_local_hint_for_reg_at_pc(proto, reg, pc).map(|hint| hint.name)
}

pub(super) fn debug_local_hint_for_reg_at_pc(
    proto: &LoweredProto,
    reg: Reg,
    pc: u32,
) -> Option<DebugBindingHint> {
    proto
        .debug_locals
        .iter()
        .enumerate()
        .find(|(_, local)| local.is_source() && local.reg == reg && local.is_active_at(pc))
        .map(|(scope, local)| DebugBindingHint {
            scope,
            name: decode_raw_string(&local.name),
        })
}

pub(super) fn debug_names_by_ssa(
    proto: &LoweredProto,
    structure: &StructureFacts,
) -> BTreeMap<SsaValue, DebugBindingHint> {
    structure
        .debug_bindings()
        .accepted
        .iter()
        .filter_map(|fact| {
            let local = proto.debug_locals.get(fact.scope)?;
            local.is_source().then_some((
                fact.value,
                DebugBindingHint {
                    scope: fact.scope,
                    name: decode_raw_string(&local.name),
                },
            ))
        })
        .collect()
}
