//! 这个文件专门负责把 Dataflow 的定义身份提升成 HIR 可直接消费的绑定表。
//!
//! HIR 第一版刻意不在主分析流程里散落 temp/phi/open-def 的编号规则，而是把这些
//! “身份分配”集中在这里统一完成。这样做有两个目的：
//! 1. 后续 `simplify` 若要把 `TempId` 提升成 `LocalId`，只需要围绕一处绑定入口演化；
//! 2. 保证表达式恢复和控制流恢复只消费稳定身份，不重复推导 Dataflow 细节。

use std::collections::{BTreeMap, BTreeSet};

use crate::cfg::{Cfg, DataflowFacts, OpenDef};
use crate::hir::common::{LocalId, ParamId, TempId, UpvalueId};
use crate::parser::RawLocalVar;
use crate::structure::{LoopKindHint, StructureFacts};
use crate::transformer::{InstrRef, LoweredProto, Reg};

use super::ProtoBindings;
use super::helpers::decode_raw_string;

pub(super) fn build_bindings(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    structure: &StructureFacts,
) -> ProtoBindings {
    let params = (0..usize::from(proto.signature.num_params))
        .map(ParamId)
        .collect::<Vec<_>>();
    let upvalues = (0..usize::from(proto.upvalues.common.count))
        .map(UpvalueId)
        .collect::<Vec<_>>();
    let mut locals = Vec::new();
    let mut local_debug_hints = Vec::new();
    let mut entry_local_regs = BTreeMap::new();
    let mut numeric_for_locals = BTreeMap::new();
    let mut generic_for_locals = BTreeMap::new();
    let mut block_local_regs = BTreeMap::new();

    if proto.signature.has_vararg_param_reg {
        let local = LocalId(locals.len());
        locals.push(local);
        local_debug_hints.push(debug_local_name_for_reg_at_pc(
            proto,
            crate::transformer::Reg(usize::from(proto.signature.num_params)),
            0,
        ));
        entry_local_regs.insert(
            crate::transformer::Reg(usize::from(proto.signature.num_params)),
            local,
        );
    }

    for candidate in structure
        .loop_candidates
        .iter()
        .filter(|candidate| candidate.kind_hint == LoopKindHint::NumericForLike)
    {
        let Some(reg) = numeric_for_binding_reg(proto, cfg, candidate.header, &candidate.blocks)
        else {
            continue;
        };
        let local = LocalId(locals.len());
        locals.push(local);
        local_debug_hints.push(None);
        numeric_for_locals.insert(candidate.header, local);

        for block in &candidate.blocks {
            block_local_regs
                .entry(*block)
                .or_insert_with(BTreeMap::new)
                .insert(reg, local);
        }
    }

    for candidate in structure
        .loop_candidates
        .iter()
        .filter(|candidate| candidate.kind_hint == LoopKindHint::GenericForLike)
    {
        let Some(bindings) = generic_for_binding_regs(proto, cfg, candidate.header) else {
            continue;
        };
        let mut locals_for_loop = Vec::with_capacity(bindings.len);
        for offset in 0..bindings.len {
            let local = LocalId(locals.len());
            locals.push(local);
            local_debug_hints.push(None);
            let reg = crate::transformer::Reg(bindings.start.index() + offset);
            locals_for_loop.push(local);

            for block in &candidate.blocks {
                block_local_regs
                    .entry(*block)
                    .or_insert_with(BTreeMap::new)
                    .insert(reg, local);
            }
        }
        generic_for_locals.insert(candidate.header, locals_for_loop);
    }

    let fixed_temps = (0..dataflow.defs.len()).map(TempId).collect::<Vec<_>>();
    let open_base = fixed_temps.len();
    let open_temps = (0..dataflow.open_defs.len())
        .map(|index| TempId(open_base + index))
        .collect::<Vec<_>>();
    let mut next_temp_index = open_base + open_temps.len();

    let mut phi_temps = Vec::with_capacity(dataflow.phi_candidates.len());
    for _phi in &dataflow.phi_candidates {
        phi_temps.push(TempId(next_temp_index));
        next_temp_index += 1;
    }

    let temps = (0..next_temp_index).map(TempId).collect::<Vec<_>>();
    let mut temp_debug_locals = vec![None; next_temp_index];

    for def in &dataflow.defs {
        let temp = fixed_temps[def.id.index()];
        temp_debug_locals[temp.index()] =
            debug_local_name_for_reg_at_instr(proto, def.reg, def.instr);
    }

    for open_def in &dataflow.open_defs {
        let temp = open_temps[open_def.id.index()];
        temp_debug_locals[temp.index()] = debug_local_name_for_open_def_start(proto, open_def);
    }

    let instr_fixed_defs = dataflow
        .instr_defs
        .iter()
        .map(|defs| {
            defs.iter()
                .map(|def| fixed_temps[def.index()])
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    let mut instr_open_defs = vec![None; proto.instrs.len()];
    for open_def in &dataflow.open_defs {
        instr_open_defs[open_def.instr.index()] = Some(open_temps[open_def.id.index()]);
    }

    // 这一层默认只消费 reachable 子图，所以 label/temp 也贴着 shared CFG/Dataflow 的约定。
    let _ = cfg;

    ProtoBindings {
        params,
        locals,
        local_debug_hints,
        upvalues,
        temps,
        temp_debug_locals,
        fixed_temps,
        open_temps,
        phi_temps,
        instr_fixed_defs,
        instr_open_defs,
        entry_local_regs,
        numeric_for_locals,
        generic_for_locals,
        block_local_regs,
    }
}

fn debug_local_name_for_open_def_start(proto: &LoweredProto, open_def: &OpenDef) -> Option<String> {
    debug_local_name_for_reg_at_instr(proto, open_def.start_reg, open_def.instr)
}

fn debug_local_name_for_reg_at_instr(
    proto: &LoweredProto,
    reg: Reg,
    instr: InstrRef,
) -> Option<String> {
    let pc = proto
        .lowering_map
        .pc_map
        .get(instr.index())?
        .first()
        .copied()?;
    debug_local_name_for_reg_at_pc(proto, reg, pc)
}

fn debug_local_name_for_reg_at_pc(proto: &LoweredProto, reg: Reg, pc: u32) -> Option<String> {
    proto
        .debug_info
        .common
        .local_vars
        .iter()
        .filter(|local| debug_local_is_active_at_pc(local, pc))
        .nth(reg.index())
        .map(|local| decode_raw_string(&local.name))
}

fn debug_local_is_active_at_pc(local: &RawLocalVar, pc: u32) -> bool {
    local.start_pc <= pc && pc < local.end_pc
}

fn numeric_for_binding_reg(
    proto: &LoweredProto,
    cfg: &Cfg,
    loop_header: crate::cfg::BlockRef,
    loop_blocks: &BTreeSet<crate::cfg::BlockRef>,
) -> Option<crate::transformer::Reg> {
    let preheader = cfg.preds[loop_header.index()]
        .iter()
        .map(|edge_ref| cfg.edges[edge_ref.index()].from)
        .find(|pred| !loop_blocks.contains(pred))?;
    let instr_ref = cfg.blocks[preheader.index()].instrs.last()?;

    match proto.instrs.get(instr_ref.index())? {
        crate::transformer::LowInstr::NumericForInit(instr) => Some(instr.binding),
        _ => None,
    }
}

fn generic_for_binding_regs(
    proto: &LoweredProto,
    cfg: &Cfg,
    loop_header: crate::cfg::BlockRef,
) -> Option<crate::transformer::RegRange> {
    let instr_ref = cfg.blocks[loop_header.index()].instrs.last()?;

    match proto.instrs.get(instr_ref.index())? {
        crate::transformer::LowInstr::GenericForLoop(instr) => Some(instr.bindings),
        _ => None,
    }
}
