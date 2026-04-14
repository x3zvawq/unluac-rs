//! 这个文件专门负责把 Dataflow 的定义身份提升成 HIR 可直接消费的绑定表。
//!
//! 这个 pass 依赖前层已经给好的结构证据和数据流事实，不再回头重扫 CFG/low-IR 去猜
//! loop binding 或 merge 形状；它只负责“分配稳定身份”。
//!
//! 例子：
//! - `for i = 1, n do ... end` 对应的 `NumericForLike + LoopSourceBindings::Numeric(rX)`
//!   会直接产出一个 `LocalId` 绑定到该 loop header
//! - `for k, v in iter() do ... end` 对应的 `LoopSourceBindings::Generic(rA..)` 会直接产出
//!   一组 header locals，而不是再从 `GenericForLoop` terminator 回扫一次

use std::collections::BTreeMap;

use crate::cfg::{BlockRef, Cfg, DataflowFacts, GraphFacts, OpenDef};
use crate::hir::common::{LocalId, ParamId, TempId, UpvalueId};
use crate::parser::RawLocalVar;
use crate::structure::{LoopSourceBindings, StructureFacts};
use crate::transformer::{InstrRef, LoweredProto, Reg};

use super::ProtoBindings;
use super::helpers::decode_raw_string;

pub(super) fn build_bindings(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    structure: &StructureFacts,
) -> ProtoBindings {
    let params = (0..usize::from(proto.signature.num_params))
        .map(ParamId)
        .collect::<Vec<_>>();
    let param_debug_hints = (0..params.len())
        .map(|reg| debug_local_name_for_reg_at_pc(proto, Reg(reg), 0))
        .collect::<Vec<_>>();
    let upvalues = (0..usize::from(proto.upvalues.common.count))
        .map(UpvalueId)
        .collect::<Vec<_>>();
    let upvalue_debug_hints = (0..upvalues.len())
        .map(|index| {
            proto
                .debug_info
                .common
                .upvalue_names
                .get(index)
                .map(decode_raw_string)
        })
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

    for candidate in &structure.loop_candidates {
        match candidate.source_bindings {
            Some(LoopSourceBindings::Numeric(reg)) => {
                let local = LocalId(locals.len());
                locals.push(local);
                local_debug_hints.push(None);
                numeric_for_locals.insert(candidate.header, local);

                // 除 natural loop body 内的块外，还需要为从循环体提前退出（如
                // return/break 分支）且被 header 支配的出口块注册绑定映射。
                let binding_blocks = loop_binding_scope(
                    &candidate.blocks,
                    &candidate.exits,
                    candidate.header,
                    cfg,
                    graph_facts,
                );
                for block in &binding_blocks {
                    block_local_regs
                        .entry(*block)
                        .or_insert_with(BTreeMap::new)
                        .insert(reg, local);
                }
            }
            Some(LoopSourceBindings::Generic(bindings)) => {
                let binding_blocks = loop_binding_scope(
                    &candidate.blocks,
                    &candidate.exits,
                    candidate.header,
                    cfg,
                    graph_facts,
                );
                let mut locals_for_loop = Vec::with_capacity(bindings.len);
                for offset in 0..bindings.len {
                    let local = LocalId(locals.len());
                    locals.push(local);
                    local_debug_hints.push(None);
                    let reg = crate::transformer::Reg(bindings.start.index() + offset);
                    locals_for_loop.push(local);

                    for block in &binding_blocks {
                        block_local_regs
                            .entry(*block)
                            .or_insert_with(BTreeMap::new)
                            .insert(reg, local);
                    }
                }
                generic_for_locals.insert(candidate.header, locals_for_loop);
            }
            None => {}
        }
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

    for phi in &dataflow.phi_candidates {
        let temp = phi_temps[phi.id.index()];
        temp_debug_locals[temp.index()] =
            debug_local_name_for_reg_at_block_entry(proto, cfg, phi.block, phi.reg);
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
        param_debug_hints,
        locals,
        local_debug_hints,
        upvalues,
        upvalue_debug_hints,
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

fn debug_local_name_for_reg_at_block_entry(
    proto: &LoweredProto,
    cfg: &Cfg,
    block: crate::cfg::BlockRef,
    reg: Reg,
) -> Option<String> {
    let instrs = cfg.blocks[block.index()].instrs;
    if instrs.is_empty() {
        return None;
    }
    let instr = instrs.start;
    debug_local_name_for_reg_at_instr(proto, reg, instr)
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

/// 计算 for-loop binding 的可见作用域块集合。
///
/// natural loop 拓扑只包含能回到 header 的 body 块，不含通过 return/break
/// 提前离开循环的块。但在 Lua 语义下，这些提前退出的块仍处于 for-binding
/// 的词法作用域中（如 `for i = 1, n do if cond then return i end end`）。
///
/// 策略：在 candidate.blocks 基础上，追加被 header 严格支配的 **提前退出** 块。
/// 只有不是通过 LoopExit 边到达的出口块才被视为提前退出——LoopExit 边的
/// 目标是循环正常结束后的后继块，for-binding 在那里已失效。
///
/// 示例：
/// - `for i = 1, n do if cond then return i end end`
///   return 所在块通过 BranchFalse 从 header 到达，被 header 支配 → 纳入作用域
/// - `for k, v in pairs(t) do ... end; print(k)`
///   print 所在块通过 LoopExit 从 body 到达 → 不纳入，for-binding 不可见
fn loop_binding_scope(
    body_blocks: &std::collections::BTreeSet<BlockRef>,
    exits: &std::collections::BTreeSet<BlockRef>,
    header: BlockRef,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
) -> std::collections::BTreeSet<BlockRef> {
    use crate::cfg::EdgeKind;

    let mut scope = body_blocks.clone();
    for &exit in exits {
        if exit == header || !graph_facts.dominator_tree.dominates(header, exit) {
            continue;
        }
        // 检查该出口块是否通过 LoopExit 边从循环体到达——如果是，
        // 说明它是循环正常完成后的后继块，for-binding 在那里不可见。
        let reached_via_loop_exit = cfg.preds[exit.index()].iter().any(|edge_ref| {
            let edge = &cfg.edges[edge_ref.index()];
            body_blocks.contains(&edge.from) && edge.kind == EdgeKind::LoopExit
        });
        if !reached_via_loop_exit {
            scope.insert(exit);
        }
    }
    scope
}
