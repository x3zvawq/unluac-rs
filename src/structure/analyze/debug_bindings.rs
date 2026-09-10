//! 将源码调试 local 生命周期映射到 canonical SSA；依赖 lowering map 与数据流，不负责 HIR 命名；例如在初始化指令后找到唯一 local 候选。

use super::*;
use crate::structure::SsaValue;

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

    let mut facts = DebugBindingFacts {
        by_scope: vec![None; proto.debug_locals.len()],
        ..Default::default()
    };
    for (value, scopes) in by_value {
        if let [scope] = scopes.as_slice() {
            let local = &proto.debug_locals[*scope];
            facts.by_scope[*scope] = Some(facts.accepted.len());
            facts.accepted.push(DebugBindingFact {
                scope: *scope,
                reg: local.reg,
                start_pc: local.start_pc,
                end_pc: local.end_pc,
                end_instr: proto.lowering_map.low_instr_at_or_after_pc(local.end_pc),
                value,
                declaration_block: match value {
                    SsaValue::Def(def) => Some(dataflow.def_block(def)),
                    SsaValue::Phi(phi) => Some(dataflow.phi_candidates[phi.index()].block),
                    SsaValue::Entry(_) => None,
                },
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
    // 参数在首条指令执行前已建立；PC 0 的重绑定不是参数 scope 的初始化。
    if start_pc == 0 && reg.index() < usize::from(proto.signature.num_params) {
        return super::super::SsaValue::Entry(reg);
    }
    let block = cfg.instr_to_block[instr.index()];
    let start = cfg.blocks[block.index()].instrs.start.index();
    // 归一化 start_pc 指向作用域首条指令执行前；该指令可能立即重绑定 local。
    // 例如 `local a,b=f(); a,b=nil,nil`，b 的入口仍是 call result，不能改取后续 nil Def。
    dataflow
        .last_fixed_def_in_range(reg, start..instr.index())
        .map_or_else(
            || dataflow.block_entry_value(block, reg),
            super::super::SsaValue::Def,
        )
}
