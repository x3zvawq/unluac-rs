//! 将源码调试 local 生命周期映射到 SSA 值或无读取的分支初始化。
//! 消费 lowering map、数据流与冻结分支身份，不负责 HIR 绑定分配和命名。

use super::*;
use crate::structure::{DebugBindingValue, SsaValue, StructurePlan};

/// 将源码 local 的生命周期入口锚定到其初始化身份。
///
/// debug 的 `start_pc` 通常位于初始化完成之后；若改用 producer 位置查询，table/closure
/// 这类多指令初始化会错过名称。同一身份上的内嵌 debug 别名不能遮掉紧邻 initializer
/// 的外层声明；完全重合的只读别名共享事实，其余没有唯一归属的情况保留冲突证据。
pub(super) fn analyze_debug_bindings(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph: &GraphFacts,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
) -> DebugBindingFacts {
    let mut scope_entries = Vec::new();
    let mut named_defs = vec![false; dataflow.defs.len()];
    for (scope, local) in proto
        .debug_locals
        .iter()
        .enumerate()
        .filter(|(_, local)| local.is_source())
    {
        let Some(instr) = proto.lowering_map.low_instr_at_or_after_pc(local.start_pc) else {
            continue;
        };
        let ssa_value = empty_generic_for_binding(proto, cfg, dataflow, instr, local)
            .map(SsaValue::Def)
            .unwrap_or_else(|| {
                ssa_value_at_debug_scope_entry(
                    proto,
                    cfg,
                    graph,
                    dataflow,
                    instr,
                    local.reg,
                    local.start_pc,
                )
            });
        if let SsaValue::Def(def) = ssa_value {
            named_defs[def.index()] = true;
        }
        scope_entries.push((scope, instr, ssa_value));
    }
    let branch_initializers = plan
        .regions()
        .filter_map(|(owner, _)| {
            let initializer = plan.unused_comparison_initializer(owner, proto, cfg, dataflow)?;
            graph
                .dominates(initializer.entry, initializer.continuation)
                .then_some((
                    (initializer.continuation, initializer.reg),
                    (owner, initializer),
                ))
        })
        .collect::<BTreeMap<_, _>>();
    let mut by_value = BTreeMap::<DebugBindingValue, Vec<usize>>::new();
    for (scope, instr, ssa_value) in scope_entries {
        let local = &proto.debug_locals[scope];
        let block = cfg.instr_to_block[instr.index()];
        let mut value = DebugBindingValue::Ssa(ssa_value);
        if ssa_value == SsaValue::Entry(local.reg)
            && instr == cfg.blocks[block.index()].instrs.start
            && let Some((owner, initializer)) = branch_initializers.get(&(block, local.reg))
        {
            if initializer.defs.iter().all(|def| !named_defs[def.index()]) {
                // pruned SSA 没有结果 phi；两臂未被独立 scope 占用时，汇合后的
                // source scope 拥有整个初始化，而不是 block_entry_value 的缺省 Entry。
                value = DebugBindingValue::BranchInitializer(*owner);
            } else if local.start_pc == local.end_pc {
                // 另一臂已有独立声明时，这个零长度 scope 不能拥有整个比较。
                // 紧邻入口、且原 PC 恰在入口前结束的末臂写入才是其 initializer。
                for &def in &initializer.defs {
                    let site = dataflow.def_instr(def);
                    if !named_defs[def.index()]
                        && site.index() + 1 == instr.index()
                        && proto.lowering_map.pc_map()[site.index()]
                            .last()
                            .and_then(|pc| pc.checked_add(1))
                            == Some(local.start_pc)
                    {
                        value = DebugBindingValue::Ssa(SsaValue::Def(def));
                    }
                }
            }
        }
        by_value.entry(value).or_default().push(scope);
    }

    let mut facts = DebugBindingFacts {
        by_scope: vec![None; proto.debug_locals.len()],
        ..Default::default()
    };
    for (value, scopes) in by_value {
        let coincident = (scopes.len() > 1)
            .then(|| coincident_initializer_scope(proto, dataflow, value, &scopes))
            .flatten();
        let scope = match scopes.as_slice() {
            [scope] => Some(*scope),
            _ => {
                coincident.or_else(|| enclosing_initializer_scope(proto, dataflow, value, &scopes))
            }
        };
        if let Some(scope) = scope {
            let local = &proto.debug_locals[scope];
            facts.by_scope[scope] = Some(facts.accepted.len());
            if coincident.is_some() {
                for &alias in &scopes {
                    facts.by_scope[alias] = Some(facts.accepted.len());
                }
            }
            facts.accepted.push(DebugBindingFact {
                scope,
                reg: local.reg,
                start_pc: local.start_pc,
                end_pc: local.end_pc,
                end_instr: proto.lowering_map.low_instr_at_or_after_pc(local.end_pc),
                initializer_end_instr: proto
                    .lowering_map
                    .low_instr_at_or_after_pc(local.start_pc)
                    .and_then(|entry| entry.index().checked_sub(1))
                    // 正式查询返回首个含 PC >= start 的 low；此前所有 PC 必已小于
                    // start，只需排除无来源的前项，不为共享入口的每个 local 重扫来源。
                    .filter(|&index| !proto.lowering_map.pc_map()[index].is_empty())
                    .map(InstrRef),
                value,
                declaration_block: match value {
                    DebugBindingValue::Ssa(SsaValue::Def(def)) => Some(dataflow.def_block(def)),
                    DebugBindingValue::Ssa(SsaValue::Phi(phi)) => {
                        Some(dataflow.phi_candidates[phi.index()].block)
                    }
                    DebugBindingValue::Ssa(SsaValue::Entry(_)) => None,
                    DebugBindingValue::BranchInitializer(_) => {
                        let entry = proto
                            .lowering_map
                            .low_instr_at_or_after_pc(local.start_pc)
                            .expect("accepted scope has an instruction entry");
                        let block = cfg.instr_to_block[entry.index()];
                        Some(branch_initializers[&(block, local.reg)].1.entry)
                    }
                },
            });
        } else {
            facts.conflicts.push(DebugBindingConflict { value, scopes });
        }
    }
    facts
}

/// 完全重合且只读的同槽 scope 是同一运行时 binding 的名称视图。选择
/// DebugLocals 活动查询已有的表序优先级，所有 scope 仍指向该初始化事实。
fn coincident_initializer_scope(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    value: DebugBindingValue,
    scopes: &[usize],
) -> Option<usize> {
    let DebugBindingValue::Ssa(SsaValue::Def(def)) = value else {
        return None;
    };
    let &scope = scopes.first()?;
    let local = &proto.debug_locals[scope];
    if local.start_pc >= local.end_pc
        || dataflow.reg_is_reference_captured(local.reg)
        || !scopes.iter().all(|&other| {
            let other = &proto.debug_locals[other];
            (other.reg, other.start_pc, other.end_pc) == (local.reg, local.start_pc, local.end_pc)
        })
    {
        return None;
    }
    let start = proto
        .lowering_map
        .low_instr_at_or_after_pc(local.start_pc)?
        .index();
    let end = proto
        .lowering_map
        .low_instr_at_or_after_pc(local.end_pc)
        .map_or(proto.instrs.len(), |instr| instr.index());
    // 边界按完整 low 操作，而非 PC+1：Luau GETIMPORT 的 AUX 占原 PC，
    // 但不构成另一条写入。只读证明使用共享写索引，不逐 scope 扫描函数体。
    (dataflow.def_instr(def).index() + 1 == start
        && dataflow
            .first_must_write_in_range(local.reg, start..end)
            .is_none())
    .then_some(scope)
}

fn enclosing_initializer_scope(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    value: DebugBindingValue,
    scopes: &[usize],
) -> Option<usize> {
    let DebugBindingValue::Ssa(SsaValue::Def(def)) = value else {
        return None;
    };
    let scope = *scopes
        .iter()
        .min_by_key(|&&scope| proto.debug_locals[scope].start_pc)?;
    let outer = &proto.debug_locals[scope];
    let producer = dataflow.def_instr(def);
    if proto.lowering_map.pc_map()[producer.index()]
        .last()?
        .checked_add(1)?
        != outer.start_pc
    {
        return None;
    }
    // Luau 内联实参可以直接借用 caller local 的寄存器，并另记一段参数 debug 区间。
    // 同槽、同 SSA、严格内含且没有独立初始化的名称是该值的局部视图；initializer
    // 仍属于紧邻原写入的外层声明。交叉区间或同起点不能据此裁决。
    scopes
        .iter()
        .all(|&other| {
            let inner = &proto.debug_locals[other];
            other == scope
                || (inner.reg == outer.reg
                    && outer.start_pc < inner.start_pc
                    && inner.end_pc <= outer.end_pc)
        })
        .then_some(scope)
}

fn empty_generic_for_binding(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    instr: InstrRef,
    local: &crate::transformer::DebugLocalFact,
) -> Option<crate::structure::DefId> {
    if local.start_pc != local.end_pc
        || !matches!(
            proto.instrs.get(instr.index()),
            Some(LowInstr::GenericForCall(_))
        )
        || !proto.lowering_map.pc_map()[instr.index()].contains(&local.start_pc)
    {
        return None;
    }
    let block = cfg.instr_to_block[instr.index()];
    let LowInstr::GenericForLoop(loop_) = cfg.terminator(&proto.instrs, block)? else {
        return None;
    };
    if loop_.body_target != instr
        || !(loop_.bindings.start.index()..loop_.bindings.start.index() + loop_.bindings.len)
            .contains(&local.reg.index())
    {
        return None;
    }
    // 空 body 的 debug 起止都落在下一次 iterator 调用之前；它描述的是循环变量，
    // 而不是该 PC 前尚未初始化的 entry 槽。用原 dispatch 的结果 Def 保留身份，
    // 不扩大零长度区间，也不把普通作用域入口后的写入误当 initializer。
    dataflow.instr_def_for_reg(instr, local.reg)
}

pub(super) fn ssa_value_at_debug_scope_entry(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph: &GraphFacts,
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
    let value = dataflow
        .last_fixed_def_in_range(reg, start..instr.index())
        .map_or_else(
            || dataflow.block_entry_value(block, reg),
            super::super::SsaValue::Def,
        );
    // 循环每轮先覆盖再读取时，pruned SSA 不保留入口 phi。debug 仍明确把
    // 紧邻 scope 入口前的原写入归给该 local；确认它支配入口，避免把相邻分支
    // 的末笔写误认成共同初始化，也不以回边重赋值替换原声明。
    if value == SsaValue::Entry(reg)
        && let Some(previous) = instr.index().checked_sub(1).map(InstrRef)
        && let Some(def) = dataflow.instr_def_for_reg(previous, reg)
        && proto.lowering_map.pc_map()[previous.index()]
            .last()
            .and_then(|pc| pc.checked_add(1))
            == Some(start_pc)
        && graph.dominates(dataflow.def_block(def), block)
    {
        return SsaValue::Def(def);
    }
    value
}
