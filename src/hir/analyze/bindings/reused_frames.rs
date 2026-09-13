//! 在原 numeric-for header 复用低槽前，恢复已闭合的直线声明帧。
//!
//! 事实来自冻结 for 协议、Dataflow 的固定定义/使用和共享求值起点查询；不推断循环次数，
//! 不把逻辑 binding Def 当作无条件物理清零。例：`do local a,b,c,t=false,false,false,{};
//! weak[1]=t end; for i=header(arg()) ... end` 保留四个原槽，在 header 首求值前结束 do，
//! 让参数查找、CALL 和 FORPREP 各自在原位置观察或覆盖旧根，而不是提前生成 nil。
//! 这里只接受入口直线帧：首次定义按原槽递增，后续同槽写仍属于该窗口，所有高槽使用
//! 和 Phi 都不逃出；低槽前缀限参数及单写常量。窗口内 CALL/open/capture 不借此改址。
//! 每个 preheader 只处理一次，全部绑定和不交叉边界先证明，再一起发布；后层不重建原槽。

use super::*;
use crate::hir::promotion::ProtoPromotionFacts;

struct FrameSlot {
    home: HomeSlotKey,
    temps: Vec<TempId>,
    scope: Option<usize>,
}

pub(in crate::hir::analyze) fn bind_reused_frames(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    structure: &ReadyStructureFacts,
    emission: &HirEmissionFacts<'_>,
    bindings: &mut ProtoBindings,
    facts: &mut ProtoPromotionFacts,
) -> Vec<LocalId> {
    let mut preserved = Vec::new();
    let mut visited = BTreeSet::new();
    for (id, _) in structure.plan().loops() {
        let Some(LoopVmProtocol::NumericFor(protocol)) = structure.plan().loop_protocol(id) else {
            continue;
        };
        let block = cfg.instr_to_block[protocol.init_instr.index()];
        if !visited.insert(block)
            || block != cfg.entry_block
            || proto.signature.legacy_arg_slot
            || proto.signature.has_vararg_param_reg
        {
            continue;
        }
        let base = protocol.index;
        if base > protocol.limit || base > protocol.step {
            continue;
        }
        let Some(end) =
            lexical_scope_evaluation_start(dataflow, cfg, block, base, protocol.init_instr.index())
        else {
            continue;
        };
        let Some((start, slots)) =
            candidate(proto, cfg, dataflow, bindings, facts, block, base, end)
        else {
            continue;
        };
        let Some(prefix) = emission.regular_prefix(block) else {
            continue;
        };
        if !prefix.contains(&start) || !prefix.contains(&end) {
            continue;
        }
        let mut scopes = bindings.lexical_scopes.clone();
        scopes.push(start..end);
        let expected = scopes
            .iter()
            .map(|range| (range.start, range.end))
            .collect::<BTreeSet<_>>();
        let scopes = lexical_windows::retain_non_crossing(scopes);
        if scopes.len() != expected.len() {
            continue;
        }
        bindings.lexical_scopes = scopes;
        for slot in slots {
            let local = LocalId(bindings.local_count);
            bindings.local_count += 1;
            bindings
                .local_debug_hints
                .push(bindings.temp_debug_locals[slot.temps[0].index()].clone());
            bindings.local_debug_scopes.push(slot.scope);
            bindings.temp_decl_locals.insert(slot.temps[0], local);
            bindings.declared_local_home_slots.push((local, slot.home));
            facts.record_local_home_slot(local, slot.home);
            for temp in slot.temps {
                bindings
                    .bound_temp_targets
                    .insert(temp, BoundSlotTarget::Local(local));
                facts.record_temp_to_local_merge(temp, local);
            }
            preserved.push(local);
        }
    }
    preserved
}

#[expect(
    clippy::too_many_arguments,
    reason = "候选借用同一原帧和绑定快照，不复制跨层事实"
)]
fn candidate(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    bindings: &ProtoBindings,
    facts: &ProtoPromotionFacts,
    block: BlockRef,
    base: Reg,
    end: usize,
) -> Option<(usize, Vec<FrameSlot>)> {
    let params = usize::from(proto.signature.num_params);
    if base.index() < params {
        return None;
    }
    let mut slots = Vec::<FrameSlot>::new();
    let mut start = None;
    let mut defined = BTreeSet::new();
    for index in cfg.blocks[block.index()].instrs.start.index()..end {
        let instr = &proto.instrs[index];
        let effect = &dataflow.instr_effects[index];
        if instr.is_control_terminator()
            || matches!(
                instr,
                LowInstr::Call(_) | LowInstr::Close(_) | LowInstr::Tbc(_)
            )
            || effect.open_use.is_some()
            || effect.open_must_def.is_some()
        {
            return None;
        }
        for &reg in effect.fixed_uses_from(Reg(params)) {
            let SsaValue::Def(def) = dataflow.use_value(InstrRef(index), reg) else {
                return None;
            };
            if !defined.contains(&def) {
                return None;
            }
        }
        for &def in &dataflow.instr_defs[index] {
            let reg = dataflow.def_reg(def);
            if reg.index() < params {
                return None;
            }
            let offset = reg.index() - params;
            if offset > slots.len() || dataflow.reg_is_reference_captured(reg) {
                return None;
            }
            let temp = TempId(def.index());
            if bindings.fixed_temps[def.index()] != temp
                || bindings.bound_temp_targets.contains_key(&temp)
                || bindings.captured_temp_targets.contains_key(&temp)
                || bindings.temp_decl_locals.contains_key(&temp)
                || !dataflow.def_phi_uses[def.index()].is_empty()
            {
                return None;
            }
            let home = facts.trusted_temp_home_slot(temp)?;
            if !facts
                .complete_temp_definition_write_homes(temp)
                .iter()
                .copied()
                .eq(std::iter::once(home))
            {
                return None;
            }
            let scope = bindings.temp_debug_scopes[temp.index()];
            if offset == slots.len()
                && scope.is_none()
                && matches!(instr, LowInstr::GetUpvalue(_))
                && dataflow.def_uses[def.index()]
                    .as_slice()
                    .first()
                    .is_some_and(|site| site.instr.index() == index + 1)
                && dataflow.def_uses[def.index()].len() == 1
                && let Some(LowInstr::SetTable(set)) = proto.instrs.get(index + 1)
                && set.base == AccessBase::Reg(reg)
                && set.key != crate::transformer::AccessKey::Reg(reg)
                && set.value != crate::transformer::ValueOperand::Reg(reg)
            {
                // 紧邻字段写的裸 upvalue base 仍交给原 access/temp-inline owner。
                // 它在当前 freereg 准备，不是一个源码声明；后续同槽 alias 有自己的身份。
                defined.insert(def);
                continue;
            }
            if reg < base {
                // 外围单写常量保留原声明位置；其它运算或低槽复写不纳入此候选。
                if offset != slots.len()
                    || start.is_some()
                    || !matches!(
                        instr,
                        LowInstr::LoadNil(_)
                            | LowInstr::LoadBool(_)
                            | LowInstr::LoadConst(_)
                            | LowInstr::LoadInteger(_)
                            | LowInstr::LoadNumber(_)
                    )
                {
                    return None;
                }
            } else {
                start.get_or_insert(index);
                if dataflow.def_uses[def.index()]
                    .iter()
                    .any(|site| site.instr.index() >= end)
                {
                    return None;
                }
            }
            if offset == slots.len() {
                slots.push(FrameSlot {
                    home,
                    temps: vec![temp],
                    scope,
                });
            } else {
                let slot = &mut slots[offset];
                if slot.home != home || scope.is_some_and(|scope| Some(scope) != slot.scope) {
                    return None;
                }
                slot.temps.push(temp);
            }
            defined.insert(def);
        }
    }
    // 无旧高槽声明时没有需要恢复的帧；声明不可落在整条多目标写的中间。
    let start = start?;
    if params + slots.len() <= base.index()
        || dataflow.instr_defs[start]
            .iter()
            .any(|&def| dataflow.def_reg(def) < base)
    {
        return None;
    }
    Some((start, slots))
}
