//! 为未读的固定 CALL 结果恢复原槽复用前的词法末端。
//!
//! 单结果接收仍影响 VM 帧，不能改成忽略结果。Dataflow 证明准备区的全部定义均不活出，
//! 后继原 callee 准备立即覆盖结果槽时，把完整准备和 CALL 放入独立窗口：
//! `do local result=seed(args) end; callback(true)`，避免 locals 把 result 接到更晚的
//! 同槽表分配，抬高中间 CALL 的空闲槽。这里只分配身份和窗口，调用表达式与源码前缀
//! 仍由现有 native frame owner 验证；不提前清空结果、不改写 CALL 的接收宽度。
//! 每个块按 CALL/cleanup 分割准备区，每条指令和定义使用至多检查一次；跨前次 CALL
//! 的高槽依赖、open/capture 和未单独发射的范围不借此重建。

use super::*;
use crate::hir::promotion::ProtoPromotionFacts;
use crate::transformer::{CallKind, ResultPack};

pub(in crate::hir::analyze) fn bind_discarded_call_results(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    emission: &HirEmissionFacts<'_>,
    bindings: &mut ProtoBindings,
    facts: &mut ProtoPromotionFacts,
) -> Vec<LocalId> {
    let mut candidates = Vec::new();
    for (block_index, block) in cfg.blocks.iter().enumerate() {
        let block_id = BlockRef(block_index);
        let Some(prefix) = emission.regular_prefix(block_id) else {
            continue;
        };
        if emission.prefix_is_hoisted(block_id) {
            continue;
        }
        let mut start = block.instrs.start.index();
        for index in block.instrs.start.index()..block.instrs.end() {
            let instr = &proto.instrs[index];
            let LowInstr::Call(call) = instr else {
                if instr.is_control_terminator()
                    || matches!(instr, LowInstr::Close(_) | LowInstr::Tbc(_))
                {
                    start = index + 1;
                }
                continue;
            };
            let window = start..index + 1;
            start = index + 1;
            let ResultPack::Fixed(result) = call.results else {
                continue;
            };
            if call.kind != CallKind::Normal
                || result.len != 1
                || result.start != call.callee
                || result.start.index() < usize::from(proto.signature.num_params)
                || !prefix.contains(&window.start)
                || !prefix.contains(&window.end)
            {
                continue;
            }
            let [def] = dataflow.instr_defs[index].as_slice() else {
                continue;
            };
            let temp = TempId(def.index());
            let Some(home) = facts.trusted_temp_home_slot(temp) else {
                continue;
            };
            // 后继必须是原 CALL 的 callee 准备，而非 `local old=f(); old=p` 的
            // 普通 binding 更新；后者应由原同槽 owner 接续，不能另造第二个声明。
            if home.slot() != result.start.index()
                || !dataflow.instr_defs[window.end].iter().any(|&next| {
                    let [use_] = dataflow.def_uses[next.index()].as_slice() else {
                        return false;
                    };
                    dataflow.def_reg(next) == result.start
                        && dataflow.def_overwritten_value(next) == Some(SsaValue::Def(*def))
                        && cfg.instr_to_block[use_.instr.index()] == block_id
                        && prefix.contains(&use_.instr.index())
                        && matches!(proto.instrs[use_.instr.index()], LowInstr::Call(consumer)
                            if consumer.callee == result.start)
                })
                || !closed_preparation(proto, dataflow, bindings, &window, result.start)
            {
                continue;
            }
            candidates.push((window, temp, home));
        }
    }
    if candidates.is_empty() {
        return Vec::new();
    }
    let scopes = lexical_windows::retain_non_crossing(
        bindings
            .lexical_scopes
            .iter()
            .cloned()
            .chain(
                candidates
                    .iter()
                    .map(|(window, _, _)| window.clone().into()),
            )
            .collect(),
    )
    .into_iter()
    .map(|window| (window.start, window.end))
    .collect::<BTreeSet<_>>();
    let mut locals = Vec::new();
    for (window, temp, home) in candidates {
        if !scopes.contains(&(window.start, window.end)) {
            continue;
        }
        let local = LocalId(bindings.local_count);
        bindings.local_count += 1;
        bindings.local_debug_hints.push(None);
        bindings.local_debug_scopes.push(None);
        bindings
            .bound_temp_targets
            .insert(temp, BoundSlotTarget::Local(local));
        bindings.temp_decl_locals.insert(temp, local);
        bindings.lexical_scopes.push(window.into());
        facts.record_local_home_slot(local, home);
        facts.record_temp_to_local_merge(temp, local);
        locals.push(local);
    }
    locals
}

fn closed_preparation(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    bindings: &ProtoBindings,
    window: &std::ops::Range<usize>,
    base: Reg,
) -> bool {
    for index in window.clone() {
        let effect = &dataflow.instr_effects[index];
        if effect.open_use.is_some()
            || effect.open_must_def.is_some()
            || matches!(proto.instrs[index], LowInstr::Close(_) | LowInstr::Tbc(_))
            || effect.fixed_must_defs().iter().any(|&reg| reg < base)
            || effect.fixed_uses_from(base).iter().any(|&reg| {
                !matches!(dataflow.use_value(InstrRef(index), reg), SsaValue::Def(def)
                    if window.contains(&dataflow.def_instr(def).index()))
            })
        {
            return false;
        }
        for &def in &dataflow.instr_defs[index] {
            let temp = TempId(def.index());
            if bindings.fixed_temps[def.index()] != temp
                || bindings.bound_temp_targets.contains_key(&temp)
                || bindings.captured_temp_targets.contains_key(&temp)
                || bindings.temp_decl_locals.contains_key(&temp)
                || bindings.temp_debug_scopes[temp.index()].is_some()
                || dataflow.reg_is_reference_captured(dataflow.def_reg(def))
                || !dataflow.def_phi_uses[def.index()].is_empty()
                || dataflow.def_uses[def.index()]
                    .iter()
                    .any(|use_| !window.contains(&use_.instr.index()))
            {
                return false;
            }
        }
    }
    true
}
