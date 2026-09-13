//! 为已证明 CLOSE 窗口的低槽闭包输出接回原 nil 声明。
//!
//! 窗口来自 capture owner，定义、读取和根区间来自 Dataflow，父级发射位置来自
//! HirEmissionFacts。这里只分配绑定候选，不重建 CFG 或把高槽 CLOSURE scratch 合并到
//! holder。省略 LOADNIL 的入口只消费原 Def 覆盖 Entry(nil) 的证明，不伪造初始化 Temp。
//! 例如 `local f; do local x=1; f=function() return x end; x=2 end; use(f)`
//! 的 f 保留在原 nil 位置，避免块外 Temp 在 AST 被提前到整个函数入口。
//! 候选只覆盖向前 CFG 中的非循环单块窗口，且 holder 的最后定义一直保活到返回；
//! 其它覆盖、Phi、捕获或源作用域仍由已有 owner 处理。

use super::*;

pub(super) struct ClosedOutputBinding {
    pub(super) initial: Option<TempId>,
    pub(super) output: TempId,
    pub(super) home: HomeSlotKey,
}

#[expect(
    clippy::too_many_arguments,
    reason = "窗口、SSA、发射与捕获事实来自同一 bindings 快照，不能丢失原 owner"
)]
pub(super) fn collect(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph: &GraphFacts,
    dataflow: &DataflowFacts,
    structure: &ReadyStructureFacts,
    emission: &HirEmissionFacts<'_>,
    epochs: &SlotEpochFacts,
    captured: &CapturedSlotTargets,
    lexical_scopes: &[std::ops::Range<usize>],
    fixed_temps: &[TempId],
) -> Vec<ClosedOutputBinding> {
    if captured.lexical_scopes.is_empty()
        || cfg.edges.iter().any(|edge| {
            cfg.blocks[edge.to.index()].instrs.start <= cfg.blocks[edge.from.index()].instrs.start
        })
    {
        return Vec::new();
    }
    // 一次标出所有已接受词法窗口；nil 必须在函数父级，而不是另一个已关闭窗口中。
    let mut depths = vec![0isize; proto.instrs.len() + 1];
    for scope in lexical_scopes {
        depths[scope.start] += 1;
        depths[scope.end] -= 1;
    }
    let mut depth = 0;
    for value in &mut depths {
        depth += *value;
        *value = depth;
    }
    let aliases = fixed_temps
        .iter()
        .enumerate()
        .filter_map(|(index, &temp)| (temp != TempId(index)).then_some(temp))
        .collect::<BTreeSet<_>>();
    let last_unknown_observation = dataflow
        .effect_summaries
        .iter()
        .enumerate()
        .filter(|(_, summary)| {
            summary.may_observe_gc_roots()
                && matches!(
                    summary.root_observation,
                    crate::structure::RootObservation::None
                )
        })
        .map(|(index, _)| index)
        .next_back();
    // PUC RETURN 可降低为同来源的 CLOSE + RETURN；词法 cleanup 没有另一次 TBC
    // 观察。只在最终原退出协议处结束根窗口，普通 CLOSE 仍是禁止跨越的边界。
    let root_end = proto
        .instrs
        .len()
        .checked_sub(2)
        .filter(|&index| {
            matches!((&proto.instrs[index], &proto.instrs[index + 1]),
            (LowInstr::Close(close), LowInstr::Return(_))
                if close.kind == crate::transformer::CloseKind::Return(InstrRef(index + 1)))
                && cfg.instr_to_block[index] == cfg.instr_to_block[index + 1]
                && matches!(
                    structure.plan().cleanup_disposition(InstrRef(index)),
                    Some(CleanupDisposition::LexicalScope(_))
                )
        })
        .unwrap_or(proto.instrs.len());
    let capture_windows = captured
        .lexical_scopes
        .iter()
        .map(|scope| (scope.start, scope.end))
        .collect::<BTreeSet<_>>();
    let windows = lexical_scopes
        .iter()
        .map(|scope| (scope.start, scope.end))
        .filter(|scope| capture_windows.contains(scope))
        .collect::<BTreeSet<_>>();
    let mut result = Vec::new();
    for (start, end) in windows {
        let Some(close_index) = end.checked_sub(1) else {
            continue;
        };
        let Some(LowInstr::Close(close)) = proto.instrs.get(close_index) else {
            continue;
        };
        let block = cfg.instr_to_block[start];
        if depths[start] != 1
            || cfg.instr_to_block[close_index] != block
            || graph.block_is_cyclic(block)
            || emission.scope_owner(block) != Some(structure.plan().root())
        {
            continue;
        }
        // 深度为一的非交叉窗口互不重叠；每个窗口内的定义只审理一次。
        for index in start..close_index {
            let [output_def] = dataflow.instr_defs[index].as_slice() else {
                continue;
            };
            let reg = dataflow.def_reg(*output_def);
            if reg >= close.from || !is_closure_output(proto, dataflow, fixed_temps, start, index) {
                continue;
            }
            let definitions = dataflow.fixed_defs_for_reg(reg);
            if definitions.last() != Some(output_def) {
                continue;
            }
            let before =
                definitions.partition_point(|&def| dataflow.def_instr(def).index() < start);
            let initial_def = before
                .checked_sub(1)
                .and_then(|index| definitions.get(index))
                .copied();
            // 窗口内只能有这次 holder 写，不能把中间身份/覆盖链一并绑定。
            if definitions.get(before) != Some(output_def) {
                continue;
            }
            let output = fixed_temps[output_def.index()];
            let home = HomeSlotKey::new(reg.index(), epochs.epoch_at(reg, InstrRef(index)));
            let initial = if let Some(initial_def) = initial_def {
                let initial_index = dataflow.def_instr(initial_def).index();
                let initial = fixed_temps[initial_def.index()];
                if initial != TempId(initial_def.index())
                    || aliases.contains(&initial)
                    || !matches!(proto.instrs[initial_index], LowInstr::LoadNil(_))
                    || HomeSlotKey::new(reg.index(), epochs.epoch_at(reg, InstrRef(initial_index)))
                        != home
                    || depths[initial_index] != 0
                    || cfg.instr_to_block[initial_index] != block
                    || !emission
                        .regular_prefix(block)
                        .is_some_and(|prefix| prefix.contains(&initial_index))
                    || !dataflow.def_uses[initial_def.index()].is_empty()
                    || !dataflow.def_phi_uses[initial_def.index()].is_empty()
                {
                    continue;
                }
                Some(initial)
            } else {
                let param_count = usize::from(proto.signature.num_params);
                let vararg_reg = proto
                    .signature
                    .has_vararg_param_reg
                    .then_some(Reg(param_count));
                if start != 0
                    || block != cfg.entry_block
                    || home != HomeSlotKey::new(reg.index(), 0)
                    || reg.index() < param_count
                    || Some(reg) == vararg_reg
                    || dataflow.def_overwrites_unknown_scratch(*output_def)
                    || dataflow.def_overwritten_value(*output_def) != Some(SsaValue::Entry(reg))
                    || !emission
                        .regular_prefix(block)
                        .is_some_and(|prefix| prefix.contains(&0))
                {
                    continue;
                }
                None
            };
            if output != TempId(output_def.index())
                || aliases.contains(&output)
                || !captured.home_is_uncaptured(home)
                || !dataflow.def_phi_uses[output_def.index()].is_empty()
                || !dataflow.def_uses[output_def.index()]
                    .iter()
                    .any(|site| site.instr.index() >= end)
                || last_unknown_observation.is_some_and(|site| site > index)
                || dataflow
                    .root_intervals
                    .first_open_write(index + 1..proto.instrs.len(), reg.index())
                    .is_some()
                || dataflow
                    .root_intervals
                    .first_close(index + 1..root_end, reg.index())
                    .is_some()
                || dataflow
                    .root_intervals
                    .minimum_rooted_prefix(index + 1..proto.instrs.len())
                    .is_some_and(|prefix| reg.index() >= prefix)
            {
                continue;
            }
            result.push(ClosedOutputBinding {
                initial,
                output,
                home,
            });
        }
    }
    result
}

fn is_closure_output(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    fixed_temps: &[TempId],
    start: usize,
    index: usize,
) -> bool {
    match &proto.instrs[index] {
        LowInstr::Closure(_) => true,
        LowInstr::Move(copy) if index > start => {
            let source_index = index - 1;
            let LowInstr::Closure(closure) = &proto.instrs[source_index] else {
                return false;
            };
            let [source_def] = dataflow.instr_defs[source_index].as_slice() else {
                return false;
            };
            closure.dst == copy.src
                && dataflow.use_value(InstrRef(index), copy.src) == SsaValue::Def(*source_def)
                && fixed_temps[source_def.index()] == TempId(source_def.index())
                && dataflow.def_phi_uses[source_def.index()].is_empty()
                && matches!(dataflow.def_uses[source_def.index()].as_slice(), [site] if site.instr == InstrRef(index))
        }
        _ => false,
    }
}
