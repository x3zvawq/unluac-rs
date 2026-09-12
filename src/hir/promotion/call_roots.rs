//! 将 Dataflow 的调用边界与 canonical 参数 def 配对，冻结 caller 槽交接事实。
//! 同时保留调用结果的同槽覆盖与精确 dispatch 终点，使 HIR 不必重扫低层后缀。
//!
//! CALL 参数位于 caller prefix 之外，callee 可覆盖这些槽；它们不是跨调用继续存在的
//! 独立 caller root。例如 t = {}; f(t) 的参数槽可交给 f，而 local owner; f(owner) 中
//! owner 的原始低槽不随参数 MOVE 一并交出。这里只发布同 basic block 的 direct def，
//! phi、跨 block use 和按引用捕获槽不产生证明；调用结果最后读取后的覆盖可以位于各直接
//! successor，由 Dataflow 发布完整 frontier。实际 producer 删除由 HIR 求值顺序 owner 审查。

use super::*;
use crate::hir::common::HirCallArgumentRoot;
use crate::transformer::ValuePack;

pub(super) fn collect(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    epochs: &SlotEpochFacts,
    fixed_temps: &[TempId],
) -> BTreeMap<InstrRef, Vec<HirCallArgumentRoot>> {
    let mut calls = BTreeMap::new();
    for (index, instr) in proto.instrs.iter().enumerate() {
        let LowInstr::Call(call) = instr else {
            continue;
        };
        // FASTCALL 可在当前 frame 内直接执行 builtin，不能借 fallback 的 CALL 外形
        // 证明参数槽已进入另一个 callee frame。
        if matches!(call.kind, crate::transformer::CallKind::FastCall(_)) {
            continue;
        }
        let args_start = match call.args {
            ValuePack::Fixed(args) => args.start,
            ValuePack::Open(start) => start,
        };
        let RootObservation::Call { caller_end } =
            dataflow.effect_summaries[index].root_observation
        else {
            continue;
        };
        let call_ref = InstrRef(index);
        let mut roots = Vec::new();
        // OPEN 参数的固定前缀已经由 Dataflow 的 SSA use map 证明；不能用可能
        // liveness uses 猜测长度，也不在 HIR 重解 open-top 协议。
        for (reg, value) in dataflow.use_values_at(call_ref).iter() {
            if reg.index() < args_start.index() {
                continue;
            }
            let argument = reg.index() - args_start.index();
            if reg.index() <= caller_end.index()
                || epochs.reference_capture_may_be_open(reg, call_ref)
            {
                continue;
            }
            let SsaValue::Def(def) = value else {
                continue;
            };
            let producer = TempId(def.index());
            if fixed_temps[def.index()] != producer
                || dataflow.def_reg(def) != reg
                || dataflow.def_block(def) != cfg.instr_to_block[index]
                || dataflow.def_instr(def).index() >= index
                || !dataflow.def_phi_uses[def.index()].is_empty()
                || dataflow.def_uses[def.index()].iter().any(|use_| {
                    use_.instr.index() <= dataflow.def_instr(def).index()
                        || use_.instr.index() > index
                })
            {
                continue;
            }
            roots.push(HirCallArgumentRoot { producer, argument });
        }
        if !roots.is_empty() {
            calls.insert(call_ref, roots);
        }
    }
    calls
}

/// 同一共享 Dataflow 事实给出 call result 的独立 root 后缀终点；HIR 不从后缀文本猜 MOVE。
pub(super) fn collect_unobserved_result_ends(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    fixed_temps: &[TempId],
) -> BTreeMap<TempId, Vec<TempId>> {
    dataflow
        .defs
        .iter()
        .filter_map(|def| {
            let producer = TempId(def.id.index());
            if fixed_temps[def.id.index()] != producer
                || dataflow.reg_is_reference_captured(def.reg)
                || !matches!(proto.instrs[def.instr.index()], LowInstr::Call(_))
            {
                return None;
            }
            let ends = dataflow.unobserved_root_overwrite_frontier_after_last_use(def.id, cfg)?;
            let endpoints = ends
                .into_iter()
                .map(|end| {
                    let endpoint = TempId(end.index());
                    (fixed_temps[end.index()] == endpoint).then_some(endpoint)
                })
                .collect::<Option<Vec<_>>>()?;
            Some((producer, endpoints))
        })
        .collect()
}

/// 将 direct call result 的 caller home 终点投影到精确调用；此前允许存在 GGET 等观察。
/// 每个候选只加入、退休一次；CALL 按寄存器边界切走后缀，不逐调用重扫全部 definition。
pub(super) fn collect_frame_result_ends(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    epochs: &SlotEpochFacts,
    fixed_temps: &[TempId],
) -> BTreeMap<InstrRef, Vec<TempId>> {
    let mut calls = BTreeMap::new();
    for &block in &cfg.block_order {
        let mut active = BTreeMap::<Reg, (TempId, usize)>::new();
        let range = cfg.blocks[block.index()].instrs;
        for index in range.start.index()..range.end() {
            let instr_ref = InstrRef(index);
            let instr = &proto.instrs[index];
            let observation = dataflow.effect_summaries[index].root_observation;
            let effect = &dataflow.instr_effects[index];
            if let RootObservation::Call { caller_end } = observation {
                let ended = active.split_off(&caller_end);
                // FASTCALL 可能在当前 frame 执行 builtin；只能使证书失效，不能签发终点。
                if matches!(instr, LowInstr::Call(call)
                    if !matches!(call.kind, crate::transformer::CallKind::FastCall(_)))
                {
                    let roots = ended
                        .into_iter()
                        .filter_map(|(reg, (temp, last_use))| {
                            (last_use < index
                                && !effect.uses_fixed(reg)
                                && effect.open_use.is_none_or(|start| reg < start))
                            .then_some(temp)
                        })
                        .collect::<Vec<_>>();
                    if !roots.is_empty() {
                        calls.insert(instr_ref, roots);
                    }
                }
            }
            match instr {
                LowInstr::Closure(closure) => {
                    for capture in &closure.captures {
                        if let CaptureSource::ByReference(reg) = capture.source {
                            active.remove(&reg);
                        }
                    }
                }
                LowInstr::Close(close) => {
                    active.split_off(&close.from);
                }
                LowInstr::GenericForCall(_) => {
                    // 迭代 dispatch 只发布有效前缀下界，不能证明高槽未经潜在覆盖。
                    if let RootObservation::PrefixLowerBound { end } = observation {
                        active.split_off(&Reg(end));
                    }
                }
                _ => {}
            }
            for reg in effect.fixed_must_defs() {
                active.remove(reg);
            }
            if let Some(start) = effect.open_must_def {
                active.split_off(&start);
            }
            if !matches!(instr, LowInstr::Call(_)) {
                continue;
            }
            for &def in &dataflow.instr_defs[index] {
                let producer = TempId(def.index());
                let reg = dataflow.def_reg(def);
                if fixed_temps[def.index()] != producer
                    || !dataflow.def_phi_uses[def.index()].is_empty()
                    || epochs.reference_capture_may_be_open(reg, instr_ref)
                {
                    continue;
                }
                // 当前 dispatch 的 callee/参数读取也必须排除；空 use 的固定多返回值仍有 home。
                let last_use =
                    dataflow.def_uses[def.index()]
                        .iter()
                        .try_fold(index, |last, use_| {
                            (use_.instr.index() > index
                                && cfg.instr_to_block[use_.instr.index()] == block)
                                .then_some(last.max(use_.instr.index()))
                        });
                if let Some(last_use) = last_use {
                    active.insert(reg, (producer, last_use));
                }
            }
        }
    }
    calls
}
