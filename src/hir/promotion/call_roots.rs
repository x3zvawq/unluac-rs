//! 将 Dataflow 的调用边界与 canonical 参数 def 配对，冻结 caller 槽交接事实。
//! 同时保留调用结果在最后值读取后、首个观察前的覆盖 def，使写表消费者不必重扫低层后缀。
//!
//! CALL 参数位于 caller prefix 之外，callee 可覆盖这些槽；它们不是跨调用继续存在的
//! 独立 caller root。例如 t = {}; f(t) 的参数槽可交给 f，而 local owner; f(owner) 中
//! owner 的原始低槽不随参数 MOVE 一并交出。这里只发布同 basic block 的 direct def，
//! phi、跨 block use 和按引用捕获槽不产生证明；实际 producer 删除由 HIR 求值顺序 owner 审查。

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
    epochs: &SlotEpochFacts,
    fixed_temps: &[TempId],
) -> BTreeMap<TempId, TempId> {
    dataflow
        .defs
        .iter()
        .filter_map(|def| {
            let producer = TempId(def.id.index());
            if fixed_temps[def.id.index()] != producer
                || epochs.tracks_reference_capture(def.reg)
                || !matches!(proto.instrs[def.instr.index()], LowInstr::Call(_))
            {
                return None;
            }
            let end = dataflow.unobserved_root_overwrite_after_last_use(def.id, cfg)?;
            let endpoint = TempId(end.index());
            (fixed_temps[end.index()] == endpoint).then_some((producer, endpoint))
        })
        .collect()
}
