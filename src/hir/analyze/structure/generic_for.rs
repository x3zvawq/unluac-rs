//! Generic-for iterator 表达式恢复。
//!
//! StructurePlan 已经冻结了 `prep/call/loop` identity 与 iterator 源寄存器区间；
//! 这里只把这些稳定输入翻译成 HIR 表达式，不再重新识别 VM 协议。

use std::collections::BTreeSet;

use crate::hir::common::{
    HirExpr, HirGenericForDispatchResult, HirGenericForInitializerProducerId,
    HirGenericForInitializerSpan, HirGenericForInitializerTransaction,
    HirGenericForInitializerTransactionId, HirLValue, HirProtoRef, HirStmt, LocalId, TempId,
};
use crate::structure::{BlockRef, SsaValue};
use crate::transformer::{InstrRef, LowInstr, Reg, ResultPack, ValuePack};

use super::super::exprs::{expr_for_reg_at_block_exit, expr_for_reg_use};
use super::super::lower::ProtoLowering;

pub(super) fn lower_generic_for_dispatch_results(
    lowering: &ProtoLowering<'_>,
    protocol: crate::structure::GenericForProtocol,
    bindings: &[LocalId],
) -> Option<Vec<HirGenericForDispatchResult>> {
    if bindings.len() != protocol.bindings.len {
        return None;
    }
    (0..protocol.bindings.len)
        .map(|offset| {
            let reg = Reg(protocol.bindings.start.index() + offset);
            let def = lowering
                .dataflow
                .instr_def_for_reg(protocol.call_instr, reg)?;
            Some(HirGenericForDispatchResult {
                result_def: TempId(def.index()),
                success_binding: bindings[offset],
            })
        })
        .collect()
}

struct ExactInitializerProducer {
    instr: InstrRef,
    protocol_start: usize,
    outputs: Vec<HirLValue>,
}

/// 从 frozen iterator reaching defs 一次发布 initializer producer ownership 与 call operand
/// roots。前者覆盖所有仍以 direct temp assignment 物化的 producer；后者只消费 ordinary
/// call 的真实 MOVE provenance。任一 side 都不把 SSA/寄存器 identity 泄漏给 HIR consumer。
pub(super) fn lower_generic_for_initializer_facts(
    lowering: &ProtoLowering<'_>,
    preheader: BlockRef,
    protocol: crate::structure::GenericForProtocol,
    proto: HirProtoRef,
    ordinal: usize,
    stmts: &mut [HirStmt],
) -> (Option<HirGenericForInitializerTransaction>, Vec<TempId>) {
    let producers = exact_initializer_producers(lowering, preheader, protocol);
    let mut roots = BTreeSet::new();
    for producer in &producers {
        let Some(LowInstr::Call(call)) = lowering.proto.instrs.get(producer.instr.index()) else {
            continue;
        };
        let ResultPack::Fixed(results) = call.results else {
            continue;
        };
        if results.start.index() != protocol.iterator.start.index() + producer.protocol_start
            || results.len != producer.outputs.len()
        {
            continue;
        }
        let mut producer_roots = BTreeSet::new();
        let mut visited_calls = BTreeSet::new();
        if collect_initializer_call_roots(
            lowering,
            producer.instr,
            &mut visited_calls,
            &mut producer_roots,
        ) {
            roots.extend(producer_roots);
        }
    }
    let transaction = stamp_initializer_transaction(proto, ordinal, stmts, &producers, protocol);
    (transaction, roots.into_iter().collect())
}

fn stamp_initializer_transaction(
    proto: HirProtoRef,
    ordinal: usize,
    stmts: &mut [HirStmt],
    producers: &[ExactInitializerProducer],
    protocol: crate::structure::GenericForProtocol,
) -> Option<HirGenericForInitializerTransaction> {
    if producers.is_empty() {
        return None;
    }
    let transaction = HirGenericForInitializerTransactionId::new(proto, ordinal);
    let mut spans = Vec::with_capacity(producers.len());
    let mut stamped = Vec::with_capacity(producers.len());
    for (producer_ordinal, producer) in producers.iter().enumerate() {
        let producer_id = HirGenericForInitializerProducerId::new(transaction, producer_ordinal);
        let matches = stmts
            .iter()
            .enumerate()
            .filter_map(|(index, stmt)| {
                let HirStmt::Assign(assign) = stmt else {
                    return None;
                };
                (assign.generic_for_initializer_producer.is_none()
                    && assign.targets.len() == producer.outputs.len()
                    && assign
                        .targets
                        .iter()
                        .zip(&producer.outputs)
                        .all(|(target, output)| target == output))
                .then_some(index)
            })
            .collect::<Vec<_>>();
        let [index] = matches.as_slice() else {
            clear_stamped_initializer_producers(stmts, &stamped);
            return None;
        };
        let HirStmt::Assign(assign) = &mut stmts[*index] else {
            unreachable!("matched generic-for initializer producer must remain an assignment");
        };
        assign.generic_for_initializer_producer = Some(producer_id);
        stamped.push(*index);
        spans.push(HirGenericForInitializerSpan {
            producer: producer_id,
            value_start: producer.protocol_start,
            value_count: producer.outputs.len(),
        });
    }
    Some(HirGenericForInitializerTransaction {
        id: transaction,
        iterator_width: protocol.iterator.len,
        producers: spans,
    })
}

fn clear_stamped_initializer_producers(stmts: &mut [HirStmt], stamped: &[usize]) {
    for &index in stamped {
        let HirStmt::Assign(assign) = &mut stmts[index] else {
            continue;
        };
        assign.generic_for_initializer_producer = None;
    }
}

fn exact_initializer_producers(
    lowering: &ProtoLowering<'_>,
    preheader: BlockRef,
    protocol: crate::structure::GenericForProtocol,
) -> Vec<ExactInitializerProducer> {
    let mut candidates = BTreeSet::new();
    for offset in 0..protocol.iterator.len {
        let reg = Reg(protocol.iterator.start.index() + offset);
        let SsaValue::Def(def) = generic_for_initializer_value(lowering, preheader, protocol, reg)
        else {
            continue;
        };
        let owner = lowering.dataflow.def_instr(def);
        if lowering.dataflow.instr_def_for_reg(owner, reg) == Some(def) {
            candidates.insert(owner);
        }
    }
    candidates
        .into_iter()
        .filter_map(|instr| exact_initializer_producer(lowering, preheader, protocol, instr))
        .collect()
}

fn exact_initializer_producer(
    lowering: &ProtoLowering<'_>,
    preheader: BlockRef,
    protocol: crate::structure::GenericForProtocol,
    instr: InstrRef,
) -> Option<ExactInitializerProducer> {
    let defs = lowering.dataflow.instr_defs.get(instr.index())?;
    if defs.is_empty() {
        return None;
    }
    let protocol_start = protocol.iterator.start.index();
    let protocol_end = protocol_start + protocol.iterator.len;
    let first_def = *defs.first()?;
    let first_reg = lowering.dataflow.def_reg(first_def).index();
    let producer_end = first_reg.checked_add(defs.len())?;
    if first_reg < protocol_start || producer_end > protocol_end {
        return None;
    }
    if lowering.dataflow.def_block(first_def) != preheader
        || instr.index() >= protocol.prep_instr.unwrap_or(protocol.call_instr).index()
    {
        return None;
    }
    let mut outputs = Vec::with_capacity(defs.len());
    for (offset, &def) in defs.iter().enumerate() {
        let temp = lowering.bindings.fixed_temps[def.index()];
        let reg = Reg(first_reg + offset);
        let target = lowering
            .bindings
            .lvalue_for_reg_result(preheader, reg, temp);
        let value = lowering.bindings.expr_for_fixed_def(preheader, reg, temp);
        // 未来同槽捕获可使某个控制结果提前成为 Local；仍按原 Def 和当前
        // 读写绑定签发 occurrence，不能因混合 Temp/Local 丢掉整组协议。
        let matches = match (&target, &value) {
            (HirLValue::Temp(target), HirExpr::TempRef(value)) => {
                target == value && *target == temp
            }
            (HirLValue::Local(target), HirExpr::LocalRef(value)) => {
                target == value && !lowering.dataflow.reference_capture_may_be_open(reg, instr)
            }
            _ => false,
        };
        if lowering.dataflow.def_reg(def) != reg
            || lowering.dataflow.instr_def_for_reg(instr, reg) != Some(def)
            || generic_for_initializer_value(lowering, preheader, protocol, reg)
                != SsaValue::Def(def)
            || !matches
        {
            return None;
        }
        outputs.push(target);
    }
    Some(ExactInitializerProducer {
        instr,
        protocol_start: first_reg - protocol_start,
        outputs,
    })
}

fn generic_for_initializer_value(
    lowering: &ProtoLowering<'_>,
    preheader: BlockRef,
    protocol: crate::structure::GenericForProtocol,
    reg: Reg,
) -> SsaValue {
    protocol.prep_instr.map_or_else(
        || lowering.dataflow.block_exit_value(preheader, reg),
        |prep| lowering.dataflow.use_value(prep, reg),
    )
}

fn collect_initializer_call_roots(
    lowering: &ProtoLowering<'_>,
    call_instr: InstrRef,
    visited_calls: &mut BTreeSet<InstrRef>,
    roots: &mut BTreeSet<TempId>,
) -> bool {
    if !visited_calls.insert(call_instr) {
        return false;
    }
    let Some(LowInstr::Call(call)) = lowering.proto.instrs.get(call_instr.index()) else {
        return false;
    };
    for value in lowering.dataflow.use_values_at(call_instr).values() {
        if let Some(root) = scope_end_root_on_move_chain(lowering, value) {
            roots.insert(root);
        }
    }
    let ValuePack::Open(_) = call.args else {
        return true;
    };
    let sources = lowering.dataflow.open_use_sources_at(call_instr);
    if sources.has_entry() || sources.defs().len() != 1 {
        return false;
    }
    let Some(open_def_id) = sources.defs().iter().next().copied() else {
        return false;
    };
    let Some(open_def) = lowering.dataflow.open_defs.get(open_def_id.index()) else {
        return false;
    };
    if !lowering.owns_open_pack(open_def_id, call_instr) {
        return false;
    }
    match lowering.proto.instrs.get(open_def.instr.index()) {
        Some(LowInstr::Call(_)) => {
            collect_initializer_call_roots(lowering, open_def.instr, visited_calls, roots)
        }
        Some(LowInstr::VarArg(_)) => true,
        _ => false,
    }
}

fn scope_end_root_on_move_chain(
    lowering: &ProtoLowering<'_>,
    mut value: SsaValue,
) -> Option<TempId> {
    let mut seen = BTreeSet::new();
    loop {
        let SsaValue::Def(def) = value else {
            return None;
        };
        let direct = TempId(def.index());
        if !seen.insert(direct) {
            return None;
        }
        if lowering.bindings.fixed_temps.get(def.index()) == Some(&direct)
            && lowering.promotion_facts.is_scope_end_copy_root_temp(direct)
            && lowering.bindings.expr_for_temp(direct) == HirExpr::TempRef(direct)
        {
            return Some(direct);
        }
        let instr = lowering.dataflow.def_instr(def);
        let Some(LowInstr::Move(move_)) = lowering.proto.instrs.get(instr.index()) else {
            return None;
        };
        if move_.dst != lowering.dataflow.def_reg(def) {
            return None;
        }
        value = lowering.dataflow.use_value(instr, move_.src);
    }
}

pub(super) fn lower_generic_for_iterator(
    lowering: &ProtoLowering<'_>,
    preheader: BlockRef,
    protocol: crate::structure::GenericForProtocol,
) -> Vec<HirExpr> {
    (0..protocol.iterator.len)
        .map(|offset| {
            let reg = Reg(protocol.iterator.start.index() + offset);
            // 无 prep 的方言必须读取 preheader 出口；header 上的 control 已是
            // loop-carried phi。5.4/5.5 则读取 prep 的交换前 use，保留第 4 项 closing。
            protocol.prep_instr.map_or_else(
                || expr_for_reg_at_block_exit(lowering, preheader, reg),
                |instr_ref| expr_for_reg_use(lowering, preheader, instr_ref, reg),
            )
        })
        .collect()
}
