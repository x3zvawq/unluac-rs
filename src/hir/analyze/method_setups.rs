//! 从 low IR 与 SSA 认领 method setup producer/call 协议。
//!
//! `CallKind::Method` 只说明调用来自方言 method 协议；这里进一步把 callee 的唯一
//! `GetTableKind::Method` reaching-def、receiver 首参和 raw key 配成一个完整协议。最终
//! HIR 是否仍可删除 producer，由 simplify 在所有形状与生命周期改写收敛后另行证明。

use super::lower::ProtoBindings;
use crate::hir::promotion::ProtoPromotionFacts;
use crate::parser::RawLiteralConst;
use crate::structure::{CanonicalMoveIndex, DataflowFacts, SsaValue};
use crate::transformer::{AccessBase, AccessKey, CallKind, LowInstr, LoweredProto, ValuePack};

pub(super) fn record_method_setup_protocols(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    bindings: &ProtoBindings,
    facts: &mut ProtoPromotionFacts,
) {
    let mut canonical_moves = CanonicalMoveIndex::new(proto, dataflow);
    proto
        .instrs
        .iter()
        .enumerate()
        .filter_map(|(index, instr)| {
            let LowInstr::Call(call) = instr else {
                return None;
            };
            if call.kind != CallKind::Method {
                return None;
            }
            let call_ref = crate::transformer::InstrRef(index);
            let SsaValue::Def(callee_def) = dataflow.use_value(call_ref, call.callee) else {
                return None;
            };
            let get_ref = dataflow.def_instr(callee_def);
            let LowInstr::GetTable(get) = proto.instrs.get(get_ref.index())? else {
                return None;
            };
            let AccessBase::Reg(receiver) = get.base else {
                return None;
            };
            let AccessKey::Const(method_key) = get.key else {
                return None;
            };
            let first_arg = match call.args {
                ValuePack::Fixed(range) if range.len > 0 => range.start,
                ValuePack::Open(start) => start,
                ValuePack::Fixed(_) => return None,
            };
            if get.kind != crate::transformer::GetTableKind::Method
                || get.dst != call.callee
                || call.method_name?.const_ref != method_key
                || dataflow.use_value(get_ref, receiver) != dataflow.use_value(call_ref, first_arg)
                || dataflow
                    .def_phi_uses
                    .get(callee_def.index())
                    .is_none_or(|uses| !uses.is_empty())
                || !matches!(
                    dataflow.def_uses.get(callee_def.index()).map(Vec::as_slice),
                    Some([site]) if site.instr == call_ref && site.reg == call.callee
                )
            {
                return None;
            }
            let [callee_temp] = bindings.instr_fixed_defs.get(get_ref.index())?.as_slice() else {
                return None;
            };
            let get_block = dataflow.def_block(callee_def);
            let prior_callee_def = dataflow
                .defs
                .iter()
                .filter(|def| {
                    def.block == get_block
                        && def.reg == get.dst
                        && def.instr.index() < get_ref.index()
                })
                .max_by_key(|def| def.instr.index())?;
            if dataflow
                .instr_effects
                .get(prior_callee_def.instr.index().checked_add(1)?..get_ref.index())?
                .iter()
                .any(|effect| effect.must_define(get.dst))
            {
                return None;
            }
            let SsaValue::Def(prior_callee_root) = canonical_moves
                .resolve(SsaValue::Def(prior_callee_def.id))
                .ok()?
            else {
                return None;
            };
            let prior_callee_root_temp = crate::hir::TempId(prior_callee_root.index());
            if bindings.fixed_temps.get(prior_callee_root.index()) != Some(&prior_callee_root_temp)
            {
                return None;
            }
            let RawLiteralConst::String(raw_key) =
                proto.constants.common.literals.get(method_key.index())?
            else {
                return None;
            };
            Some((
                call_ref,
                get_ref,
                *callee_temp,
                prior_callee_root_temp,
                crate::LuaString::from_raw(raw_key),
            ))
        })
        .for_each(
            |(call_ref, get_ref, callee_temp, prior_callee_root_temp, method_key)| {
                facts.record_method_setup_protocol(
                    call_ref,
                    get_ref,
                    callee_temp,
                    prior_callee_root_temp,
                    method_key,
                );
            },
        );
}
