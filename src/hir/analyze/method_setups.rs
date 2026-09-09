//! 从 low IR 与 SSA 认领 method setup producer/call 协议。
//!
//! `CallKind::Method` 只说明调用来自方言 method 协议；这里进一步把 callee 的唯一
//! `GetTableKind::Method` reaching-def、receiver 首参和 raw key 配成一个完整协议。最终
//! HIR 是否仍可删除 producer，由 simplify 在所有形状与生命周期改写收敛后另行证明。
//! callee 槽的旧值消费 Dataflow 的覆盖身份；这里只收紧同块协议边界，不重扫定义与 open 写。

use super::lower::ProtoBindings;
use crate::hir::promotion::ProtoPromotionFacts;
use crate::parser::RawLiteralConst;
use crate::structure::{DataflowFacts, SsaValue};
use crate::transformer::{AccessBase, AccessKey, CallKind, LowInstr, LoweredProto, ValuePack};

pub(super) fn record_method_setup_protocols(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    bindings: &ProtoBindings,
    facts: &mut ProtoPromotionFacts,
) {
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
            let [result_def] = dataflow.instr_defs.get(get_ref.index())?.as_slice() else {
                return None;
            };
            let SsaValue::Def(prior_callee_def) = dataflow.def_overwritten_value(callee_def)?
            else {
                return None;
            };
            if dataflow.def_block(prior_callee_def) != dataflow.def_block(callee_def)
                || dataflow.def_instr(prior_callee_def).index() >= get_ref.index()
            {
                return None;
            }
            let SsaValue::Def(prior_callee_root) =
                dataflow.canonical_move_value(SsaValue::Def(prior_callee_def))?
            else {
                return None;
            };
            let prior_callee_root_temp = crate::hir::TempId(prior_callee_root.index());
            if bindings.fixed_temps.get(prior_callee_root.index()) != Some(&prior_callee_root_temp)
            {
                return None;
            }
            let RawLiteralConst::String(raw_key) = proto.constants.get(method_key.index())? else {
                return None;
            };
            Some((
                call_ref,
                get_ref,
                bindings.fixed_temps[result_def.index()],
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
