//! 从原 SELF/NAMECALL 与 SSA 认领方法准备及调用的配对协议。
//!
//! 参数跨分支后，顺序 lowering 的 method 提示可能已失效；唯一 reaching-def、
//! 同一 receiver 首参和原 key 仍可证明配对。协议不授权删除准备值，完整帧消费者
//! 继续验证实际求值顺序、槽位与生命周期；TAILCALL 不签发返回后的旧 callee 根交接。

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
            let (callee, args, kind, method_name, returns_to_frame) = match instr {
                LowInstr::Call(call) => (call.callee, call.args, call.kind, call.method_name, true),
                LowInstr::TailCall(call) => {
                    (call.callee, call.args, call.kind, call.method_name, false)
                }
                _ => return None,
            };
            if matches!(kind, CallKind::FastCall(_)) {
                return None;
            }
            let call_ref = crate::transformer::InstrRef(index);
            let SsaValue::Def(callee_def) = dataflow.use_value(call_ref, callee) else {
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
            let first_arg = match args {
                ValuePack::Fixed(range) if range.len > 0 => range.start,
                ValuePack::Open(start) => start,
                ValuePack::Fixed(_) => return None,
            };
            if get.kind != crate::transformer::GetTableKind::Method
                || get.dst != callee
                || method_name.is_some_and(|hint| hint.const_ref != method_key)
                || dataflow.use_value(get_ref, receiver) != dataflow.use_value(call_ref, first_arg)
                || dataflow
                    .def_phi_uses
                    .get(callee_def.index())
                    .is_none_or(|uses| !uses.is_empty())
                || !matches!(
                    dataflow.def_uses.get(callee_def.index()).map(Vec::as_slice),
                    Some([site]) if site.instr == call_ref && site.reg == callee
                )
            {
                return None;
            }
            let [result_def] = dataflow.instr_defs.get(get_ref.index())?.as_slice() else {
                return None;
            };
            // setup/call 配对与旧 callee 根是独立事实。首次使用入口 nil 槽时没有旧根，
            // 但仍必须保留完整 method 协议，不能迫使后层重新猜 SELF。
            let prior_callee_root_temp = (|| {
                // TAILCALL 仍拥有 setup 双端身份，但没有返回当前帧后的 callee 根接管。
                if !returns_to_frame {
                    return None;
                }
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
                let temp = crate::hir::TempId(prior_callee_root.index());
                (bindings.fixed_temps.get(prior_callee_root.index()) == Some(&temp)).then_some(temp)
            })();
            let RawLiteralConst::String(raw_key) = proto.constants.get(method_key.index())? else {
                return None;
            };
            // SELF 的参数 COPY 可在提升前消失；保留原 receiver 的 SSA 值来源，
            // 后层不能把已退休的 COPY Def 当成 receiver local 的 producer。
            let receiver_temp =
                match dataflow.canonical_move_value(dataflow.use_value(get_ref, receiver)) {
                    Some(SsaValue::Def(def)) => bindings.fixed_temps.get(def.index()).copied(),
                    _ => None,
                };
            Some((
                call_ref,
                get_ref,
                bindings.fixed_temps[result_def.index()],
                receiver_temp,
                prior_callee_root_temp,
                crate::LuaString::from_raw(raw_key),
            ))
        })
        .for_each(
            |(
                call_ref,
                get_ref,
                callee_temp,
                receiver_temp,
                prior_callee_root_temp,
                method_key,
            )| {
                facts.record_method_setup_protocol(
                    call_ref,
                    get_ref,
                    callee_temp,
                    receiver_temp,
                    prior_callee_root_temp,
                    method_key,
                );
            },
        );
}
