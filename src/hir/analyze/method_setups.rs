//! 消费 Dataflow 的方法配对查询，将 receiver 与 lookup 身份映射为 HIR 协议。
//!
//! 参数跨分支后，顺序 lowering 的 method 提示可能已失效；唯一 reaching-def、
//! 同一 receiver 首参和原 key 仍可证明配对。协议不授权删除准备值，完整帧消费者
//! 继续验证实际求值顺序、槽位与生命周期；TAILCALL 不签发返回后的旧 callee 根交接。

use super::lower::ProtoBindings;
use crate::hir::promotion::ProtoPromotionFacts;
use crate::parser::RawLiteralConst;
use crate::structure::{DataflowFacts, SsaValue};
use crate::transformer::{LowInstr, LoweredProto};

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
            let call_ref = crate::transformer::InstrRef(index);
            let setup = dataflow.method_setup_for_call(proto, call_ref)?;
            let callee_def = setup.callee_def;
            let get_ref = setup.lookup;
            let receiver = setup.receiver;
            let method_key = setup.key;
            let returns_to_frame = matches!(instr, LowInstr::Call(_));
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
                bindings.fixed_temps[callee_def.index()],
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
