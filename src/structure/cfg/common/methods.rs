//! 以原 method setup 身份和 SSA 唯一读取证明 receiver、lookup 与调用的配对。
//! 查询只认领协议端点；求值顺序、物理 home 与生命周期仍由完整帧消费者证明。

use super::{DataflowFacts, DefId, SsaValue};
use crate::parser::RawLiteralConst;
use crate::transformer::{
    AccessBase, AccessKey, CallKind, ConstRef, GetTableKind, InstrRef, LowInstr, LoweredProto, Reg,
    ValuePack,
};

pub(crate) struct MethodSetup {
    pub(crate) callee_def: DefId,
    pub(crate) lookup: InstrRef,
    pub(crate) receiver: Reg,
    pub(crate) first_arg: Reg,
    pub(crate) key: ConstRef,
}

impl DataflowFacts {
    /// 只对当前 proto/SSA 快照有效，不授权移除 lookup 或跨参数副作用移动 receiver。
    pub(crate) fn method_setup_for_call(
        &self,
        proto: &LoweredProto,
        call_ref: InstrRef,
    ) -> Option<MethodSetup> {
        let (callee, args, kind, method_name) = match proto.instrs.get(call_ref.index())? {
            LowInstr::Call(call) => (call.callee, call.args, call.kind, call.method_name),
            LowInstr::TailCall(call) => (call.callee, call.args, call.kind, call.method_name),
            _ => return None,
        };
        if matches!(kind, CallKind::FastCall(_)) {
            return None;
        }
        let SsaValue::Def(callee_def) = self.use_value(call_ref, callee) else {
            return None;
        };
        let lookup = self.def_instr(callee_def);
        let LowInstr::GetTable(get) = proto.instrs.get(lookup.index())? else {
            return None;
        };
        let (AccessBase::Reg(receiver), AccessKey::Const(key)) = (get.base, get.key) else {
            return None;
        };
        let first_arg = match args {
            ValuePack::Fixed(range) if range.len > 0 => range.start,
            ValuePack::Open(start) => start,
            ValuePack::Fixed(_) => return None,
        };
        if get.kind != GetTableKind::Method
            || get.dst != callee
            || method_name.is_some_and(|hint| hint.const_ref != key)
            || self.use_value(lookup, receiver) != self.use_value(call_ref, first_arg)
            || !self.def_phi_uses.get(callee_def.index())?.is_empty()
            || !matches!(self.def_uses.get(callee_def.index())?.as_slice(),
                [site] if site.instr == call_ref && site.reg == callee)
            || self.instr_defs.get(lookup.index())?.as_slice() != [callee_def]
            || !matches!(
                proto.constants.get(key.index())?,
                RawLiteralConst::String(_)
            )
        {
            return None;
        }
        Some(MethodSetup {
            callee_def,
            lookup,
            receiver,
            first_arg,
            key,
        })
    }
}
