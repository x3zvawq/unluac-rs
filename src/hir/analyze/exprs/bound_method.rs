//! 识别 `local f = obj.method; f(obj, ...)` 这类显式表索引 + CALL 的 bound method 调用，
//! 并回收成 `obj:method(...)` 的 HIR method 糖。Lua 5.1 里 `obj:Lookup(x)` 与
//! `obj.Lookup(obj, x)` 都会编译成 GETTABLE + CALL，而不一定走 NAMECALL。

use super::*;

pub(in crate::hir::analyze) fn try_recover_bound_method_call(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    call: &crate::transformer::CallInstr,
) -> Option<HirCallExpr> {
    if matches!(call.kind, CallKind::Method) || call.method_name.is_some() {
        return None;
    }

    let callee_reg = call.callee;
    let def_id = single_reaching_def(lowering, instr_ref, callee_reg)?;
    let def_instr_ref = lowering.dataflow.def_instr(def_id);
    if lowering.dataflow.def_reg(def_id) != callee_reg {
        return None;
    }

    let LowInstr::GetTable(get_table) = lowering.proto.instrs.get(def_instr_ref.index())?
    else {
        return None;
    };
    if get_table.dst != callee_reg {
        return None;
    }

    let AccessBase::Reg(base_reg) = get_table.base else {
        return None;
    };
    let method_name = method_name_from_access_key(lowering.proto, get_table.key)?;

    let first_arg_reg = first_arg_reg_from_pack(call.args)?;
    if !receiver_reg_matches_base(
        lowering,
        block,
        instr_ref,
        first_arg_reg,
        base_reg,
    ) {
        return None;
    }

    Some(HirCallExpr {
        callee: HirExpr::Nil,
        args: lower_value_pack(lowering, block, instr_ref, call.args),
        multiret: is_multiret_results(call.results),
        method: true,
        method_name: Some(method_name),
    })
}

fn single_reaching_def(
    lowering: &ProtoLowering<'_>,
    instr_ref: InstrRef,
    reg: Reg,
) -> Option<DefId> {
    let values = lowering.dataflow.use_values_at(instr_ref).get(reg)?;
    let mut defs = values.iter().filter_map(|value| match value {
        SsaValue::Def(def) => Some(def),
        SsaValue::Phi(_) => None,
    });
    let def = defs.next()?;
    if defs.next().is_some() {
        return None;
    }
    Some(def)
}

fn first_arg_reg_from_pack(pack: crate::transformer::ValuePack) -> Option<Reg> {
    match pack {
        crate::transformer::ValuePack::Fixed(range) if range.len >= 1 => Some(range.start),
        crate::transformer::ValuePack::Open(reg) => Some(reg),
        _ => None,
    }
}

fn method_name_from_access_key(proto: &LoweredProto, key: AccessKey) -> Option<String> {
    let AccessKey::Const(const_ref) = key else {
        return None;
    };
    match proto.constants.common.literals.get(const_ref.index()) {
        Some(RawLiteralConst::String(value)) => Some(decode_raw_string(value)),
        _ => None,
    }
}

fn receiver_reg_matches_base(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    receiver_reg: Reg,
    base_reg: Reg,
) -> bool {
    if receiver_reg == base_reg {
        return true;
    }

    let Some(def_id) = single_reaching_def(lowering, instr_ref, receiver_reg) else {
        return false;
    };
    let def_instr_ref = lowering.dataflow.def_instr(def_id);
    if lowering.dataflow.def_block(def_id) != block {
        return false;
    }
    if def_instr_ref.index() >= instr_ref.index() {
        return false;
    }

    match lowering.proto.instrs.get(def_instr_ref.index()) {
        Some(LowInstr::Move(mv)) if mv.dst == receiver_reg && mv.src == base_reg => true,
        _ => false,
    }
}
