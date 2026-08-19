//! 提取并校验 generic-for header/prep/source 指令协议；依赖 lowered 指令与 terminator，不负责通用循环值分析；例如匹配 TFORCALL/TFORLOOP 组合。

use super::*;

pub(super) fn generic_for_header_instrs(
    proto: &LoweredProto,
    terminator: &crate::structure::BlockTerminatorPlan,
) -> Option<(InstrRef, GenericForCallInstr, GenericForLoopInstr)> {
    let BlockTerminatorKind::GenericForLoop {
        instr: loop_instr_ref,
        ..
    } = terminator.kind
    else {
        return None;
    };
    let call_index = loop_instr_ref.index().checked_sub(1)?;
    if call_index < terminator.instrs.start.index() {
        return None;
    }
    let call_instr_ref = InstrRef(call_index);
    let LowInstr::GenericForCall(call) = proto.instrs.get(call_instr_ref.index())? else {
        return None;
    };
    let LowInstr::GenericForLoop(loop_instr) = proto.instrs.get(loop_instr_ref.index())? else {
        return None;
    };
    if call.results != crate::transformer::ResultPack::Fixed(loop_instr.bindings) {
        return None;
    }
    Some((call_instr_ref, *call, *loop_instr))
}

pub(super) fn generic_for_source(
    proto: &LoweredProto,
    preheader: BlockRef,
    terminator: &crate::structure::BlockTerminatorPlan,
    call: GenericForCallInstr,
) -> Result<(Option<InstrRef>, RegRange), StructureError> {
    let prep_instr_ref = match terminator.kind {
        BlockTerminatorKind::Jump { instr, .. }
            if instr.index() > terminator.instrs.start.index() =>
        {
            Some(InstrRef(instr.index() - 1))
        }
        _ => None,
    };
    let Some((prep_instr_ref, prep)) =
        prep_instr_ref.and_then(|instr_ref| match proto.instrs.get(instr_ref.index())? {
            LowInstr::GenericForPrep(prep) => Some((instr_ref, *prep)),
            _ => None,
        })
    else {
        if call.state != Reg(call.iterator.index() + 1)
            || call.control != Reg(call.iterator.index() + 2)
        {
            return Err(StructureError::invalid(format!(
                "generic-for preheader {preheader} has no stable iterator triple",
            )));
        }
        return Ok((None, crate::transformer::RegRange::new(call.iterator, 3)));
    };
    validate_generic_prep(prep, call)?;
    Ok((
        Some(prep_instr_ref),
        crate::transformer::RegRange::new(prep.iterator, 4),
    ))
}

pub(super) fn validate_generic_prep(
    prep: GenericForPrepInstr,
    call: GenericForCallInstr,
) -> Result<(), StructureError> {
    if prep.iterator != call.iterator
        || prep.state != call.state
        || prep.state != Reg(prep.iterator.index() + 1)
        || prep.control_source != Reg(prep.iterator.index() + 2)
        || prep.closing_source != Reg(prep.iterator.index() + 3)
        || prep.control_target != call.control
    {
        return Err(StructureError::invalid(
            "generic-for prep/call contract changed after planning",
        ));
    }
    Ok(())
}
