//! 核对共享读取返回体的完整纯程序和参数/结果寄存器映射。
//! 不推断实参如何准备；各调用帧另证当前树、SSA 输入与 home 生命周期。

use super::*;
use crate::hir::promotion::value_programs::{Operation, Predicate, Region};
use crate::transformer::Reg;

pub(in crate::hir::simplify::call_frames::native::expanded::calling_values) struct ReturnSlots {
    pub base: HomeSlotKey,
    pub flag: HomeSlotKey,
    pub value: HomeSlotKey,
    pub item: HomeSlotKey,
    pub selection: HomeSlotKey,
}

pub(in crate::hir::simplify::call_frames::native::expanded::calling_values) fn matches_return(
    program: &Region,
    slots: ReturnSlots,
    hit: &Literal,
    fallback: &Literal,
) -> bool {
    matches!(program.program.shape.as_slice(), [Operation::Copy,
        Operation::Branch { predicate: Predicate::Truthy, negated: true, operands: a, truthy: 12, falsy: 2 },
        Operation::Load(Literal::Boolean(false)),
        Operation::Branch { predicate: Predicate::Truthy, negated: true, operands: b, truthy: 6, falsy: 4 },
        Operation::Load(yes), Operation::Jump(7), Operation::Load(no),
        Operation::Branch { predicate: Predicate::Eq, negated: true, operands: c, truthy: 12, falsy: 8 },
        Operation::Branch { predicate: Predicate::Eq, negated: false, operands: d, truthy: 11, falsy: 9 },
        Operation::Load(Literal::Boolean(false)), Operation::Jump(12), Operation::Load(Literal::Boolean(true))]
        if a.as_slice() == [None] && b.as_slice() == [None] && c.as_slice() == [None, None] && d.as_slice() == [None, None]
            && yes == hit && no == fallback)
        && program.end.index() == program.source.index() + 12
        && program.program.registers.iter().map(Vec::as_slice).eq([
            &[Reg(slots.base.slot()), Reg(slots.flag.slot())] as &[Reg],
            &[Reg(slots.base.slot())],
            &[Reg(slots.base.slot())],
            &[Reg(slots.item.slot())],
            &[Reg(slots.selection.slot())],
            &[],
            &[Reg(slots.selection.slot())],
            &[Reg(slots.value.slot()), Reg(slots.selection.slot())],
            &[Reg(slots.item.slot()), Reg(slots.value.slot())],
            &[Reg(slots.base.slot())],
            &[],
            &[Reg(slots.base.slot())],
        ])
        && program.inputs.len() == 3
}
