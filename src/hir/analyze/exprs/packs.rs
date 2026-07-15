//! 把 Transformer 的 fixed/open value pack 降成显式 HIR value pack。
//!
//! normal 与 single-eval 只在寄存器表达式和 open owner 的解析策略上不同；pack 边界、
//! fixed prefix 和 unresolved fail-fast 共享同一条 lowering，避免两套实现漂移。

use super::*;

pub(crate) fn lower_value_pack(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    pack: crate::transformer::ValuePack,
) -> crate::hir::common::HirValuePack {
    lower_value_pack_with(
        pack,
        |reg| expr_for_reg_use(lowering, block, instr_ref, reg),
        |start| resolve_open_pack_tail(lowering, instr_ref, start),
        instr_ref,
    )
}

pub(crate) fn lower_value_pack_single_eval(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    pack: crate::transformer::ValuePack,
) -> crate::hir::common::HirValuePack {
    lower_value_pack_with(
        pack,
        |reg| expr_for_reg_use_single_eval_with_call_policy(lowering, block, instr_ref, reg, false),
        |start| resolve_open_pack_tail_single_eval(lowering, instr_ref, start),
        instr_ref,
    )
}

fn lower_value_pack_with(
    pack: crate::transformer::ValuePack,
    mut lower_reg: impl FnMut(Reg) -> HirExpr,
    resolve_tail: impl FnOnce(Reg) -> Option<(Reg, crate::hir::common::HirPackTail)>,
    instr_ref: InstrRef,
) -> crate::hir::common::HirValuePack {
    let (start, end, tail) = match pack {
        crate::transformer::ValuePack::Fixed(range) => {
            (range.start.index(), range.start.index() + range.len, None)
        }
        crate::transformer::ValuePack::Open(start) => {
            let Some((tail_start, tail)) = resolve_tail(start) else {
                return vec![unresolved_expr(format!(
                    "open-pack r{} @{}",
                    start.index(),
                    instr_ref.index()
                ))]
                .into();
            };
            (start.index(), tail_start.index(), Some(tail))
        }
    };

    let fixed = (start..end).map(|index| lower_reg(Reg(index))).collect();
    match tail {
        Some(tail) => crate::hir::common::HirValuePack::expanding(fixed, tail),
        None => crate::hir::common::HirValuePack::fixed(fixed),
    }
}
