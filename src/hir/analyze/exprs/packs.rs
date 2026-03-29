//! 这个子模块负责把 fixed/open value pack 降成 HIR 多值表达式序列。
//!
//! 它依赖 Transformer 已经区分好的 `ValuePack` / `ResultPack`，以及 Dataflow 对开放尾值
//! 的事实，不会在这里猜补 pack 边界。
//! 例如：`call(...)` 的开放返回包会在这里变成 `[..., tail_expr]` 这种 HIR 值序列。

use super::*;

fn lower_open_value_pack<F>(
    lowering: &ProtoLowering<'_>,
    start_reg: Reg,
    instr_ref: InstrRef,
    mut lower_reg: F,
) -> Vec<HirExpr>
where
    F: FnMut(Reg) -> HirExpr,
{
    let Some((tail_start, tail_expr)) = resolve_open_pack_tail(lowering, instr_ref, start_reg)
    else {
        return vec![unresolved_expr(format!(
            "open-pack r{} @{}",
            start_reg.index(),
            instr_ref.index()
        ))];
    };

    let mut values = (start_reg.index()..tail_start.index())
        .map(|index| lower_reg(Reg(index)))
        .collect::<Vec<_>>();
    values.push(tail_expr);
    values
}

pub(crate) fn lower_value_pack(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    pack: crate::transformer::ValuePack,
) -> Vec<HirExpr> {
    let (mut values, trailing_multivalue) =
        lower_value_pack_components(lowering, block, instr_ref, pack);
    if let Some(trailing) = trailing_multivalue {
        values.push(trailing);
    }
    values
}

pub(crate) fn lower_value_pack_components(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    pack: crate::transformer::ValuePack,
) -> (Vec<HirExpr>, Option<HirExpr>) {
    match pack {
        crate::transformer::ValuePack::Fixed(range) => (
            (0..range.len)
                .map(|offset| {
                    expr_for_reg_use(
                        lowering,
                        block,
                        instr_ref,
                        Reg(range.start.index() + offset),
                    )
                })
                .collect(),
            None,
        ),
        crate::transformer::ValuePack::Open(reg) => {
            lower_open_value_pack_components(lowering, reg, instr_ref, |reg| {
                expr_for_reg_use(lowering, block, instr_ref, reg)
            })
        }
    }
}

pub(crate) fn lower_value_pack_inline(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    pack: crate::transformer::ValuePack,
) -> Vec<HirExpr> {
    match pack {
        crate::transformer::ValuePack::Fixed(range) => (0..range.len)
            .map(|offset| {
                expr_for_reg_use_inline(
                    lowering,
                    block,
                    instr_ref,
                    Reg(range.start.index() + offset),
                )
            })
            .collect(),
        crate::transformer::ValuePack::Open(reg) => {
            lower_open_value_pack(lowering, reg, instr_ref, |reg| {
                expr_for_reg_use_inline(lowering, block, instr_ref, reg)
            })
        }
    }
}

fn lower_open_value_pack_components<F>(
    lowering: &ProtoLowering<'_>,
    start_reg: Reg,
    instr_ref: InstrRef,
    mut lower_reg: F,
) -> (Vec<HirExpr>, Option<HirExpr>)
where
    F: FnMut(Reg) -> HirExpr,
{
    let Some((tail_start, tail_expr)) = resolve_open_pack_tail(lowering, instr_ref, start_reg)
    else {
        return (
            vec![unresolved_expr(format!(
                "open-pack r{} @{}",
                start_reg.index(),
                instr_ref.index()
            ))],
            None,
        );
    };

    let values = (start_reg.index()..tail_start.index())
        .map(|index| lower_reg(Reg(index)))
        .collect::<Vec<_>>();
    (values, Some(tail_expr))
}
