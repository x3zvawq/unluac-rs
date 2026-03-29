//! 这个子模块负责把单一来源的 `DefId` 解释成可直接复用的 HIR 值表达式。
//!
//! 它依赖 Dataflow 已确认的 def/block/instr 身份，只在“一个 def 稳定对应一个值”时返回
//! 结果，不会越权为多来源 merge 伪造表达式。
//! 例如：单一 `NewTable` 定义会在这里直接变成空表构造器表达式。

use super::*;

pub(crate) fn is_multiret_results(results: crate::transformer::ResultPack) -> bool {
    matches!(results, crate::transformer::ResultPack::Open(_))
}

/// 尝试把一个固定定义直接解释成 HIR 表达式。
///
/// 这主要服务 merge 点上的值恢复。我们只在“一个 def 能稳定对应一个值表达式”时
/// 返回 `Some`，否则宁可交回上层继续保守退化，也不在这里伪造来源。
pub(crate) fn expr_for_fixed_def(lowering: &ProtoLowering<'_>, def_id: DefId) -> Option<HirExpr> {
    if let Some(expr) = expr_for_dup_safe_fixed_def(lowering, def_id) {
        return Some(expr);
    }

    let def_instr = lowering.dataflow.def_instr(def_id);
    let def_reg = lowering.dataflow.def_reg(def_id);
    let def_block = lowering.dataflow.def_block(def_id);
    let instr = lowering.proto.instrs.get(def_instr.index())?;

    match instr {
        LowInstr::GetTable(get_table) if get_table.dst == def_reg => {
            Some(lower_table_access_expr_inline(
                lowering,
                def_block,
                def_instr,
                get_table.base,
                get_table.key,
            ))
        }
        LowInstr::NewTable(new_table) if new_table.dst == def_reg => {
            Some(HirExpr::TableConstructor(Box::default()))
        }
        LowInstr::Call(call) => expr_for_fixed_call(lowering, def_block, def_instr, call, def_reg),
        LowInstr::VarArg(vararg) => expr_for_fixed_vararg(vararg.results, def_reg),
        LowInstr::Closure(closure) if closure.dst == def_reg => {
            Some(HirExpr::Closure(Box::new(HirClosureExpr {
                proto: lowering.child_refs[closure.proto.index()],
                captures: closure
                    .captures
                    .iter()
                    .map(|capture| HirCapture {
                        value: match capture.source {
                            crate::transformer::CaptureSource::Reg(reg) if reg == closure.dst => {
                                HirExpr::TempRef(lowering.bindings.fixed_temps[def_id.index()])
                            }
                            crate::transformer::CaptureSource::Reg(reg) => {
                                expr_for_reg_use_inline(lowering, def_block, def_instr, reg)
                            }
                            crate::transformer::CaptureSource::Upvalue(upvalue) => {
                                HirExpr::UpvalueRef(UpvalueId(upvalue.index()))
                            }
                        },
                    })
                    .collect(),
            })))
        }
        LowInstr::GenericForCall(for_call) => expr_for_generic_for_call(for_call.results, def_reg),
        LowInstr::SetUpvalue(_)
        | LowInstr::SetTable(_)
        | LowInstr::SetList(_)
        | LowInstr::TailCall(_)
        | LowInstr::Return(_)
        | LowInstr::Close(_)
        | LowInstr::NumericForInit(_)
        | LowInstr::NumericForLoop(_)
        | LowInstr::GenericForLoop(_)
        | LowInstr::Jump(_)
        | LowInstr::Branch(_) => None,
        _ => None,
    }
}

/// 这类定义可以安全地在表达式里重复展开，不会额外增加副作用，也不会改变
/// `newtable/closure/call` 这类“每次求值都不一样”的语义。
pub(crate) fn expr_for_dup_safe_fixed_def(
    lowering: &ProtoLowering<'_>,
    def_id: DefId,
) -> Option<HirExpr> {
    let def_instr = lowering.dataflow.def_instr(def_id);
    let def_reg = lowering.dataflow.def_reg(def_id);
    let def_block = lowering.dataflow.def_block(def_id);
    let instr = lowering.proto.instrs.get(def_instr.index())?;

    match instr {
        LowInstr::Move(move_instr) if move_instr.dst == def_reg => Some(expr_for_reg_use_inline(
            lowering,
            def_block,
            def_instr,
            move_instr.src,
        )),
        LowInstr::LoadNil(load_nil) if reg_in_range(load_nil.dst, def_reg) => Some(HirExpr::Nil),
        LowInstr::LoadBool(load_bool) if load_bool.dst == def_reg => {
            Some(HirExpr::Boolean(load_bool.value))
        }
        LowInstr::LoadConst(load_const) if load_const.dst == def_reg => {
            Some(expr_for_const(lowering.proto, load_const.value))
        }
        LowInstr::LoadInteger(load_integer) if load_integer.dst == def_reg => {
            Some(HirExpr::Integer(load_integer.value))
        }
        LowInstr::LoadNumber(load_number) if load_number.dst == def_reg => {
            Some(HirExpr::Number(load_number.value))
        }
        LowInstr::UnaryOp(unary) if unary.dst == def_reg => {
            Some(HirExpr::Unary(Box::new(HirUnaryExpr {
                op: lower_unary_op(unary.op),
                expr: expr_for_reg_use_inline(lowering, def_block, def_instr, unary.src),
            })))
        }
        LowInstr::BinaryOp(binary) if binary.dst == def_reg => {
            Some(HirExpr::Binary(Box::new(HirBinaryExpr {
                op: lower_binary_op(binary.op),
                lhs: expr_for_value_operand_inline(lowering, def_block, def_instr, binary.lhs),
                rhs: expr_for_value_operand_inline(lowering, def_block, def_instr, binary.rhs),
            })))
        }
        LowInstr::Concat(concat) if concat.dst == def_reg => {
            let value = (0..concat.src.len)
                .map(|offset| {
                    expr_for_reg_use_inline(
                        lowering,
                        def_block,
                        def_instr,
                        Reg(concat.src.start.index() + offset),
                    )
                })
                .reduce(|lhs, rhs| {
                    HirExpr::Binary(Box::new(HirBinaryExpr {
                        op: HirBinaryOpKind::Concat,
                        lhs,
                        rhs,
                    }))
                })
                .unwrap_or_else(|| unresolved_expr("concat empty source"));
            Some(value)
        }
        LowInstr::GetUpvalue(get_upvalue) if get_upvalue.dst == def_reg => {
            Some(HirExpr::UpvalueRef(UpvalueId(get_upvalue.src.index())))
        }
        _ => None,
    }
}

fn expr_for_fixed_call(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    call: &crate::transformer::CallInstr,
    reg: Reg,
) -> Option<HirExpr> {
    let ResultPack::Fixed(results) = call.results else {
        return None;
    };
    if results.len != 1 || results.start != reg {
        return None;
    }

    Some(HirExpr::Call(Box::new(HirCallExpr {
        callee: expr_for_reg_use_inline(lowering, block, instr_ref, call.callee),
        args: lower_value_pack_inline(lowering, block, instr_ref, call.args),
        multiret: false,
        method: matches!(call.kind, CallKind::Method),
    })))
}

fn expr_for_fixed_vararg(results: ResultPack, reg: Reg) -> Option<HirExpr> {
    let ResultPack::Fixed(range) = results else {
        return None;
    };
    if range.len == 1 && range.start == reg {
        Some(HirExpr::VarArg)
    } else {
        None
    }
}

fn expr_for_generic_for_call(results: ResultPack, reg: Reg) -> Option<HirExpr> {
    let ResultPack::Fixed(range) = results else {
        return None;
    };
    if range.len == 1 && range.start == reg {
        Some(unresolved_expr("generic-for-call"))
    } else {
        None
    }
}
