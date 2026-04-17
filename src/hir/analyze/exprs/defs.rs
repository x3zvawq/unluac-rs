//! 这个子模块负责把单一来源的 `DefId` 解释成可直接复用的 HIR 值表达式。
//!
//! 它依赖 Dataflow 已确认的 def/block/instr 身份，只在“一个 def 稳定对应一个值”时返回
//! 结果，不会越权为多来源 merge 伪造表达式。
//! 例如：单一 `NewTable` 定义会在这里直接变成空表构造器表达式。

use super::*;

pub(crate) fn is_multiret_results(results: crate::transformer::ResultPack) -> bool {
    match results {
        crate::transformer::ResultPack::Open(_) => true,
        crate::transformer::ResultPack::Fixed(range) => range.len > 1,
        crate::transformer::ResultPack::Ignore => false,
    }
}

/// 尝试把一个固定定义直接解释成 HIR 表达式。
///
/// 这主要服务 merge 点上的值恢复。我们只在“一个 def 能稳定对应一个值表达式”时
/// 返回 `Some`，否则宁可交回上层继续保守退化，也不在这里伪造来源。
///
/// 这里一旦决定把某个 `call(...)` def 直接恢复成表达式，嵌套的 `callee/args` 也应继续按
/// `single-eval` 语义下钻；否则像 `obj.method(...)` 这种“先读 field 再调用”的值会被
/// 半截留成 temp，最终又把更高层的短路/value-merge 恢复逼回 `if` 壳。
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
/// `single-eval` 变体：允许沿着 Move/GetTable 链深度展开，
/// 把 call 等非 dup-safe 的值也直接内联成表达式。
/// 专门服务被吸收的短路分支里 temp 赋值不会出现的场景。
pub(crate) fn expr_for_fixed_def_single_eval(
    lowering: &ProtoLowering<'_>,
    def_id: DefId,
) -> Option<HirExpr> {
    let def_instr = lowering.dataflow.def_instr(def_id);
    let def_reg = lowering.dataflow.def_reg(def_id);
    let def_block = lowering.dataflow.def_block(def_id);
    let instr = lowering.proto.instrs.get(def_instr.index())?;

    match instr {
        LowInstr::Move(move_instr) if move_instr.dst == def_reg => {
            return Some(expr_for_reg_use_single_eval(
                lowering,
                def_block,
                def_instr,
                move_instr.src,
            ));
        }
        LowInstr::GetTable(get_table) if get_table.dst == def_reg => {
            return Some(lower_table_access_expr_single_eval(
                lowering,
                def_block,
                def_instr,
                get_table.base,
                get_table.key,
            ));
        }
        _ => {}
    }

    expr_for_fixed_def(lowering, def_id)
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
            Some(super::super::helpers::binary_expr(
                lower_binary_op(binary.op),
                expr_for_value_operand_inline(lowering, def_block, def_instr, binary.lhs),
                expr_for_value_operand_inline(lowering, def_block, def_instr, binary.rhs),
            ))
        }
        LowInstr::Concat(concat) if concat.dst == def_reg => {
            let value = concat_expr((0..concat.src.len).map(|offset| {
                expr_for_reg_use_inline(
                    lowering,
                    def_block,
                    def_instr,
                    Reg(concat.src.start.index() + offset),
                )
            }));
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

    let method_name = lower_method_name(lowering.proto, call.method_name);
    let is_method_sugar = matches!(call.kind, CallKind::Method) && method_name.is_some();
    let callee = if is_method_sugar {
        HirExpr::Nil
    } else {
        expr_for_reg_use_single_eval(lowering, block, instr_ref, call.callee)
    };

    Some(HirExpr::Call(Box::new(HirCallExpr {
        callee,
        args: lower_value_pack_single_eval(lowering, block, instr_ref, call.args),
        multiret: false,
        method: matches!(call.kind, CallKind::Method),
        method_name,
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
