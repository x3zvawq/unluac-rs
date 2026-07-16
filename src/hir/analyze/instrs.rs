//! low-IR 普通指令与非循环控制终结到 HIR 语句的直接 lowering。
//!
//! 这个模块只处理“单条指令如何发射 HIR 语句”：普通赋值、调用、返回、vararg、
//! set-list 和显式 jump/branch。它依赖 `ProtoLowering` 中已经准备好的 CFG / Dataflow /
//! StructureFacts / binding 映射，不重新识别 block 结构，也不接管 numeric/generic-for
//! 控制协议；这些 terminator 只能由 StructurePlan 选中的 loop owner 消费。
//!
//! 输入形状：`CALL r0 ...` + 指令 def 映射。
//! 输出形状：`t0 = f(args)` 或 `f(args)` 这类 HIR 语句。

use std::collections::BTreeMap;

use super::exprs::{
    expr_for_closure_capture, expr_for_const, expr_for_reg_use, expr_for_value_operand,
    global_name_for_access, lower_binary_op, lower_branch_cond, lower_method_name,
    lower_table_access_expr, lower_table_access_target, lower_unary_op, lower_upvalue_operand_expr,
    lower_upvalue_operand_target, lower_value_pack,
};
use super::helpers::{
    assign_stmt, binary_expr, branch_stmt, concat_expr, decode_raw_string, goto_block,
    label_for_block, return_stmt,
};
use super::lower::ProtoLowering;
use crate::hir::common::{
    HirCallExpr, HirCallStmt, HirCapture, HirClose, HirClosureExpr, HirExpr, HirLValue, HirLabelId,
    HirLocalDecl, HirPackTail, HirStmt, HirTableSetList, HirToBeClosed, HirUnaryExpr, HirValuePack,
    LocalId,
};
use crate::structure::BlockRef;
use crate::transformer::{
    AccessBase, AccessKey, CallKind, GenericForCallInstr, GetTableKind, InstrRef, LowInstr,
    MethodNameHint, Reg, ResultPack,
};

pub(super) fn lower_regular_instr(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    instr: &LowInstr,
) -> Vec<HirStmt> {
    match instr {
        LowInstr::Move(move_instr) => fixed_assign(
            lowering,
            instr_ref,
            vec![expr_for_reg_use(lowering, block, instr_ref, move_instr.src)],
        ),
        LowInstr::LoadNil(_instr) => fixed_assign(
            lowering,
            instr_ref,
            lowering.bindings.instr_fixed_defs[instr_ref.index()]
                .iter()
                .map(|_temp| HirExpr::Nil)
                .collect::<Vec<_>>(),
        ),
        LowInstr::LoadBool(load_bool) => {
            fixed_assign(lowering, instr_ref, vec![HirExpr::Boolean(load_bool.value)])
        }
        LowInstr::LoadConst(load_const) => fixed_assign(
            lowering,
            instr_ref,
            vec![expr_for_const(lowering.proto, load_const.value)],
        ),
        LowInstr::LoadInteger(load_integer) => fixed_assign(
            lowering,
            instr_ref,
            vec![HirExpr::Integer(load_integer.value)],
        ),
        LowInstr::LoadNumber(load_number) => fixed_assign(
            lowering,
            instr_ref,
            vec![HirExpr::Number(load_number.value)],
        ),
        LowInstr::UnaryOp(unary) => fixed_assign(
            lowering,
            instr_ref,
            vec![HirExpr::Unary(Box::new(HirUnaryExpr {
                op: lower_unary_op(unary.op),
                expr: expr_for_reg_use(lowering, block, instr_ref, unary.src),
            }))],
        ),
        LowInstr::BinaryOp(binary) => fixed_assign(
            lowering,
            instr_ref,
            vec![binary_expr(
                lower_binary_op(binary.op),
                expr_for_value_operand(lowering, block, instr_ref, binary.lhs),
                expr_for_value_operand(lowering, block, instr_ref, binary.rhs),
            )],
        ),
        LowInstr::Concat(concat) => {
            let value = concat_expr((0..concat.src.len).map(|offset| {
                expr_for_reg_use(
                    lowering,
                    block,
                    instr_ref,
                    Reg(concat.src.start.index() + offset),
                )
            }));
            fixed_assign(lowering, instr_ref, vec![value])
        }
        LowInstr::GetUpvalue(get_upvalue)
            if env_upvalue_is_consumed_by_global_accesses(lowering, instr_ref, get_upvalue) =>
        {
            Vec::new()
        }
        LowInstr::GetUpvalue(get_upvalue) => fixed_assign(
            lowering,
            instr_ref,
            vec![lower_upvalue_operand_expr(lowering, get_upvalue.src)],
        ),
        LowInstr::SetUpvalue(set_upvalue) => vec![assign_stmt(
            vec![lower_upvalue_operand_target(lowering, set_upvalue.dst)],
            vec![expr_for_value_operand(
                lowering,
                block,
                instr_ref,
                set_upvalue.src,
            )],
        )],
        LowInstr::GetTable(get_table) => {
            // `SELF` / `NAMECALL` 三元式会在 Move + GetTable 之后紧跟一个方法调用，
            // 该调用的 `method_name` 命中时 AST 端会走 `obj:method()` 糖，彻底忽略
            // GetTable 写入的目标寄存器。这里在 HIR 降级阶段直接丢弃这类装饰性的
            // GetTable，避免下游 `temp-inline` / `locals` 等 pass 把它保留成无意义的
            // `local x = obj.method` 语句。
            //
            // 只在 Method 标记、键是字符串常量时跳过：这样和
            // `lower_method_name` 对 `MethodNameHint` 的成功条件一一对应，若常量不是
            // 字符串（理论上不会出现，但保险），依然按普通表访问发射。
            if get_table.kind == GetTableKind::Method
                && let AccessKey::Const(const_ref) = get_table.key
                && lower_method_name(lowering, Some(MethodNameHint { const_ref })).is_some()
            {
                Vec::new()
            } else {
                fixed_assign(
                    lowering,
                    instr_ref,
                    vec![lower_table_access_expr(
                        lowering,
                        block,
                        instr_ref,
                        get_table.base,
                        get_table.key,
                    )],
                )
            }
        }
        LowInstr::SetTable(set_table) => vec![assign_stmt(
            vec![lower_table_access_target(
                lowering,
                block,
                instr_ref,
                set_table.base,
                set_table.key,
            )],
            vec![expr_for_value_operand(
                lowering,
                block,
                instr_ref,
                set_table.value,
            )],
        )],
        LowInstr::ErrNil(err_nnil) => {
            vec![HirStmt::ErrNil(Box::new(crate::hir::common::HirErrNil {
                value: expr_for_reg_use(lowering, block, instr_ref, err_nnil.subject),
                name: err_nnil.name.and_then(|const_ref| {
                    match lowering
                        .proto
                        .constants
                        .common
                        .literals
                        .get(const_ref.index())
                    {
                        Some(crate::parser::RawLiteralConst::String(value)) => {
                            Some(decode_raw_string(value))
                        }
                        _ => None,
                    }
                }),
            }))]
        }
        LowInstr::NewTable(_new_table) => fixed_assign(
            lowering,
            instr_ref,
            vec![HirExpr::TableConstructor(Box::default())],
        ),
        LowInstr::SetList(set_list) => lower_set_list(lowering, block, instr_ref, set_list),
        LowInstr::Call(call) => lower_call(lowering, block, instr_ref, call),
        LowInstr::VarArg(vararg) => lower_vararg(lowering, instr_ref, vararg.results),
        LowInstr::Closure(closure) => {
            let mut stmts = capture_empty_local_decl_stmts(lowering, instr_ref);
            stmts.extend(fixed_assign(
                lowering,
                instr_ref,
                vec![HirExpr::Closure(Box::new(HirClosureExpr {
                    proto: lowering.child_refs[closure.proto.index()],
                    captures: closure
                        .captures
                        .iter()
                        .map(|capture| HirCapture {
                            value: expr_for_closure_capture(
                                lowering,
                                block,
                                instr_ref,
                                closure.dst,
                                capture.source,
                            ),
                        })
                        .collect(),
                }))],
            ));
            stmts
        }
        LowInstr::Close(close) => vec![HirStmt::Close(Box::new(HirClose {
            from_reg: close.from.index(),
        }))],
        LowInstr::Tbc(tbc) => vec![HirStmt::ToBeClosed(Box::new(HirToBeClosed {
            reg_index: tbc.reg.index(),
            value: expr_for_reg_use(lowering, block, instr_ref, tbc.reg),
        }))],
        LowInstr::GenericForCall(instr) => {
            lower_generic_for_call(lowering, block, instr_ref, instr)
        }
        LowInstr::TailCall(_)
        | LowInstr::Return(_)
        | LowInstr::NumericForInit(_)
        | LowInstr::NumericForLoop(_)
        | LowInstr::GenericForLoop(_)
        | LowInstr::Jump(_)
        | LowInstr::Branch(_) => {
            unreachable!("control terminators must be lowered by their structure owner")
        }
    }
}

fn env_upvalue_is_consumed_by_global_accesses(
    lowering: &ProtoLowering<'_>,
    instr_ref: InstrRef,
    get_upvalue: &crate::transformer::GetUpvalueInstr,
) -> bool {
    if !matches!(get_upvalue.src, crate::transformer::UpvalueOperand::Env) {
        return false;
    }
    let Some(def) = lowering
        .dataflow
        .instr_def_for_reg(instr_ref, get_upvalue.dst)
    else {
        return false;
    };
    if lowering
        .dataflow
        .def_phi_uses
        .get(def.index())
        .is_some_and(|uses| !uses.is_empty())
    {
        return false;
    }

    lowering
        .dataflow
        .def_uses
        .get(def.index())
        .is_some_and(|uses| {
            uses.iter().all(|site| {
                let use_block = lowering.cfg.instr_to_block[site.instr.index()];
                let access = match &lowering.proto.instrs[site.instr.index()] {
                    LowInstr::GetTable(access) if access.base == AccessBase::Reg(site.reg) => {
                        (access.base, access.key)
                    }
                    LowInstr::SetTable(access) if access.base == AccessBase::Reg(site.reg) => {
                        (access.base, access.key)
                    }
                    _ => return false,
                };
                global_name_for_access(lowering, use_block, site.instr, access.0, access.1)
                    .is_some()
            })
        })
}

pub(super) fn lower_control_instr(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    instr: &LowInstr,
    label_map: &BTreeMap<BlockRef, HirLabelId>,
) -> Vec<HirStmt> {
    match instr {
        LowInstr::Jump(jump) => vec![super::helpers::goto_stmt(label_for_block(
            lowering.cfg,
            label_map,
            jump.target,
        ))],
        LowInstr::Branch(branch) => vec![branch_stmt(
            lower_branch_cond(lowering, block, instr_ref, branch.cond),
            goto_block(label_for_block(lowering.cfg, label_map, branch.then_target)),
            Some(goto_block(label_for_block(
                lowering.cfg,
                label_map,
                branch.else_target,
            ))),
        )],
        LowInstr::Return(ret) => {
            vec![return_stmt(lower_value_pack(
                lowering, block, instr_ref, ret.values,
            ))]
        }
        LowInstr::TailCall(tail_call) => {
            let method_name = lower_method_name(lowering, tail_call.method_name);
            let is_method_sugar =
                matches!(tail_call.kind, CallKind::Method) && method_name.is_some();
            let callee = if is_method_sugar {
                HirExpr::Nil
            } else {
                expr_for_reg_use(lowering, block, instr_ref, tail_call.callee)
            };
            vec![return_stmt(HirValuePack::expanding(
                Vec::new(),
                HirPackTail::open(HirExpr::Call(Box::new(HirCallExpr {
                    callee,
                    args: lower_value_pack(lowering, block, instr_ref, tail_call.args),
                    method: matches!(tail_call.kind, CallKind::Method),
                    method_name,
                }))),
            ))]
        }
        LowInstr::NumericForInit(_) | LowInstr::NumericForLoop(_) | LowInstr::GenericForLoop(_) => {
            unreachable!("for control terminators must be consumed by a loop owner")
        }
        _ => unreachable!("non-control instructions must use regular lowering"),
    }
}

fn lower_set_list(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    set_list: &crate::transformer::SetListInstr,
) -> Vec<HirStmt> {
    let values = lower_value_pack(lowering, block, instr_ref, set_list.values);
    vec![HirStmt::TableSetList(Box::new(HirTableSetList {
        base: expr_for_reg_use(lowering, block, instr_ref, set_list.base),
        start_index: set_list.start_index,
        values,
    }))]
}

fn lower_generic_for_call(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    instr: &GenericForCallInstr,
) -> Vec<HirStmt> {
    lower_result_assign(
        lowering,
        instr_ref,
        generic_for_iterator_call(lowering, block, instr_ref, instr),
        instr.results,
    )
}

fn generic_for_iterator_call(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    instr: &GenericForCallInstr,
) -> HirExpr {
    let callee = expr_for_reg_use(lowering, block, instr_ref, instr.state.start);
    let args = (1..instr.state.len)
        .map(|offset| {
            expr_for_reg_use(
                lowering,
                block,
                instr_ref,
                Reg(instr.state.start.index() + offset),
            )
        })
        .collect::<Vec<_>>()
        .into();

    HirExpr::Call(Box::new(HirCallExpr {
        callee,
        args,
        method: false,
        method_name: None,
    }))
}

fn lower_call(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    call: &crate::transformer::CallInstr,
) -> Vec<HirStmt> {
    let method_name = lower_method_name(lowering, call.method_name);
    let is_method_sugar = matches!(call.kind, CallKind::Method) && method_name.is_some();
    // 当调用会被 AST 渲染成 `obj:method()` 糖时，AST 只读 args[0] 和
    // method_name，callee 被丢弃。这里直接把 callee 置为 Nil，从而让源自
    // `SELF` / `NAMECALL` 的 method-load GetTable 在 HIR 中也真正失去读者，
    // 配合同一 pass 里对 Method 读取的跳过逻辑建立闭环。
    let callee = if is_method_sugar {
        HirExpr::Nil
    } else {
        expr_for_reg_use(lowering, block, instr_ref, call.callee)
    };
    let expr = HirExpr::Call(Box::new(HirCallExpr {
        callee,
        args: lower_value_pack(lowering, block, instr_ref, call.args),
        method: matches!(call.kind, CallKind::Method),
        method_name,
    }));

    match call.results {
        ResultPack::Ignore => call_stmt(expr),
        ResultPack::Open(_) if lowering.open_pack_is_owned(instr_ref) => Vec::new(),
        ResultPack::Open(_) => call_stmt(expr),
        ResultPack::Fixed(_) => lower_result_assign(lowering, instr_ref, expr, call.results),
    }
}

fn lower_vararg(
    lowering: &ProtoLowering<'_>,
    instr_ref: InstrRef,
    results: ResultPack,
) -> Vec<HirStmt> {
    match results {
        // VARARG 的结果数为零时，VM 不读取也不写入任何值；源码层没有对应语句。
        ResultPack::Ignore => Vec::new(),
        ResultPack::Open(_) if lowering.open_pack_is_owned(instr_ref) => Vec::new(),
        ResultPack::Open(_) => Vec::new(),
        ResultPack::Fixed(_) => lower_result_assign(lowering, instr_ref, HirExpr::VarArg, results),
    }
}

fn call_stmt(expr: HirExpr) -> Vec<HirStmt> {
    let HirExpr::Call(call) = expr else {
        unreachable!("call lowering should always build a call expression");
    };
    vec![HirStmt::CallStmt(Box::new(HirCallStmt { call: *call }))]
}

fn lower_result_assign(
    lowering: &ProtoLowering<'_>,
    instr_ref: InstrRef,
    expr: HirExpr,
    results: ResultPack,
) -> Vec<HirStmt> {
    let ResultPack::Fixed(range) = results else {
        unreachable!("only fixed results can be assigned as scalar HIR values");
    };
    let values = if range.len > 1 {
        HirValuePack::expanding(Vec::new(), HirPackTail::exact(expr, range.len))
    } else {
        HirValuePack::fixed(vec![expr])
    };
    fixed_assign(lowering, instr_ref, values)
}

fn fixed_assign(
    lowering: &ProtoLowering<'_>,
    instr_ref: InstrRef,
    values: impl Into<HirValuePack>,
) -> Vec<HirStmt> {
    let values = values.into();
    let temps = &lowering.bindings.instr_fixed_defs[instr_ref.index()];
    let decl_locals = temps
        .iter()
        .filter_map(|temp| {
            lowering
                .bindings
                .captured_temp_decl_locals
                .get(temp)
                .copied()
        })
        .collect::<Vec<_>>();
    let targets = lower_fixed_targets(lowering, instr_ref);
    if targets.is_empty() {
        Vec::new()
    } else if decl_locals.len() == targets.len()
        && values.exact_result_len() == Some(decl_locals.len())
    {
        vec![HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: decl_locals,
            values,
        }))]
    } else {
        let mut stmts = local_decl_stmts(decl_locals);
        stmts.push(assign_stmt(targets, values));
        stmts
    }
}

fn capture_empty_local_decl_stmts(
    lowering: &ProtoLowering<'_>,
    instr_ref: InstrRef,
) -> Vec<HirStmt> {
    local_decl_stmts(
        lowering
            .bindings
            .capture_empty_local_decls
            .get(&instr_ref.index())
            .cloned()
            .unwrap_or_default(),
    )
}

fn local_decl_stmts(locals: Vec<LocalId>) -> Vec<HirStmt> {
    if locals.is_empty() {
        Vec::new()
    } else {
        vec![HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: locals,
            values: HirValuePack::default(),
        }))]
    }
}

fn lower_fixed_targets(lowering: &ProtoLowering<'_>, instr_ref: InstrRef) -> Vec<HirLValue> {
    lowering.bindings.instr_fixed_defs[instr_ref.index()]
        .iter()
        .map(|temp| lowering.bindings.lvalue_for_temp(*temp))
        .collect()
}
