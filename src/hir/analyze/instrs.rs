//! low-IR 指令到 HIR 语句的直接 lowering。
//!
//! 这个模块只处理“单条指令如何发射 HIR 语句”：普通赋值、调用、返回、vararg、
//! set-list、for 控制指令和 fallback 控制指令。它依赖 `ProtoLowering` 中已经准备好的
//! CFG / Dataflow / StructureFacts / binding 映射，不重新识别 block 结构，也不决定
//! branch、loop、short-circuit 应该如何结构化。
//!
//! 输入形状：`CALL r0 ...` + 指令 def 映射。
//! 输出形状：`t0 = f(args)` 或 `f(args)` 这类 HIR 语句。

use std::collections::BTreeMap;

use super::exprs::{
    expr_for_closure_capture, expr_for_const, expr_for_reg_use, expr_for_value_operand,
    is_multiret_results, lower_binary_op, lower_branch_cond, lower_method_name,
    lower_table_access_expr, lower_table_access_target, lower_unary_op, lower_value_pack,
    lower_value_pack_components,
};
use super::helpers::{
    assign_stmt, binary_expr, branch_stmt, build_label_map_for_summary, concat_expr,
    decode_raw_string, goto_block, label_for_block, return_stmt, unresolved_expr,
    unstructured_stmt,
};
use super::lower::ProtoLowering;
use crate::hir::common::{
    HirBinaryExpr, HirBinaryOpKind, HirBlock, HirCallExpr, HirCallStmt, HirCapture, HirClose,
    HirClosureExpr, HirExpr, HirLValue, HirLabelId, HirLocalDecl, HirStmt, HirTableSetList,
    HirToBeClosed, HirUnaryExpr, LocalId, UpvalueId,
};
use crate::structure::BlockRef;
use crate::transformer::{
    AccessKey, CallKind, GenericForCallInstr, GenericForLoopInstr, InstrRef, LowInstr, Reg,
    ResultPack,
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
                .collect(),
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
        LowInstr::GetUpvalue(get_upvalue) => fixed_assign(
            lowering,
            instr_ref,
            vec![HirExpr::UpvalueRef(UpvalueId(get_upvalue.src.index()))],
        ),
        LowInstr::SetUpvalue(set_upvalue) => vec![assign_stmt(
            vec![HirLValue::Upvalue(UpvalueId(set_upvalue.dst.index()))],
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
            // 只在 method_load 标记为真、键是字符串常量时跳过：这样和
            // `lower_method_name` 对 `MethodNameHint` 的成功条件一一对应，若常量不是
            // 字符串（理论上不会出现，但保险），依然按普通表访问发射。
            if get_table.method_load
                && let AccessKey::Const(const_ref) = get_table.key
                && matches!(
                    lowering
                        .proto
                        .constants
                        .common
                        .literals
                        .get(const_ref.index()),
                    Some(crate::parser::RawLiteralConst::String(_))
                )
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
        LowInstr::TailCall(tail_call) => {
            // TailCall 总是展开所有返回值
            let method_name = lower_method_name(lowering.proto, tail_call.method_name);
            let is_method_sugar =
                matches!(tail_call.kind, CallKind::Method) && method_name.is_some();
            let callee = if is_method_sugar {
                // 方法调用糖下，AST 直接用 args[0]+method_name 重建 callee；
                // 这里主动置空，避免上游 method-load GetTable 的目标温度被
                // `temp-inline` / `locals` 等 pass 当成被读取的 live 值留下来。
                HirExpr::Nil
            } else {
                expr_for_reg_use(lowering, block, instr_ref, tail_call.callee)
            };
            vec![return_stmt(
                vec![HirExpr::Call(Box::new(HirCallExpr {
                    callee,
                    args: lower_value_pack(lowering, block, instr_ref, tail_call.args),
                    multiret: true,
                    method: matches!(tail_call.kind, CallKind::Method),
                    method_name,
                }))],
                true,
            )]
        }
        LowInstr::VarArg(vararg) => lower_vararg(lowering, instr_ref, vararg.results),
        LowInstr::Return(ret) => {
            let trailing_multiret = matches!(ret.values, crate::transformer::ValuePack::Open(_));
            vec![return_stmt(
                lower_value_pack(lowering, block, instr_ref, ret.values),
                trailing_multiret,
            )]
        }
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
        LowInstr::NumericForInit(instr) => vec![
            assign_stmt(
                lower_fixed_targets(lowering, instr_ref),
                vec![unresolved_expr(format!(
                    "numeric-for-init index=r{} limit=r{} step=r{}",
                    instr.index.index(),
                    instr.limit.index(),
                    instr.step.index()
                ))],
            ),
            branch_stmt(
                unresolved_expr("numeric-for-init cond"),
                goto_block(label_for_block(
                    lowering.cfg,
                    &build_label_map_for_summary(lowering.cfg),
                    instr.body_target,
                )),
                Some(goto_block(label_for_block(
                    lowering.cfg,
                    &build_label_map_for_summary(lowering.cfg),
                    instr.exit_target,
                ))),
            ),
        ],
        LowInstr::NumericForLoop(instr) => vec![
            assign_stmt(
                lower_fixed_targets(lowering, instr_ref),
                vec![unresolved_expr(format!(
                    "numeric-for-loop index=r{} limit=r{} step=r{}",
                    instr.index.index(),
                    instr.limit.index(),
                    instr.step.index()
                ))],
            ),
            branch_stmt(
                unresolved_expr("numeric-for-loop cond"),
                goto_block(label_for_block(
                    lowering.cfg,
                    &build_label_map_for_summary(lowering.cfg),
                    instr.body_target,
                )),
                Some(goto_block(label_for_block(
                    lowering.cfg,
                    &build_label_map_for_summary(lowering.cfg),
                    instr.exit_target,
                ))),
            ),
        ],
        LowInstr::GenericForCall(instr) => {
            lower_generic_for_call(lowering, block, instr_ref, instr)
        }
        LowInstr::GenericForLoop(_instr) => vec![unstructured_stmt("generic-for-loop")],
        LowInstr::Jump(_) | LowInstr::Branch(_) => Vec::new(),
    }
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
            let trailing_multiret = matches!(ret.values, crate::transformer::ValuePack::Open(_));
            vec![return_stmt(
                lower_value_pack(lowering, block, instr_ref, ret.values),
                trailing_multiret,
            )]
        }
        LowInstr::TailCall(tail_call) => {
            let method_name = lower_method_name(lowering.proto, tail_call.method_name);
            let is_method_sugar =
                matches!(tail_call.kind, CallKind::Method) && method_name.is_some();
            let callee = if is_method_sugar {
                HirExpr::Nil
            } else {
                expr_for_reg_use(lowering, block, instr_ref, tail_call.callee)
            };
            vec![return_stmt(
                vec![HirExpr::Call(Box::new(HirCallExpr {
                    callee,
                    args: lower_value_pack(lowering, block, instr_ref, tail_call.args),
                    multiret: true,
                    method: matches!(tail_call.kind, CallKind::Method),
                    method_name,
                }))],
                true,
            )]
        }
        LowInstr::NumericForInit(instr) => vec![
            assign_stmt(
                lower_fixed_targets(lowering, instr_ref),
                vec![unresolved_expr(format!(
                    "numeric-for-init index=r{}",
                    instr.index.index()
                ))],
            ),
            branch_stmt(
                unresolved_expr("numeric-for-init cond"),
                goto_block(label_for_block(lowering.cfg, label_map, instr.body_target)),
                Some(goto_block(label_for_block(
                    lowering.cfg,
                    label_map,
                    instr.exit_target,
                ))),
            ),
        ],
        LowInstr::NumericForLoop(instr) => vec![
            assign_stmt(
                lower_fixed_targets(lowering, instr_ref),
                vec![unresolved_expr(format!(
                    "numeric-for-loop index=r{}",
                    instr.index.index()
                ))],
            ),
            branch_stmt(
                unresolved_expr("numeric-for-loop cond"),
                goto_block(label_for_block(lowering.cfg, label_map, instr.body_target)),
                Some(goto_block(label_for_block(
                    lowering.cfg,
                    label_map,
                    instr.exit_target,
                ))),
            ),
        ],
        LowInstr::GenericForLoop(instr) => vec![branch_stmt(
            generic_for_loop_continue_cond(lowering, block, instr_ref, instr),
            {
                let mut body = generic_for_control_update(lowering, block, instr_ref, instr);
                body.extend(
                    goto_block(label_for_block(lowering.cfg, label_map, instr.body_target)).stmts,
                );
                HirBlock { stmts: body }
            },
            Some(goto_block(label_for_block(
                lowering.cfg,
                label_map,
                instr.exit_target,
            ))),
        )],
        _ => lower_regular_instr(lowering, block, instr_ref, instr),
    }
}

pub(super) fn is_control_terminator(instr: &LowInstr) -> bool {
    matches!(
        instr,
        LowInstr::Jump(_)
            | LowInstr::Branch(_)
            | LowInstr::Return(_)
            | LowInstr::TailCall(_)
            | LowInstr::NumericForInit(_)
            | LowInstr::NumericForLoop(_)
            | LowInstr::GenericForLoop(_)
    )
}

fn lower_set_list(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    set_list: &crate::transformer::SetListInstr,
) -> Vec<HirStmt> {
    let (values, trailing_multivalue) =
        lower_value_pack_components(lowering, block, instr_ref, set_list.values);
    vec![HirStmt::TableSetList(Box::new(HirTableSetList {
        base: expr_for_reg_use(lowering, block, instr_ref, set_list.base),
        start_index: set_list.start_index,
        values,
        trailing_multivalue,
    }))]
}

fn lower_generic_for_call(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    instr: &GenericForCallInstr,
) -> Vec<HirStmt> {
    fixed_or_open_assign(
        lowering,
        instr_ref,
        vec![generic_for_iterator_call(lowering, block, instr_ref, instr)],
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
        .collect();

    HirExpr::Call(Box::new(HirCallExpr {
        callee,
        args,
        multiret: true,
        method: false,
        method_name: None,
    }))
}

pub(super) fn generic_for_loop_continue_cond(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    instr: &GenericForLoopInstr,
) -> HirExpr {
    let first_binding = generic_for_loop_first_binding_expr(lowering, block, instr_ref, instr);
    HirExpr::Binary(Box::new(HirBinaryExpr {
        op: HirBinaryOpKind::Eq,
        lhs: first_binding,
        rhs: HirExpr::Nil,
    }))
    .negate()
}

pub(super) fn generic_for_control_update(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    instr: &GenericForLoopInstr,
) -> Vec<HirStmt> {
    let target = match expr_for_reg_use(lowering, block, instr_ref, instr.control) {
        HirExpr::TempRef(temp) => HirLValue::Temp(temp),
        HirExpr::LocalRef(local) => HirLValue::Local(local),
        _ => return Vec::new(),
    };
    let value = generic_for_loop_first_binding_expr(lowering, block, instr_ref, instr);
    vec![assign_stmt(vec![target], vec![value])]
}

fn generic_for_loop_first_binding_expr(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    instr: &GenericForLoopInstr,
) -> HirExpr {
    // `TFORLOOP` 的判空对象是同一 header 中前一条 `GenericForCall` 刚写出的
    // 第一个返回值；不能用 loop 指令处对 binding 寄存器的 reaching value，否则会
    // 读到上一轮迭代的源码 local。
    let range = lowering.cfg.blocks[block.index()].instrs;
    if instr_ref.index() > range.start.index()
        && let Some(LowInstr::GenericForCall(_)) = lowering.proto.instrs.get(instr_ref.index() - 1)
        && let Some(temp) = lowering.bindings.instr_fixed_defs[instr_ref.index() - 1].first()
    {
        return HirExpr::TempRef(*temp);
    }

    expr_for_reg_use(lowering, block, instr_ref, instr.bindings.start)
}

fn lower_call(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    call: &crate::transformer::CallInstr,
) -> Vec<HirStmt> {
    let method_name = lower_method_name(lowering.proto, call.method_name);
    let is_method_sugar = matches!(call.kind, CallKind::Method) && method_name.is_some();
    // 当调用会被 AST 渲染成 `obj:method()` 糖时，AST 只读 args[0] 和
    // method_name，callee 被丢弃。这里直接把 callee 置为 Nil，从而让源自
    // `SELF` / `NAMECALL` 的 method-load GetTable 在 HIR 中也真正失去读者，
    // 配合同一 pass 里对 `method_load` 的跳过逻辑建立闭环。
    let callee = if is_method_sugar {
        HirExpr::Nil
    } else {
        expr_for_reg_use(lowering, block, instr_ref, call.callee)
    };
    let expr = HirExpr::Call(Box::new(HirCallExpr {
        callee,
        args: lower_value_pack(lowering, block, instr_ref, call.args),
        multiret: is_multiret_results(call.results),
        method: matches!(call.kind, CallKind::Method),
        method_name,
    }));

    if matches!(call.results, ResultPack::Ignore) {
        vec![HirStmt::CallStmt(Box::new(HirCallStmt {
            call: match expr {
                HirExpr::Call(call) => *call,
                _ => unreachable!("call lowering should always build a call expression"),
            },
        }))]
    } else {
        fixed_or_open_assign(lowering, instr_ref, vec![expr])
    }
}

fn lower_vararg(
    lowering: &ProtoLowering<'_>,
    instr_ref: InstrRef,
    results: ResultPack,
) -> Vec<HirStmt> {
    let expr = HirExpr::VarArg;
    match results {
        ResultPack::Ignore => vec![unstructured_stmt("vararg ignore")],
        _ => fixed_or_open_assign(lowering, instr_ref, vec![expr]),
    }
}

fn fixed_assign(
    lowering: &ProtoLowering<'_>,
    instr_ref: InstrRef,
    values: Vec<HirExpr>,
) -> Vec<HirStmt> {
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
    } else if decl_locals.len() == targets.len() && decl_locals.len() == values.len() {
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
            values: Vec::new(),
        }))]
    }
}

fn fixed_or_open_assign(
    lowering: &ProtoLowering<'_>,
    instr_ref: InstrRef,
    values: Vec<HirExpr>,
) -> Vec<HirStmt> {
    let mut targets = lower_fixed_targets(lowering, instr_ref);
    if let Some(open_target) = lowering.bindings.instr_open_defs[instr_ref.index()] {
        targets.push(HirLValue::Temp(open_target));
    }

    if targets.is_empty() {
        Vec::new()
    } else {
        vec![assign_stmt(targets, values)]
    }
}

fn lower_fixed_targets(lowering: &ProtoLowering<'_>, instr_ref: InstrRef) -> Vec<HirLValue> {
    lowering.bindings.instr_fixed_defs[instr_ref.index()]
        .iter()
        .map(|temp| lowering.bindings.lvalue_for_temp(*temp))
        .collect()
}
