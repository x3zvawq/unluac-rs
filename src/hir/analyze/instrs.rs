//! low-IR 普通指令与非循环控制终结到 HIR 语句的直接 lowering。
//!
//! 这个模块只处理“单条指令如何发射 HIR 语句”：普通赋值、调用、返回、vararg 和
//! set-list。它依赖 `ProtoLowering` 中已经准备好的 CFG / Dataflow /
//! StructureFacts / binding 映射，不重新识别 block 结构，也不接管 numeric/generic-for
//! 控制协议；这些 terminator 只能由 StructurePlan 选中的 loop owner 消费。
//!
//! 输入形状：`CALL r0 ...` + 指令 def 映射。
//! 输出形状：`t0 = f(args)` 或 `f(args)` 这类 HIR 语句。

use super::exprs::{
    expr_for_const, expr_for_reg_use, expr_for_value_operand, global_name_for_access,
    lower_binary_op, lower_closure_capture, lower_closure_expr, lower_composite_factory_expr,
    lower_method_name, lower_raw_table_get_expr, lower_raw_table_set_call, lower_table_access_expr,
    lower_table_access_target, lower_unary_op, lower_upvalue_operand_expr,
    lower_upvalue_operand_target, lower_value_pack,
};
use super::helpers::{
    assign_stmt, binary_expr, concat_expr, decode_raw_string, return_stmt, unresolved_expr,
};
use super::lower::ProtoLowering;
use super::shared_closures::CompositeFactoryRef;
use crate::hir::common::{
    HirCallExpr, HirCallStmt, HirClose, HirExpr, HirLValue, HirLocalDecl, HirPackTail, HirStmt,
    HirTableAccess, HirTableConstructor, HirTableField, HirTableSetList, HirToBeClosed,
    HirUnaryExpr, HirValuePack, LocalId,
};
use crate::structure::BlockRef;
use crate::transformer::{
    AccessBase, CallKind, GenericForCallInstr, GetTableKind, InstrRef, LowInstr, Reg, RegRange,
    ResultPack, SetTableKind,
};

pub(super) fn lower_regular_instr(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    instr: &LowInstr,
) -> Option<Vec<HirStmt>> {
    let stmts = match instr {
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
        LowInstr::GetTable(get_table) => fixed_assign(
            lowering,
            instr_ref,
            vec![if get_table.kind == GetTableKind::Raw {
                lower_raw_table_get_expr(lowering, block, instr_ref, get_table.base, get_table.key)
            } else {
                lower_table_access_expr(lowering, block, instr_ref, get_table.base, get_table.key)
            }],
        ),
        LowInstr::SetTable(set_table) if set_table.kind == SetTableKind::Raw => {
            vec![HirStmt::CallStmt(Box::new(HirCallStmt {
                call: lower_raw_table_set_call(
                    lowering,
                    block,
                    instr_ref,
                    set_table.base,
                    set_table.key,
                    set_table.value,
                ),
            }))]
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
        LowInstr::TypeGuard(type_guard) => {
            let call = HirCallExpr {
                callee: unresolved_expr(format!(
                    "LuaJIT {} type guard has no exact Lua source form",
                    type_guard.kind.label()
                )),
                args: vec![expr_for_reg_use(
                    lowering,
                    block,
                    instr_ref,
                    type_guard.subject,
                )]
                .into(),
                method: false,
                method_name: None,
            };
            if type_guard.kind.normalizes_subject() {
                fixed_assign(lowering, instr_ref, vec![HirExpr::Call(Box::new(call))])
            } else {
                vec![HirStmt::CallStmt(Box::new(HirCallStmt { call }))]
            }
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
            let owner = lowering.shared_closure_owner(instr_ref);
            let consumed = lowering.shared_closure_is_consumed(instr_ref);
            if consumed && owner.is_none() {
                return Some(Vec::new());
            }
            let mut stmts = capture_empty_local_decl_stmts(lowering, instr_ref);
            match owner {
                Some(factory) => {
                    let plan = lowering.captured_shared_closures.composite_plan(factory);
                    if !consumed && plan.preserve_owner_value {
                        stmts.extend(fixed_assign(
                            lowering,
                            instr_ref,
                            vec![lower_closure_expr(lowering, block, instr_ref, closure)],
                        ));
                    }
                    stmts.extend(lower_shared_capture_barrier(
                        lowering, block, instr_ref, closure, factory,
                    ));
                    stmts.push(HirStmt::LocalDecl(Box::new(HirLocalDecl {
                        bindings: vec![lowering.shared_factory_local(factory)],
                        values: vec![lower_composite_factory_expr(
                            lowering, block, instr_ref, closure, factory,
                        )]
                        .into(),
                    })));
                }
                None => stmts.extend(fixed_assign(
                    lowering,
                    instr_ref,
                    vec![lower_closure_expr(lowering, block, instr_ref, closure)],
                )),
            }
            stmts
        }
        LowInstr::Close(close) => vec![HirStmt::Close(Box::new(HirClose {
            from_reg: close.from.index(),
        }))],
        LowInstr::Tbc(tbc) => vec![HirStmt::ToBeClosed(Box::new(HirToBeClosed {
            origin: instr_ref,
            reg_index: tbc.reg.index(),
            value: expr_for_reg_use(lowering, block, instr_ref, tbc.reg),
        }))],
        LowInstr::GenericForCall(instr) => {
            let ResultPack::Fixed(results) = instr.results else {
                return None;
            };
            lower_generic_for_call(lowering, block, instr_ref, instr, results)
        }
        LowInstr::TailCall(_)
        | LowInstr::Return(_)
        | LowInstr::NumericForInit(_)
        | LowInstr::NumericForLoop(_)
        | LowInstr::GenericForPrep(_)
        | LowInstr::GenericForLoop(_)
        | LowInstr::Jump(_)
        | LowInstr::Branch(_) => return None,
    };
    Some(stmts)
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

pub(super) fn lower_terminal_instr(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    instr: &LowInstr,
) -> Option<Vec<HirStmt>> {
    match instr {
        LowInstr::Return(ret) => Some(vec![return_stmt(lower_value_pack(
            lowering, block, instr_ref, ret.values,
        ))]),
        LowInstr::TailCall(tail_call) => {
            let method_name = lower_method_name(lowering, tail_call.method_name);
            let callee = expr_for_reg_use(lowering, block, instr_ref, tail_call.callee);
            Some(vec![return_stmt(HirValuePack::expanding(
                Vec::new(),
                HirPackTail::open(HirExpr::Call(Box::new(HirCallExpr {
                    callee,
                    args: lower_value_pack(lowering, block, instr_ref, tail_call.args),
                    method: matches!(tail_call.kind, CallKind::Method),
                    method_name,
                }))),
            ))])
        }
        _ => None,
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
    results: RegRange,
) -> Vec<HirStmt> {
    lower_result_assign(
        lowering,
        instr_ref,
        generic_for_iterator_call(lowering, block, instr_ref, instr),
        results,
    )
}

fn generic_for_iterator_call(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    instr: &GenericForCallInstr,
) -> HirExpr {
    let callee = expr_for_reg_use(lowering, block, instr_ref, instr.iterator);
    let args = vec![
        expr_for_reg_use(lowering, block, instr_ref, instr.state),
        expr_for_reg_use(lowering, block, instr_ref, instr.control),
    ]
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
    let results = call.results;
    let method_name = lower_method_name(lowering, call.method_name);
    let callee = expr_for_reg_use(lowering, block, instr_ref, call.callee);
    let call_expr = HirCallExpr {
        callee,
        args: lower_value_pack(lowering, block, instr_ref, call.args),
        method: matches!(call.kind, CallKind::Method),
        method_name,
    };

    match results {
        ResultPack::Ignore => call_stmt(call_expr),
        ResultPack::Open(_) if lowering.open_pack_is_owned(instr_ref) => Vec::new(),
        ResultPack::Open(_) => call_stmt(call_expr),
        ResultPack::Fixed(results) => lower_result_assign(
            lowering,
            instr_ref,
            HirExpr::Call(Box::new(call_expr)),
            results,
        ),
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
        ResultPack::Fixed(results) => {
            lower_result_assign(lowering, instr_ref, HirExpr::VarArg, results)
        }
    }
}

fn call_stmt(call: HirCallExpr) -> Vec<HirStmt> {
    vec![HirStmt::CallStmt(Box::new(HirCallStmt { call }))]
}

fn lower_result_assign(
    lowering: &ProtoLowering<'_>,
    instr_ref: InstrRef,
    expr: HirExpr,
    range: RegRange,
) -> Vec<HirStmt> {
    let values = if range.len > 1 {
        HirValuePack::expanding(Vec::new(), HirPackTail::exact(expr, range.len))
    } else {
        HirValuePack::fixed(vec![expr])
    };
    fixed_assign(lowering, instr_ref, values)
}

fn lower_shared_capture_barrier(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    closure: &crate::transformer::ClosureInstr,
    factory: CompositeFactoryRef,
) -> Vec<HirStmt> {
    let Some(barrier) = lowering.captured_shared_closures.capture_barrier(factory) else {
        return Vec::new();
    };
    let sources = &lowering
        .captured_shared_closures
        .composite_plan(factory)
        .outer_captures;
    let mut locals = Vec::new();
    let mut fields = Vec::new();
    for (index, snapshot) in barrier.snapshots.iter().enumerate() {
        let Some(local) = snapshot else {
            continue;
        };
        let capture =
            lower_closure_capture(lowering, block, instr_ref, closure.dst, sources[index]);
        locals.push(*local);
        fields.push(HirTableField::Array(capture.value));
    }
    let table = HirExpr::TableConstructor(Box::new(HirTableConstructor {
        fields,
        trailing_multivalue: None,
    }));
    let snapshots = locals
        .iter()
        .enumerate()
        .map(|(index, _)| {
            HirExpr::TableAccess(Box::new(HirTableAccess {
                base: HirExpr::LocalRef(barrier.box_local),
                key: HirExpr::Integer((index + 1) as i64),
            }))
        })
        .collect::<Vec<_>>();
    vec![
        HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: vec![barrier.box_local],
            values: vec![table].into(),
        })),
        HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: locals,
            values: snapshots.into(),
        })),
    ]
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

pub(super) fn local_decl_stmts(locals: Vec<LocalId>) -> Vec<HirStmt> {
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
    let block = lowering.cfg.instr_to_block[instr_ref.index()];
    lowering.dataflow.instr_defs[instr_ref.index()]
        .iter()
        .zip(&lowering.bindings.instr_fixed_defs[instr_ref.index()])
        .map(|(def, temp)| {
            // for 的可见 binding 是当前 body 内该寄存器的词法 owner；显式写入也必须
            // 回到同一个 local。只在读取侧映射会把 `i = value` 留成无人读取的 temp，
            // 随后 dead-temp 清理会静默删除真实赋值。
            lowering
                .bindings
                .local_for_reg_in_block(block, lowering.dataflow.def_reg(*def))
                .map_or_else(
                    || lowering.bindings.lvalue_for_temp(*temp),
                    HirLValue::Local,
                )
        })
        .collect()
}
