//! low-IR 普通指令与非循环控制终结到 HIR 语句的直接 lowering。
//!
//! 这个模块只处理“单条指令如何发射 HIR 语句”：普通赋值、调用、返回、vararg 和
//! set-list。它依赖 `ProtoLowering` 中已经准备好的 CFG / Dataflow /
//! StructureFacts / binding 映射，不重新识别 block 结构，也不接管 numeric/generic-for
//! 控制协议；这些 terminator 只能由 StructurePlan 选中的 loop owner 消费。
//! LuaJIT 没有精确 Lua 拼写的 `TypeGuard` 只保留带位置与效果说明的 residual；本模块不
//! 猜测可覆盖的 helper 语义，严格模式仍由后续 residual 合同拒绝。
//!
//! 输入形状：`CALL r0 ...` + 指令 def 映射，或已由 global protocol owner 认领的指令区间。
//! 输出形状：`t0 = f(args)`、`f(args)`，或 typed `HirStmt::GlobalDecl`。

use super::exprs::{
    expr_for_const, expr_for_reg_use, expr_for_value_operand, global_key_for_access,
    lower_binary_op, lower_call_root_handoff, lower_closure_capture, lower_closure_expr,
    lower_composite_factory_expr, lower_method_key, lower_raw_table_get_expr,
    lower_raw_table_set_call, lower_table_access_expr, lower_table_access_target, lower_unary_op,
    lower_upvalue_operand_expr, lower_upvalue_operand_target, lower_value_pack,
};
use super::global_decls::{GlobalDeclProtocol, GlobalDeclValues};
use super::helpers::{
    assign_stmt, binary_expr, concat_expr, decode_raw_string, return_stmt, unresolved_expr,
};
use super::lower::ProtoLowering;
use super::shared_closures::CompositeFactoryRef;
use crate::hir::common::{
    HirCallExpr, HirCallStmt, HirClose, HirExpr, HirGlobalDecl, HirLValue, HirLocalDecl,
    HirPackTail, HirStmt, HirTableAccess, HirTableConstructor, HirTableField, HirTableSetList,
    HirToBeClosed, HirUnaryExpr, HirValuePack, LocalId,
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
    if lowering
        .captured_shared_closures
        .effect_prefix_at(instr_ref)
    {
        return Some(Vec::new());
    }
    let stmts = lower_regular_instr_body(lowering, block, instr_ref, instr)?;
    if matches!(instr, LowInstr::Closure(_)) {
        return Some(stmts);
    }
    // 已证明的 Entry nil 在 CLOSE 窗口起点声明；不必等到首次 CLOSURE 才建 cell。
    let mut declarations = capture_empty_local_decl_stmts(lowering, instr_ref);
    if declarations.is_empty() {
        return Some(stmts);
    }
    declarations.extend(stmts);
    Some(declarations)
}

fn lower_regular_instr_body(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    instr: &LowInstr,
) -> Option<Vec<HirStmt>> {
    if lowering
        .bindings
        .numeric_binding_copies
        .contains(&instr_ref)
    {
        // Structure 已共同证明可写 for binding 与每轮入口 COPY；源码 for 在同槽重发它。
        // 其它 MOVE（包括数组 buffer 和前值快照）仍按原指令降低。
        return Some(Vec::new());
    }
    let mut stmts = match instr {
        LowInstr::Move(move_instr) => fixed_assign(
            lowering,
            instr_ref,
            vec![expr_for_reg_use(lowering, block, instr_ref, move_instr.src)],
        ),
        LowInstr::LoadNil(_instr) => fixed_assign(
            lowering,
            instr_ref,
            vec![HirExpr::Nil; lowering.dataflow.instr_defs[instr_ref.index()].len()],
        ),
        LowInstr::LoadBool(_)
            if lowering
                .captured_shared_closures
                .identity_initializers
                .contains_key(&instr_ref) =>
        {
            Vec::new()
        }
        LowInstr::LoadBool(load_bool) => {
            fixed_assign(lowering, instr_ref, vec![HirExpr::Boolean(load_bool.value)])
        }
        LowInstr::LoadConst(load_const) => fixed_assign(
            lowering,
            instr_ref,
            vec![lower_literal_initializer(
                lowering,
                instr_ref,
                expr_for_const(lowering.proto, load_const.value),
            )],
        ),
        LowInstr::LoadInteger(load_integer) => fixed_assign(
            lowering,
            instr_ref,
            vec![lower_literal_initializer(
                lowering,
                instr_ref,
                HirExpr::Integer(load_integer.value),
            )],
        ),
        LowInstr::LoadNumber(load_number) => fixed_assign(
            lowering,
            instr_ref,
            vec![lower_literal_initializer(
                lowering,
                instr_ref,
                HirExpr::Number(load_number.value),
            )],
        ),
        LowInstr::UnaryOp(unary) => fixed_assign(
            lowering,
            instr_ref,
            vec![HirExpr::Unary(Box::new(HirUnaryExpr {
                source_site: Some(crate::hir::common::HirSourceSite {
                    proto: lowering.id,
                    instr: instr_ref,
                }),
                op: lower_unary_op(unary.op),
                expr: expr_for_reg_use(lowering, block, instr_ref, unary.src),
            }))],
        ),
        LowInstr::BinaryOp(binary) => fixed_assign(
            lowering,
            instr_ref,
            vec![binary_expr(
                crate::hir::common::HirSourceSite {
                    proto: lowering.id,
                    instr: instr_ref,
                },
                lower_binary_op(binary.op),
                expr_for_value_operand(lowering, block, instr_ref, binary.lhs),
                expr_for_value_operand(lowering, block, instr_ref, binary.rhs),
            )],
        ),
        LowInstr::Concat(concat) => {
            let value = concat_expr(
                crate::hir::common::HirSourceSite {
                    proto: lowering.id,
                    instr: instr_ref,
                },
                (0..concat.src.len).map(|offset| {
                    expr_for_reg_use(
                        lowering,
                        block,
                        instr_ref,
                        Reg(concat.src.start.index() + offset),
                    )
                }),
            );
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
        LowInstr::SetUpvalue(set_upvalue) => {
            let mut stmt = assign_stmt(
                vec![lower_upvalue_operand_target(lowering, set_upvalue.dst)],
                vec![expr_for_value_operand(
                    lowering,
                    block,
                    instr_ref,
                    set_upvalue.src,
                )],
            );
            let HirStmt::Assign(assign) = &mut stmt else {
                unreachable!()
            };
            assign.upvalue_write_source = Some(crate::hir::common::HirSourceSite {
                proto: lowering.id,
                instr: instr_ref,
            });
            vec![stmt]
        }
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
                    match lowering.proto.constants.get(const_ref.index()) {
                        Some(crate::parser::RawLiteralConst::String(value)) => {
                            Some(decode_raw_string(value))
                        }
                        _ => None,
                    }
                }),
            }))]
        }
        LowInstr::TypeGuard(type_guard) => {
            let effect = if type_guard.kind.normalizes_subject() {
                "it can raise a LuaJIT-specific argument error and normalize the subject value"
            } else {
                "it can raise a LuaJIT-specific argument error without producing a Lua value"
            };
            let call = HirCallExpr {
                required_luau_inlining: None,
                source_site: None,
                argument_roots: Vec::new(),
                frame_root_ends: Vec::new(),
                callee: unresolved_expr(format!(
                    "LuaJIT builtin {} type guard at block {block}, instruction {instr_ref} has no exact Lua source spelling; {effect}",
                    type_guard.kind.label(),
                )),
                args: vec![expr_for_reg_use(
                    lowering,
                    block,
                    instr_ref,
                    type_guard.subject,
                )]
                .into(),
                method: false.into(),
                fastcall: None,
                method_key: None,
                callee_root_handoff: None,
                method_rewrite_transaction: None,
                plain_method_syntax: false,
                boolean_prewrite_arguments: Vec::new(),
            };
            if type_guard.kind.normalizes_subject() {
                fixed_assign(lowering, instr_ref, vec![HirExpr::Call(Box::new(call))])
            } else {
                vec![HirStmt::CallStmt(Box::new(HirCallStmt { call }))]
            }
        }
        LowInstr::NewTable(new_table) => fixed_assign(
            lowering,
            instr_ref,
            vec![super::exprs::expr_for_new_table(
                lowering.proto,
                new_table,
                crate::hir::common::HirSourceSite {
                    proto: lowering.id,
                    instr: instr_ref,
                },
            )],
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
            if let Some(snapshot) = lowering.self_value_capture_locals.get(&instr_ref).copied() {
                // Luau 在处理 CAPTURE VAL 前先把新 closure 写入 dst，因此 reflexive
                // capture 保存的是 closure 对象本身。先用独立 binding 固定这个快照，
                // 再写真实 dst；AST capture 元数据不保留 VM capture mode，且 dst 可重绑。
                debug_assert!(owner.is_none() && !consumed);
                let value = lower_closure_expr(lowering, block, instr_ref, closure);
                if lower_fixed_targets(lowering, instr_ref).as_slice()
                    == [HirLValue::Local(snapshot)]
                {
                    // 独立结果 Def 直接建立递归 local，没有需要额外快照的旧 dst cell。
                    stmts.push(HirStmt::LocalDecl(Box::new(HirLocalDecl {
                        bindings: vec![snapshot],
                        values: vec![value].into(),
                        initializer_merge_transaction: None,
                    })));
                    return Some(stmts);
                }
                stmts.extend(local_decl_stmts(vec![snapshot]));
                stmts.push(assign_stmt(vec![HirLValue::Local(snapshot)], vec![value]));
                stmts.extend(fixed_assign(
                    lowering,
                    instr_ref,
                    vec![HirExpr::LocalRef(snapshot)],
                ));
                return Some(stmts);
            }
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
                        initializer_merge_transaction: None,
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
            kind: close.kind,
            from_reg: close.from.index(),
            origins: lowering
                .structure
                .plan()
                .cleanup_tbc_origins(instr_ref)
                .into_iter()
                .flatten()
                .copied()
                .collect(),
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
    let roots = lowering
        .promotion_facts
        .copy_root_before_releases(instr_ref);
    if !roots.is_empty() {
        // 异槽 NOT 在读完输入后写 Boolean；它不调用元方法，也不需要先清除目标根。
        let boolean_overwrite = (matches!(instr, LowInstr::LoadBool(_))
            || matches!(instr, LowInstr::UnaryOp(unary)
                if unary.op == crate::transformer::UnaryOpKind::Not && unary.src != unary.dst))
        .then(|| {
            let def = *lowering.dataflow.instr_defs[instr_ref.index()].first()?;
            let temp = lowering.bindings.fixed_temps[def.index()];
            Some((
                lowering.bindings.lvalue_for_temp(temp),
                lowering.promotion_facts.trusted_temp_home_slot(temp)?,
            ))
        })
        .flatten();
        let declared_nil_locals = if matches!(instr, LowInstr::LoadNil(_)) {
            lowering.dataflow.instr_defs[instr_ref.index()]
                .iter()
                .filter_map(|def| {
                    lowering
                        .bindings
                        .temp_decl_locals
                        .get(&lowering.bindings.fixed_temps[def.index()])
                        .copied()
                })
                .collect::<std::collections::BTreeSet<_>>()
        } else {
            Default::default()
        };
        let roots = roots.iter().copied()
            // 原 Boolean 写已更新同一 binding/home，且没有 RHS 观察事件；
            // 不提前发 nil 清除，也不能让其后无读取的 Boolean Def 被误删。
            .filter(|temp| boolean_overwrite.as_ref().is_none_or(|(target, home)| {
                lowering.bindings.lvalue_for_temp(*temp) != *target
                    || lowering.promotion_facts.trusted_temp_home_slot(*temp) != Some(*home)
            }))
            .map(|temp| lowering.bindings.lvalue_for_temp(temp))
            // 原 nil 声明已在同一指令清空这个槽；不能在声明前另写一次未绑定的 local。
            .filter(|target| !matches!(target, HirLValue::Local(local) if declared_nil_locals.contains(local)))
            .collect::<Vec<_>>();
        if !roots.is_empty() {
            let count = roots.len();
            stmts.insert(0, assign_stmt(roots, vec![HirExpr::Nil; count]));
        }
    }
    let roots = lowering.promotion_facts.copy_root_after_releases(instr_ref);
    for &temp in roots {
        let HirLValue::Local(local) = lowering.bindings.lvalue_for_temp(temp) else {
            return None;
        };
        stmts.push(HirStmt::LocalRootRelease(local));
    }
    Some(stmts)
}

fn env_upvalue_is_consumed_by_global_accesses(
    lowering: &ProtoLowering<'_>,
    instr_ref: InstrRef,
    get_upvalue: &crate::transformer::GetUpvalueInstr,
) -> bool {
    if !matches!(get_upvalue.src, crate::transformer::UpvalueOperand::Env(_)) {
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
                global_key_for_access(lowering, use_block, site.instr, access.0, access.1).is_some()
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
        LowInstr::Return(ret) => Some(vec![return_stmt(
            lower_value_pack(lowering, block, instr_ref, ret.values),
            lowering.promotion_facts.return_frame_source(instr_ref),
            lowering
                .pending_frame_returns
                .contains(&instr_ref)
                .then_some(instr_ref),
        )]),
        LowInstr::TailCall(tail_call) => {
            let method_key = lower_method_key(lowering, tail_call.method_name);
            let callee = expr_for_reg_use(lowering, block, instr_ref, tail_call.callee);
            Some(vec![return_stmt(
                HirValuePack::expanding(
                    Vec::new(),
                    HirPackTail::open(HirExpr::Call(Box::new(HirCallExpr {
                        required_luau_inlining: None,
                        source_site: Some(crate::hir::common::HirSourceSite {
                            proto: lowering.id,
                            instr: instr_ref,
                        }),
                        argument_roots: Vec::new(),
                        frame_root_ends: Vec::new(),
                        callee,
                        args: lower_value_pack(lowering, block, instr_ref, tail_call.args),
                        method: matches!(tail_call.kind, CallKind::Method).into(),
                        fastcall: match tail_call.kind {
                            CallKind::FastCall(args) => Some(args),
                            CallKind::Normal | CallKind::Method => None,
                        },
                        method_key,
                        // 尾调用保留 SELF 双端身份，原 owner 不为它签发 post-call 根。
                        callee_root_handoff: lower_call_root_handoff(
                            lowering,
                            instr_ref,
                            tail_call.kind,
                        ),
                        method_rewrite_transaction: None,
                        plain_method_syntax: false,
                        boolean_prewrite_arguments: Vec::new(),
                    }))),
                ),
                None,
                lowering
                    .pending_frame_returns
                    .contains(&instr_ref)
                    .then_some(instr_ref),
            )])
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
    let initializer_debug_scope = lowering
        .structure
        .debug_bindings()
        .for_value(lowering.dataflow.use_value(instr_ref, set_list.base))
        .filter(|scope| scope.initializer_end_instr == Some(instr_ref))
        .map(|scope| scope.scope);
    vec![HirStmt::TableSetList(Box::new(HirTableSetList {
        source_site: Some(crate::hir::common::HirSourceSite {
            proto: lowering.id,
            instr: instr_ref,
        }),
        base: expr_for_reg_use(lowering, block, instr_ref, set_list.base),
        start_index: set_list.start_index,
        values,
        initializer_debug_scope,
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
        required_luau_inlining: None,
        source_site: Some(crate::hir::common::HirSourceSite {
            proto: lowering.id,
            instr: instr_ref,
        }),
        argument_roots: Vec::new(),
        frame_root_ends: Vec::new(),
        callee,
        args,
        method: false.into(),
        fastcall: None,
        method_key: None,
        callee_root_handoff: None,
        method_rewrite_transaction: None,
        plain_method_syntax: false,
        boolean_prewrite_arguments: Vec::new(),
    }))
}

fn lower_call(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    call: &crate::transformer::CallInstr,
) -> Vec<HirStmt> {
    let results = call.results;
    let call_expr = lower_call_expr(lowering, block, instr_ref, call);

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

fn lower_call_expr(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    call: &crate::transformer::CallInstr,
) -> HirCallExpr {
    let method_key = lower_method_key(lowering, call.method_name);
    let callee = expr_for_reg_use(lowering, block, instr_ref, call.callee);
    HirCallExpr {
        required_luau_inlining: None,
        source_site: Some(crate::hir::common::HirSourceSite {
            proto: lowering.id,
            instr: instr_ref,
        }),
        argument_roots: lowering.promotion_facts.call_argument_roots(instr_ref),
        frame_root_ends: lowering.promotion_facts.call_frame_root_ends(instr_ref),
        callee,
        args: lower_value_pack(lowering, block, instr_ref, call.args),
        method: matches!(call.kind, CallKind::Method).into(),
        fastcall: match call.kind {
            CallKind::FastCall(args) => Some(args),
            CallKind::Normal | CallKind::Method => None,
        },
        method_key,
        callee_root_handoff: lower_call_root_handoff(lowering, instr_ref, call.kind),
        method_rewrite_transaction: None,
        plain_method_syntax: false,
        boolean_prewrite_arguments: Vec::new(),
    }
}

pub(super) fn lower_global_decl_owner(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    protocol: &GlobalDeclProtocol,
) -> Option<HirStmt> {
    let values = match &protocol.values {
        GlobalDeclValues::FixedCall(results) => {
            let LowInstr::Call(call) = lowering.proto.instrs.get(instr_ref.index())? else {
                return None;
            };
            if call.results != ResultPack::Fixed(*results) {
                return None;
            }
            let call = HirExpr::Call(Box::new(lower_call_expr(lowering, block, instr_ref, call)));
            if results.len == 1 {
                HirValuePack::fixed(vec![call])
            } else {
                HirValuePack::expanding(Vec::new(), HirPackTail::exact(call, results.len))
            }
        }
        GlobalDeclValues::ValueUses(values) => HirValuePack::fixed(
            values
                .iter()
                .map(|value| expr_for_reg_use(lowering, block, value.instr, value.reg))
                .collect(),
        ),
    };
    Some(HirStmt::GlobalDecl(Box::new(HirGlobalDecl {
        names: protocol.names.clone(),
        values,
    })))
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

/// 已证相邻的 NaN capture 初始化保留不透明字段读取，避免目标编译器删除捕获。
/// 合成表和读取不继承原 VM 操作来源；原标量 binding 的 SharedClosureIdentity 禁止折回常量。
pub(in crate::hir::analyze) fn lower_literal_initializer(
    lowering: &ProtoLowering<'_>,
    instr: InstrRef,
    value: HirExpr,
) -> HirExpr {
    if let Some(initializer) = lowering
        .captured_shared_closures
        .identity_initializers
        .get(&instr)
    {
        return HirExpr::Call(Box::new(HirCallExpr {
            required_luau_inlining: Some(crate::hir::common::HirSourceSite {
                proto: lowering.id,
                instr,
            }),
            source_site: None,
            argument_roots: Vec::new(),
            frame_root_ends: Vec::new(),
            callee: HirExpr::LocalRef(initializer.callee),
            args: vec![value].into(),
            method: false.into(),
            fastcall: None,
            method_key: None,
            callee_root_handoff: None,
            method_rewrite_transaction: None,
            plain_method_syntax: false,
            boolean_prewrite_arguments: Vec::new(),
        }));
    }
    if !lowering
        .captured_shared_closures
        .has_literal_initializer(instr)
    {
        return value;
    }
    HirExpr::TableAccess(Box::new(HirTableAccess {
        sources: Default::default(),
        metamethod_free: true,
        base: HirExpr::TableConstructor(Box::new(HirTableConstructor {
            fields: vec![HirTableField::Array(value)],
            ..Default::default()
        })),
        key: HirExpr::Integer(1),
        method_setup_protocol: None,
    }))
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
        fields.push(HirTableField::Array(match capture {
            Ok(capture) => capture.binding.expr(),
            Err(error) => HirExpr::Unresolved(Box::new(error)),
        }));
    }
    let table = HirExpr::TableConstructor(Box::new(HirTableConstructor {
        sources: Default::default(),
        allocation: Default::default(),
        implicit_template_fields: Default::default(),
        fields,
        trailing_multivalue: None,
    }));
    // 单个快照只读取合成表一次，表本身从不逃逸，所捕获值仍由
    // 快照持有；没有保留独立 box binding 的身份或生命周期要求。仍在原 capture 锚点分配并读取，不能
    // 提前到原 NaN 写入之前，也不能将不透明读取折回常量。
    let Some(box_local) = barrier.box_local else {
        return vec![HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: locals,
            values: vec![HirExpr::TableAccess(Box::new(HirTableAccess {
                sources: Default::default(),
                metamethod_free: true,
                base: table,
                key: HirExpr::Integer(1),
                method_setup_protocol: None,
            }))]
            .into(),
            initializer_merge_transaction: None,
        }))];
    };
    let snapshots = locals
        .iter()
        .enumerate()
        .map(|(index, _)| {
            HirExpr::TableAccess(Box::new(HirTableAccess {
                sources: Default::default(),
                metamethod_free: false,
                base: HirExpr::LocalRef(box_local),
                key: HirExpr::Integer((index + 1) as i64),
                method_setup_protocol: None,
            }))
        })
        .collect::<Vec<_>>();
    vec![
        HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: vec![box_local],
            values: vec![table].into(),
            initializer_merge_transaction: None,
        })),
        HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: locals,
            values: snapshots.into(),
            initializer_merge_transaction: None,
        })),
    ]
}

fn fixed_assign(
    lowering: &ProtoLowering<'_>,
    instr_ref: InstrRef,
    values: impl Into<HirValuePack>,
) -> Vec<HirStmt> {
    let values = values.into();
    let decl_locals = lowering.dataflow.instr_defs[instr_ref.index()]
        .iter()
        .filter_map(|def| {
            lowering
                .bindings
                .temp_decl_locals
                .get(&lowering.bindings.fixed_temps[def.index()])
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
            initializer_merge_transaction: None,
        }))]
    } else {
        let declared = decl_locals
            .iter()
            .copied()
            .collect::<std::collections::BTreeSet<_>>();
        let mut stmts = local_decl_stmts(decl_locals);
        if matches!(
            lowering.proto.instrs[instr_ref.index()],
            LowInstr::LoadNil(_)
        ) {
            if let Some(HirStmt::LocalDecl(decl)) = stmts.first_mut() {
                decl.values = vec![HirExpr::Nil; decl.bindings.len()].into();
            }
            // LOADNIL 没有求值事件；新 local 声明中的 nil 已消费它自己的原槽写。
            // 混合组里的其它目标仍逐一保留，不能为同一 local 再重复一次 nil 赋值。
            let remaining = targets
                .into_iter()
                .filter(
                    |target| !matches!(target, HirLValue::Local(local) if declared.contains(local)),
                )
                .collect::<Vec<_>>();
            if !remaining.is_empty() {
                let count = remaining.len();
                stmts.push(assign_stmt(remaining, vec![HirExpr::Nil; count]));
            }
        } else {
            stmts.push(assign_stmt(targets, values));
        }
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
            initializer_merge_transaction: None,
        }))]
    }
}

fn lower_fixed_targets(lowering: &ProtoLowering<'_>, instr_ref: InstrRef) -> Vec<HirLValue> {
    let block = lowering.cfg.instr_to_block[instr_ref.index()];
    lowering.dataflow.instr_defs[instr_ref.index()]
        .iter()
        .map(|def| {
            // for 的可见 binding 是当前 body 内该寄存器的词法 owner；显式写入也必须
            // 回到同一个 local。只在读取侧映射会把 `i = value` 留成无人读取的 temp，
            // 随后 dead-temp 清理会静默删除真实赋值。
            lowering.bindings.lvalue_for_reg_result(
                block,
                lowering.dataflow.def_reg(*def),
                lowering.bindings.fixed_temps[def.index()],
            )
        })
        .collect()
}
