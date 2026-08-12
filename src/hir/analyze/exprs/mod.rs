//! 这个文件集中处理 low-ir 到 HIR 表达式世界的映射。
//!
//! HIR 的主流程需要频繁把寄存器、常量、表访问和分支条件翻译成表达式节点，如果
//! 这些逻辑散落在主 lowering 里，后面做短路恢复、临时变量消解时会很难判断修改边界。
//! 因此这里专门承载“值如何解释”的规则，让 `analyze/mod.rs` 更多只关心语句和控制流骨架。

mod access;
mod branch;
mod defs;
mod packs;
mod regs;

use crate::ast::is_lua_identifier_name;
use crate::hir::common::{
    HirBinaryExpr, HirBinaryOpKind, HirCallExpr, HirCapture, HirCaptureMode, HirClosureExpr,
    HirExpr, HirGlobalRef, HirLValue, HirPackTail, HirTableAccess, HirUnaryExpr, HirUnaryOpKind,
    UpvalueId,
};
use crate::parser::RawLiteralConst;
use crate::structure::BlockRef;
use crate::structure::{DefId, SsaValue};
use crate::transformer::{
    AccessBase, AccessKey, BinaryOpKind, BranchCond, BranchPredicate, BranchSubject, CallKind,
    CaptureSource, ClosureInstr, CondOperand, ConstRef, InstrRef, LowInstr, LoweredProto,
    MethodNameHint, Reg, ResultPack, UnaryOpKind, UpvalueOperand, ValueOperand,
};

pub(super) use self::access::{
    expr_for_const, expr_for_value_operand, global_name_for_access, lower_raw_table_get_expr,
    lower_raw_table_set_call, lower_table_access_expr, lower_table_access_target,
    lower_upvalue_operand_expr, lower_upvalue_operand_target,
};
use self::access::{
    expr_for_value_operand_single_eval_pure_operand, lower_raw_table_get_expr_inline,
    lower_raw_table_get_expr_single_eval, lower_table_access_expr_inline,
    lower_table_access_expr_single_eval,
};
pub(super) use self::branch::{
    lower_binary_op, lower_branch_cond, lower_branch_subject, lower_branch_subject_single_eval,
    lower_unary_op,
};
pub(super) use self::defs::expr_for_direct_literal_def;
use self::defs::expr_for_dup_safe_fixed_def;
pub(super) use self::defs::{expr_for_fixed_def, expr_for_fixed_def_single_eval};
pub(super) use self::packs::lower_value_pack;
use self::packs::lower_value_pack_single_eval;
pub(super) use self::regs::block_is_absorbed_decision;
pub(super) use self::regs::{
    expr_for_reg_at_block_exit, expr_for_reg_use, expr_for_ssa_value, lower_closure_capture,
};
use self::regs::{
    expr_for_reg_use_dup_safe, expr_for_reg_use_inline,
    expr_for_reg_use_single_eval_with_call_policy,
};
use super::helpers::{concat_expr, decode_raw_string, raw_lua_string, unresolved_expr};
use super::lower::ProtoLowering;
use super::shared_closures::CompositeFactoryRef;

pub(super) fn lower_closure_expr(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    closure: &ClosureInstr,
) -> HirExpr {
    if let Some(factory) = lowering.shared_closure_replacement(instr_ref) {
        return HirExpr::Call(Box::new(HirCallExpr {
            callee: HirExpr::LocalRef(lowering.shared_factory_local(factory)),
            args: Default::default(),
            method: false,
            method_name: None,
        }));
    }
    if let Some(local) = lowering.shared_closure_local(closure.creation) {
        return HirExpr::LocalRef(local);
    }
    lower_plain_closure_expr(lowering, block, instr_ref, closure)
}

pub(super) fn lower_plain_closure_expr(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    closure: &ClosureInstr,
) -> HirExpr {
    HirExpr::Closure(Box::new(HirClosureExpr {
        proto: lowering.child_refs[closure.proto.index()],
        captures: closure
            .captures
            .iter()
            .map(|capture| {
                lower_closure_capture(lowering, block, instr_ref, closure.dst, capture.source)
            })
            .collect(),
    }))
}

pub(super) fn lower_composite_factory_expr(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    closure: &ClosureInstr,
    factory: CompositeFactoryRef,
) -> HirExpr {
    let plan = lowering.captured_shared_closures.composite_plan(factory);
    HirExpr::Closure(Box::new(HirClosureExpr {
        proto: lowering.captured_shared_closures.composite_proto(factory),
        captures: lower_factory_captures(
            lowering,
            block,
            instr_ref,
            closure.dst,
            factory,
            plan.outer_captures.iter().copied(),
        ),
    }))
}

fn lower_factory_captures(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    dst: Reg,
    factory: CompositeFactoryRef,
    sources: impl IntoIterator<Item = CaptureSource>,
) -> Vec<HirCapture> {
    let barrier = lowering.captured_shared_closures.capture_barrier(factory);
    sources
        .into_iter()
        .enumerate()
        .map(|(index, source)| {
            barrier
                .and_then(|barrier| barrier.snapshots.get(index).copied().flatten())
                .map_or_else(
                    || lower_closure_capture(lowering, block, instr_ref, dst, source),
                    |snapshot| HirCapture {
                        mode: HirCaptureMode::ByValue,
                        value: HirExpr::LocalRef(snapshot),
                    },
                )
        })
        .collect()
}

/// `Open(start)` 不是“只有一个开放尾值”，而是“从 start 到 top 的整段值包”。
///
/// 因此这里会先找出真正的开放尾部起点：若 open def 从更晚的寄存器开始，那么
/// `start..tail_start-1` 这一段仍然要按固定值逐个吐出来，最后再接上 open tail。
fn resolve_open_pack_tail(
    lowering: &ProtoLowering<'_>,
    instr_ref: InstrRef,
    start_reg: Reg,
) -> Option<(Reg, HirPackTail)> {
    resolve_open_pack_tail_with_policy(lowering, instr_ref, start_reg, false)
}

fn resolve_open_pack_tail_with_policy(
    lowering: &ProtoLowering<'_>,
    instr_ref: InstrRef,
    start_reg: Reg,
    single_eval: bool,
) -> Option<(Reg, HirPackTail)> {
    let sources = lowering.dataflow.open_use_sources_at(instr_ref);
    let defs = sources.defs();
    if !sources.has_entry() && defs.len() == 1 {
        let def = defs.iter().next()?;
        let open_def = lowering.dataflow.open_defs.get(def.index())?;
        if open_def.start_reg.index() < start_reg.index() {
            return None;
        }
        if !lowering.owns_open_pack(*def, instr_ref) {
            return None;
        }
        return Some((
            open_def.start_reg,
            pack_tail_for_open_def(lowering, *def, single_eval)?,
        ));
    }

    if sources.has_entry()
        && defs.is_empty()
        && lowering.proto.signature.is_vararg
        && start_reg.index() <= usize::from(lowering.proto.signature.num_params)
    {
        return Some((
            Reg(usize::from(lowering.proto.signature.num_params)),
            HirPackTail::open(HirExpr::VarArg),
        ));
    }

    None
}

/// `single_eval` 版本：在短路恢复等已被吸收的 block 里，open temp 不会被物化，
/// 这里尝试把 open def 直接内联成多返回 call 表达式。
fn resolve_open_pack_tail_single_eval(
    lowering: &ProtoLowering<'_>,
    instr_ref: InstrRef,
    start_reg: Reg,
) -> Option<(Reg, HirPackTail)> {
    resolve_open_pack_tail_with_policy(lowering, instr_ref, start_reg, true)
}

/// 把一个 open def (多返回 call / vararg) 直接降成 HIR 表达式。
fn pack_tail_for_open_def(
    lowering: &ProtoLowering<'_>,
    open_def_id: crate::structure::OpenDefId,
    single_eval: bool,
) -> Option<HirPackTail> {
    let open_def = lowering.dataflow.open_defs.get(open_def_id.index())?;
    let instr = lowering.proto.instrs.get(open_def.instr.index())?;
    match instr {
        LowInstr::Call(call) if matches!(call.results, ResultPack::Open(_)) => {
            let method_name = lower_method_name(lowering, call.method_name);
            let callee = if single_eval {
                expr_for_reg_use_single_eval_with_call_policy(
                    lowering,
                    open_def.block,
                    open_def.instr,
                    call.callee,
                    false,
                )
            } else {
                expr_for_reg_use(lowering, open_def.block, open_def.instr, call.callee)
            };
            Some(HirPackTail::open(HirExpr::Call(Box::new(HirCallExpr {
                callee,
                args: if single_eval {
                    lower_value_pack_single_eval(
                        lowering,
                        open_def.block,
                        open_def.instr,
                        call.args,
                    )
                } else {
                    lower_value_pack(lowering, open_def.block, open_def.instr, call.args)
                },
                method: matches!(call.kind, CallKind::Method),
                method_name,
            }))))
        }
        LowInstr::VarArg(vararg) if matches!(vararg.results, ResultPack::Open(_)) => {
            Some(HirPackTail::open(HirExpr::VarArg))
        }
        _ => None,
    }
}

pub(crate) fn expr_for_entry_reg(lowering: &ProtoLowering<'_>, reg: Reg) -> HirExpr {
    if reg.index() < lowering.bindings.params.len() {
        HirExpr::ParamRef(lowering.bindings.params[reg.index()])
    } else if let Some(local) = lowering.bindings.entry_local_regs.get(&reg) {
        HirExpr::LocalRef(*local)
    } else {
        // Lua 调用帧里的寄存器槽默认是 nil。数据流没有到达定义、bindings 也没有
        // 入口 local 身份时，这不是“无法表达”的值，而是源码层面的 nil。
        HirExpr::Nil
    }
}

fn reg_in_range(range: crate::transformer::RegRange, reg: Reg) -> bool {
    reg.index() >= range.start.index() && reg.index() < range.start.index() + range.len
}

pub(super) fn lower_method_name(
    lowering: &ProtoLowering<'_>,
    method_name: Option<MethodNameHint>,
) -> Option<String> {
    let const_ref = method_name?.const_ref;
    match lowering
        .proto
        .constants
        .common
        .literals
        .get(const_ref.index())
    {
        Some(RawLiteralConst::String(value)) => {
            let name = decode_raw_string(value);
            is_lua_identifier_name(&name, lowering.target.version).then_some(name)
        }
        _ => None,
    }
}
