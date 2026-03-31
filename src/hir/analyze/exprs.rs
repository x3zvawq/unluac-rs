//! 这个文件集中处理 low-ir 到 HIR 表达式世界的映射。
//!
//! HIR 的主流程需要频繁把寄存器、常量、表访问和分支条件翻译成表达式节点，如果
//! 这些逻辑散落在主 lowering 里，后面做短路恢复、临时变量消解时会很难判断修改边界。
//! 因此这里专门承载“值如何解释”的规则，让 `analyze.rs` 更多只关心语句和控制流骨架。

mod access;
mod branch;
mod defs;
mod packs;
mod regs;

use crate::cfg::BlockRef;
use crate::cfg::{DefId, SsaValue};
use crate::hir::common::{
    HirBinaryExpr, HirBinaryOpKind, HirCallExpr, HirCapture, HirClosureExpr, HirExpr, HirGlobalRef,
    HirLValue, HirTableAccess, HirUnaryExpr, HirUnaryOpKind, UpvalueId,
};
use crate::parser::RawLiteralConst;
use crate::transformer::{
    AccessBase, AccessKey, BinaryOpKind, BranchCond, BranchOperands, BranchPredicate, CallKind,
    CondOperand, ConstRef, InstrRef, LowInstr, LoweredProto, MethodNameHint, Reg, ResultPack,
    UnaryOpKind, ValueOperand,
};

pub(super) use self::access::{
    expr_for_const, expr_for_value_operand, lower_table_access_expr, lower_table_access_target,
};
use self::access::{expr_for_value_operand_inline, lower_table_access_expr_inline};
pub(super) use self::branch::{
    lower_binary_op, lower_branch_cond, lower_branch_subject, lower_branch_subject_inline,
    lower_branch_subject_single_eval, lower_unary_op,
};
pub(super) use self::defs::{expr_for_dup_safe_fixed_def, expr_for_fixed_def, is_multiret_results};
use self::packs::lower_value_pack_single_eval;
pub(super) use self::packs::{lower_value_pack, lower_value_pack_components};
pub(super) use self::regs::{
    expr_for_closure_capture, expr_for_reg_at_block_entry, expr_for_reg_at_block_exit,
    expr_for_reg_use,
};
use self::regs::{expr_for_reg_use_inline, expr_for_reg_use_single_eval};
use super::ProtoLowering;
use super::helpers::{concat_expr, decode_raw_string, unresolved_expr};

/// `Open(start)` 不是“只有一个开放尾值”，而是“从 start 到 top 的整段值包”。
///
/// 因此这里会先找出真正的开放尾部起点：若 open def 从更晚的寄存器开始，那么
/// `start..tail_start-1` 这一段仍然要按固定值逐个吐出来，最后再接上 open tail。
fn resolve_open_pack_tail(
    lowering: &ProtoLowering<'_>,
    instr_ref: InstrRef,
    start_reg: Reg,
) -> Option<(Reg, HirExpr)> {
    let defs = lowering.dataflow.open_use_defs_at(instr_ref);
    if defs.len() == 1 {
        let def = defs
            .iter()
            .next()
            .expect("len checked above, exactly one reaching open def exists");
        let open_def = lowering.dataflow.open_defs.get(def.index())?;
        if open_def.start_reg.index() < start_reg.index() {
            return None;
        }
        return Some((
            open_def.start_reg,
            HirExpr::TempRef(lowering.bindings.open_temps[def.index()]),
        ));
    }

    if defs.is_empty()
        && lowering.proto.signature.is_vararg
        && start_reg.index() == usize::from(lowering.proto.signature.num_params)
    {
        return Some((start_reg, HirExpr::VarArg));
    }

    None
}

fn entry_reg_expr(lowering: &ProtoLowering<'_>, reg: Reg) -> HirExpr {
    if reg.index() < lowering.bindings.params.len() {
        HirExpr::ParamRef(lowering.bindings.params[reg.index()])
    } else if let Some(local) = lowering.bindings.entry_local_regs.get(&reg) {
        HirExpr::LocalRef(*local)
    } else {
        unresolved_expr(format!("entry-reg r{}", reg.index()))
    }
}

fn loop_local_for_reg(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    reg: Reg,
) -> Option<crate::hir::common::LocalId> {
    lowering
        .bindings
        .block_local_regs
        .get(&block)
        .and_then(|locals| locals.get(&reg))
        .copied()
}

fn fixed_def_for_reg(lowering: &ProtoLowering<'_>, instr_ref: InstrRef, reg: Reg) -> Option<DefId> {
    lowering.dataflow.instr_def_for_reg(instr_ref, reg)
}

fn reg_in_range(range: crate::transformer::RegRange, reg: Reg) -> bool {
    reg.index() >= range.start.index() && reg.index() < range.start.index() + range.len
}

pub(super) fn lower_method_name(
    proto: &LoweredProto,
    method_name: Option<MethodNameHint>,
) -> Option<String> {
    let const_ref = method_name?.const_ref;
    match proto.constants.common.literals.get(const_ref.index()) {
        Some(RawLiteralConst::String(value)) => Some(decode_raw_string(value)),
        _ => None,
    }
}
