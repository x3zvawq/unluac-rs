//! 这个子模块负责把寄存器读取解释成 local/temp/entry 值引用。
//!
//! 它依赖 Dataflow 的 `use_values` 和 bindings 层已经分配好的 temp/local 身份，不会在这里
//! 重新做 SSA 合流判定。
//! 例如：某条指令读取 `r0`，若对应唯一 `TempId`，这里会直接降成 `TempRef(t0)`。

use super::*;
use crate::hir::HirUnresolvedExpr;

pub(crate) fn expr_for_reg_use(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    reg: Reg,
) -> HirExpr {
    lowering.bindings.expr_for_reg_value(block, reg, || {
        expr_for_ssa_value(lowering, lowering.dataflow.use_value(instr_ref, reg))
    })
}

/// 冻结叶值保留 SSA 来源，但在读取位置消费已有循环 binding；不能引用未发射的 dispatch temp。
pub(in crate::hir::analyze) fn expr_for_ssa_value_in_block(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    value: SsaValue,
) -> Option<HirExpr> {
    let reg = lowering.ssa_reg(value)?;
    Some(
        lowering
            .bindings
            .expr_for_reg_value(block, reg, || expr_for_ssa_value(lowering, value)),
    )
}

pub(crate) fn lower_closure_capture(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    dst: Reg,
    source: crate::transformer::CaptureSource,
) -> Result<HirCapture, HirUnresolvedExpr> {
    let (mode, value) = match source {
        crate::transformer::CaptureSource::ByValue(reg) if reg == dst => (
            HirCaptureMode::ByValue,
            HirExpr::LocalRef(
                *lowering
                    .self_value_capture_locals
                    .get(&instr_ref)
                    .expect("self value capture must have a snapshot local"),
            ),
        ),
        crate::transformer::CaptureSource::ByValue(reg) => (
            HirCaptureMode::ByValue,
            expr_for_reg_use(lowering, block, instr_ref, reg),
        ),
        crate::transformer::CaptureSource::ByReference(reg) if reg == dst => (
            HirCaptureMode::ByReference,
            closure_result_expr(lowering, block, instr_ref),
        ),
        crate::transformer::CaptureSource::ByReference(reg) => {
            if let Some(target) = lowering.bindings.closure_capture_target(instr_ref, reg) {
                return capture_from_expr(instr_ref, HirCaptureMode::ByReference, target.expr());
            }
            // 同 epoch 的后续写、前向声明由 captured_slots 签发 cell 身份。
            // 其余 capture 保留原 reaching 值；不能按寄存器前向扫描并越过 Close。
            (
                HirCaptureMode::ByReference,
                expr_for_reg_use(lowering, block, instr_ref, reg),
            )
        }
        crate::transformer::CaptureSource::Upvalue(upvalue) => (
            HirCaptureMode::ByReference,
            HirExpr::UpvalueRef(UpvalueId(upvalue.index())),
        ),
    };
    capture_from_expr(instr_ref, mode, value)
}

fn capture_from_expr(
    instr: InstrRef,
    mode: HirCaptureMode,
    value: HirExpr,
) -> Result<HirCapture, HirUnresolvedExpr> {
    let binding = crate::hir::HirBinding::from_expr(&value).ok_or_else(|| HirUnresolvedExpr {
        summary: format!("closure at {instr} has no parent binding for capture {value:?}"),
    })?;
    Ok(HirCapture { mode, binding })
}

fn closure_result_expr(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
) -> HirExpr {
    lowering.dataflow.instr_defs[instr_ref.index()]
        .first()
        .map(|def| {
            lowering.bindings.expr_for_fixed_def(
                block,
                lowering.dataflow.def_reg(*def),
                lowering.bindings.fixed_temps[def.index()],
            )
        })
        .unwrap_or_else(|| {
            HirExpr::Unresolved(Box::new(HirUnresolvedExpr {
                summary: format!("closure at {instr_ref} has no fixed result"),
            }))
        })
}

/// 某些 `goto + label` 形状需要读取“离开 block 时这个寄存器的稳定值”。
///
/// 这和普通 `expr_for_reg_use` 不同：phi edge copy 不一定对应某条真实 use，
/// 也不能只看 `incoming.defs`，否则像“从 inner loop header 直接跳回 outer header”
/// 这种边会把 block 入口 phi 的稳定值丢掉。
pub(crate) fn expr_for_reg_at_block_exit(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    reg: Reg,
) -> HirExpr {
    if let Some(local) = lowering.bindings.local_for_reg_in_block(block, reg) {
        return HirExpr::LocalRef(local);
    }

    expr_for_ssa_value(lowering, lowering.dataflow.block_exit_value(block, reg))
}

/// 当值恢复跨过被整体吸收的 branch 区域时，内部 leaf/node block 可能不会单独物化。
///
/// 这里允许沿着单一 `DefId` 继续下钻，但只展开“可以安全重复求值”的定义。
/// 像 `call/newtable/gettable` 这类一旦重复展开就可能改写求值次数或对象身份的值，
/// 仍然退回已有 temp，避免 HIR 先天带入错误语义。
pub(crate) fn expr_for_reg_use_inline(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    reg: Reg,
) -> HirExpr {
    if let Some(local) = lowering.bindings.local_for_reg_in_block(block, reg) {
        return HirExpr::LocalRef(local);
    }
    match lowering.dataflow.use_value(instr_ref, reg) {
        SsaValue::Entry(entry_reg) => expr_for_entry_reg(lowering, entry_reg),
        SsaValue::Def(def) => {
            let temp = lowering.bindings.fixed_temps[def.index()];
            if lowering.bindings.captured_temp_targets.contains_key(&temp) {
                return lowering.bindings.expr_for_temp(temp);
            }
            expr_for_dup_safe_fixed_def(lowering, def)
                .unwrap_or_else(|| lowering.bindings.expr_for_temp(temp))
        }
        SsaValue::Phi(phi) => lowering.bindings.expr_for_phi(phi),
    }
}

/// dup-safe 重建会把表达式移到原定义之后；按引用捕获的寄存器可能在任意调用中改值，
/// 因此只能由定义点 temp 保存快照，不能把当前 binding 重新读成旧 def 的操作数。
pub(crate) fn expr_for_reg_use_dup_safe(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    reg: Reg,
) -> Option<HirExpr> {
    (!lowering.dataflow.reg_is_reference_captured(reg))
        .then(|| expr_for_reg_use_inline(lowering, block, instr_ref, reg))
}

/// `single-eval` 只承诺“这次求值可以直接表达出来”，并不承诺“可以重复复制很多次”。
///
/// 这条语义专门服务短路节点的单次 test：像 `call(...)` 这种不可复制但可单次出现的值，
/// 在这里应该优先恢复成本体表达式，而不是先掉回 temp。
///
/// 纯表达式壳层（如 `not call()` / `call() + 1`）本身不会额外观察 call 的结果，
/// 被短路 header 整体吸收时也不会单独物化这些中间 temp。因此
/// `allow_call_consumed_by_pure_wrapper` 只应在 unary/binary/concat 这类纯壳层 operand
/// 中打开；普通 call-arg / table-base 仍传 `false`。
pub(crate) fn expr_for_reg_use_single_eval_with_call_policy(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    reg: Reg,
    allow_call_consumed_by_pure_wrapper: bool,
) -> HirExpr {
    let decision_owner = absorbed_decision_owner(lowering, block);
    let absorbed = decision_owner.is_some();
    // 被整体吸收的 decision 可以省掉内部机械 temp，但不能省掉按引用 capture 的
    // 词法 local：任意 child call 都可能经 upvalue 改写它，旧 SSA def 不是调用后的值。
    if let Some(local) = lowering.bindings.local_for_reg_in_block(block, reg)
        && (!absorbed || lowering.dataflow.reg_is_reference_captured(reg))
    {
        return HirExpr::LocalRef(local);
    }
    match lowering.dataflow.use_value(instr_ref, reg) {
        SsaValue::Entry(entry_reg) => lowering
            .bindings
            .local_for_reg_in_block(block, reg)
            .map(HirExpr::LocalRef)
            .unwrap_or_else(|| expr_for_entry_reg(lowering, entry_reg)),
        SsaValue::Def(def) => {
            let temp = lowering.bindings.fixed_temps[def.index()];
            if lowering.bindings.captured_temp_targets.contains_key(&temp) {
                return lowering.bindings.expr_for_temp(temp);
            }
            let def_block = lowering.dataflow.def_block(def);
            let def_is_absorbed = decision_owner.is_some_and(|owner| {
                absorbed_decision_owner(lowering, def_block) == Some(owner)
                    && absorbed_decision_entry(lowering, owner) != Some(def_block)
            });
            if def_block != block && !def_is_absorbed {
                return lowering
                    .bindings
                    .local_for_reg_in_block(block, reg)
                    .map(HirExpr::LocalRef)
                    .unwrap_or_else(|| lowering.bindings.expr_for_temp(temp));
            }
            if !absorbed && def_has_intervening_barrier(lowering, def, instr_ref) {
                return lowering.bindings.expr_for_temp(temp);
            }
            if !absorbed
                && def_is_call_consumed_by_non_branch(lowering, def, instr_ref)
                && (!allow_call_consumed_by_pure_wrapper
                    || def_has_later_use_after_pure_wrapper(lowering, def, instr_ref))
            {
                return lowering.bindings.expr_for_temp(temp);
            }
            expr_for_fixed_def_single_eval(lowering, def)
                .unwrap_or_else(|| lowering.bindings.expr_for_temp(temp))
        }
        SsaValue::Phi(phi) => lowering
            .bindings
            .local_for_reg_in_block(block, reg)
            .map_or_else(|| lowering.bindings.expr_for_phi(phi), HirExpr::LocalRef),
    }
}

pub(crate) fn block_is_absorbed_decision(lowering: &ProtoLowering<'_>, block: BlockRef) -> bool {
    absorbed_decision_owner(lowering, block).is_some()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AbsorbedDecisionOwner {
    Value(crate::structure::RegionId),
    Condition(crate::structure::ConditionPlanId),
}

fn absorbed_decision_owner(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
) -> Option<AbsorbedDecisionOwner> {
    if let Some(condition) = lowering.structure.plan().absorbed_condition_owner(block) {
        return Some(AbsorbedDecisionOwner::Condition(condition));
    }
    lowering
        .structure
        .plan()
        .region_for_block(block)
        .filter(|region| {
            matches!(
                lowering.structure.plan().region(*region),
                Some(crate::structure::RegionPlan::ValueDecision { .. })
            )
        })
        .map(AbsorbedDecisionOwner::Value)
}

fn absorbed_decision_entry(
    lowering: &ProtoLowering<'_>,
    owner: AbsorbedDecisionOwner,
) -> Option<BlockRef> {
    match owner {
        AbsorbedDecisionOwner::Condition(condition) => {
            lowering.structure.plan().condition(condition)?.header()
        }
        AbsorbedDecisionOwner::Value(region) => match lowering.structure.plan().region(region)? {
            crate::structure::RegionPlan::ValueDecision { entry, .. } => Some(*entry),
            _ => None,
        },
    }
}

pub(in crate::hir::analyze) fn expr_for_ssa_value(
    lowering: &ProtoLowering<'_>,
    value: SsaValue,
) -> HirExpr {
    match value {
        SsaValue::Entry(reg) => expr_for_entry_reg(lowering, reg),
        SsaValue::Def(def) => lowering
            .bindings
            .expr_for_temp(lowering.bindings.fixed_temps[def.index()]),
        SsaValue::Phi(phi) => lowering.bindings.expr_for_phi(phi),
    }
}

fn def_is_call_consumed_by_non_branch(
    lowering: &ProtoLowering<'_>,
    def: DefId,
    consumer_instr: InstrRef,
) -> bool {
    let def_instr = lowering.dataflow.def_instr(def);
    matches!(lowering.proto.instrs[def_instr.index()], LowInstr::Call(_))
        && !matches!(
            lowering.proto.instrs[consumer_instr.index()],
            LowInstr::Branch(_)
        )
}

// 纯壳层只代表同一次条件求值；如果 call 结果在壳层之后还被非 branch 指令读取，
// 展开 call 会把一次求值变成多次求值，因此必须退回 temp。最终 branch/test
// 读取同一个结果是这条条件求值的一部分，不应算作额外消费。
fn def_has_later_use_after_pure_wrapper(
    lowering: &ProtoLowering<'_>,
    def: DefId,
    wrapper_instr: InstrRef,
) -> bool {
    let def_reg = lowering.dataflow.def_reg(def);
    let def_block = lowering.dataflow.def_block(def);
    if lowering.cfg.instr_to_block.get(wrapper_instr.index()) != Some(&def_block) {
        return true;
    }

    let range = lowering.cfg.blocks[def_block.index()].instrs;
    for instr_index in (wrapper_instr.index() + 1)..range.end() {
        let effect = &lowering.dataflow.instr_effects[instr_index];
        if effect.uses_fixed(def_reg)
            && !matches!(lowering.proto.instrs[instr_index], LowInstr::Branch(_))
        {
            return true;
        }
        if effect.must_define(def_reg) {
            return false;
        }
    }
    false
}

fn def_has_intervening_barrier(
    lowering: &ProtoLowering<'_>,
    def: DefId,
    consumer_instr: InstrRef,
) -> bool {
    let def_instr = lowering.dataflow.def_instr(def);
    if def_instr.index() >= consumer_instr.index() {
        return false;
    }
    let producer = &lowering.dataflow.instr_effects[def_instr.index()];
    ((def_instr.index() + 1)..consumer_instr.index()).any(|instr_index| {
        producer.fixed_defs_intersect_uses(&lowering.dataflow.instr_effects[instr_index])
            || lowering.dataflow.effect_summaries[instr_index].has_effect_tags()
    })
}
