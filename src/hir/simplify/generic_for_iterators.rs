//! 把 generic-for 的 VM 初始化序列收回完整 source value pack。
//!
//! Lua 5.4+ 除 iterator/state/control 外还会物化第 4 个 closing value；前置固定表达式
//! 与最终多返回调用又可能拆成多条赋值。这里优先按 GenericFor 已记录的完整源码 pack
//! 一次接管初始化序列；若 closing value 已经更早求值，则只额外收回紧邻循环头的匿名
//! 单次 `nil` run，不跨语句移动其它表达式。
//!
//! 输入：`t0 = next; t1,t2,t3 = factory()<exact:3>; GenericFor(t0,t1,t2,t3)`
//! 输出：`GenericFor(next, factory()<open>)`
//! 输入：`t1,t2 = nil,nil; GenericFor(t0,t1,t2,t3)`
//! 输出：`GenericFor(t0,nil,nil,t3)`
//! direct closure producer 保留为独立 local function；child proto 的体量无法由 HIR
//! 表达式复杂度概括，不应恢复成 loop head 内的多行匿名函数。

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::decompile::DecompileDialect;
use crate::hir::common::{
    HirBlock, HirExpr, HirGenericFor, HirLValue, HirProto, HirStmt, HirValuePack, TempId,
};
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

use super::mention::collect_temp_use_counts;
use super::walk::{HirRewritePass, rewrite_proto};

pub(super) fn fold_generic_for_iterators_in_proto(
    proto: &mut HirProto,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
) -> bool {
    let use_counts = collect_temp_use_counts(proto);
    let debug_temps = proto
        .temp_debug_locals
        .iter()
        .map(Option::is_some)
        .collect();
    rewrite_proto(
        proto,
        &mut GenericForIteratorPass {
            use_counts,
            debug_temps,
            facts,
            dialect,
        },
    )
}

struct GenericForIteratorPass<'a> {
    use_counts: BTreeMap<TempId, usize>,
    debug_temps: Vec<bool>,
    facts: &'a ProtoPromotionFacts,
    dialect: DecompileDialect,
}

impl HirRewritePass for GenericForIteratorPass<'_> {
    fn rewrite_stmt(&mut self, stmt: &mut HirStmt) -> bool {
        let HirStmt::GenericFor(generic_for) = stmt else {
            return false;
        };
        trim_trailing_nil_iterators(&mut generic_for.iterator)
    }

    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        let old_stmts = std::mem::take(&mut block.stmts);
        let mut pending = VecDeque::from(old_stmts);
        let mut new_stmts = Vec::with_capacity(pending.len());
        let mut changed = false;

        while !pending.is_empty() {
            if fold_adjacent_nil_iterators(&mut pending, self, &mut new_stmts) {
                changed = true;
            } else if let Some(plan) = fold_plan(pending.make_contiguous(), self) {
                fold_front(&mut pending, plan, &mut new_stmts);
                changed = true;
            } else {
                new_stmts.push(
                    pending
                        .pop_front()
                        .expect("non-empty generic-for scan queue"),
                );
            }
        }

        block.stmts = new_stmts;
        changed
    }
}

fn trim_trailing_nil_iterators(iterator: &mut HirValuePack) -> bool {
    // 候选拒绝[SemanticBarrier:ValueArity]：`for _ in nil, f() do` 的 fixed nil 位于 open tail 前，删除会把 iterator/state 位置左移。
    if iterator.tail.is_some() {
        return false;
    }
    let original_len = iterator.fixed.len();
    while iterator.fixed.len() > 1 && matches!(iterator.fixed.last(), Some(HirExpr::Nil)) {
        iterator.fixed.pop();
    }
    iterator.fixed.len() != original_len
}

fn fold_adjacent_nil_iterators(
    pending: &mut VecDeque<HirStmt>,
    context: &GenericForIteratorPass<'_>,
    new_stmts: &mut Vec<HirStmt>,
) -> bool {
    let (iterator_start, value_count) = {
        let stmts = pending.make_contiguous();
        let (Some(HirStmt::Assign(assign)), Some(HirStmt::GenericFor(generic_for))) =
            (stmts.first(), stmts.get(1))
        else {
            return false;
        };
        let value_count = assign.targets.len();
        // exact-width tail 也能给出目标数，但 fixed 为空；这里只接受逐项可核验的 nil。
        if value_count == 0
            || assign.values.tail.is_some()
            || assign.values.fixed.len() != value_count
        {
            return false;
        }
        let Some(iterator_start) =
            generic_for
                .iterator
                .fixed
                .windows(value_count)
                .position(|window| {
                    window
                        .iter()
                        .zip(&assign.targets)
                        .zip(&assign.values.fixed)
                        .all(|((iterator, target), value)| {
                            matches!(
                                (iterator, target, value),
                                (
                                    HirExpr::TempRef(actual),
                                    HirLValue::Temp(expected),
                                    HirExpr::Nil
                                ) if actual == expected
                                    && iterator_target_can_be_deleted(*expected, context)
                            )
                        })
                })
        else {
            return false;
        };
        (iterator_start, value_count)
    };

    let Some(HirStmt::Assign(_)) = pending.pop_front() else {
        unreachable!("validated adjacent generic-for nil assignment");
    };
    let Some(HirStmt::GenericFor(mut generic_for)) = pending.pop_front() else {
        unreachable!("validated adjacent generic-for owner");
    };
    generic_for.iterator.fixed[iterator_start..iterator_start + value_count].fill(HirExpr::Nil);
    trim_trailing_nil_iterators(&mut generic_for.iterator);
    new_stmts.push(HirStmt::GenericFor(generic_for));
    true
}

#[derive(Clone, Copy)]
struct FoldPlan {
    assignment_count: usize,
    gap_count: usize,
}

fn fold_plan(stmts: &[HirStmt], context: &GenericForIteratorPass<'_>) -> Option<FoldPlan> {
    // VM 最多给 generic-for 保留 iterator/state/control/closing 四个 source slots。
    for assignment_count in 1..=4 {
        if !matches!(stmts.get(assignment_count - 1), Some(HirStmt::Assign(_))) {
            return None;
        }
        let assignments = &stmts[..assignment_count];
        if let Some(HirStmt::GenericFor(generic_for)) = stmts.get(assignment_count) {
            return assignments_match_iterator(assignments, generic_for, context).then_some(
                FoldPlan {
                    assignment_count,
                    gap_count: 0,
                },
            );
        }
        if let (Some(gap @ HirStmt::Assign(_)), Some(HirStmt::GenericFor(generic_for))) =
            (stmts.get(assignment_count), stmts.get(assignment_count + 1))
            && assignments_match_iterator(assignments, generic_for, context)
        {
            return iterator_pack_can_cross_assignment(assignments, gap, context).then_some(
                FoldPlan {
                    assignment_count,
                    gap_count: 1,
                },
            );
        }
    }
    None
}

// 跨 gap 比相邻折叠多一次求值重排。稳定标量的求值没有 user-code effect；只要 producer、
// gap 的直接读写 home 两两满足依赖顺序，就可以保留 gap 并把 iterator pack 延后到 loop head。
fn iterator_pack_can_cross_assignment(
    assignments: &[HirStmt],
    gap: &HirStmt,
    context: &GenericForIteratorPass<'_>,
) -> bool {
    let HirStmt::Assign(gap) = gap else {
        return false;
    };
    if gap
        .values
        .tail
        .as_ref()
        .is_some_and(|tail| matches!(tail.as_expr(), HirExpr::Call(_)))
    {
        // 候选拒绝[SemanticBarrier:EvalOrder]：open/exact call gap 可执行 user code；iterator 求值跨过它会颠倒 producer 与 call 的事件顺序。
        return false;
    }

    let gap_target_slots = match direct_target_home_slots(&gap.targets, context.facts) {
        Ok(slots) => slots,
        Err(CrossGapFactError::MissingHome) => {
            // 候选拒绝[ProofIncomplete]：gap direct target 缺可信 home 时，尚不能证明它不覆盖 iterator 的 source/target；应由 promotion provenance 补齐。
            return false;
        }
        Err(CrossGapFactError::Observable) => {
            // 候选拒绝[SemanticBarrier:EvalOrder]：upvalue/global/table 左值可执行 user code 或改变 loop head 可观察状态，iterator 求值不能跨过它。
            return false;
        }
    };
    let gap_source_slots = match stable_value_home_slots(&gap.values.fixed, context.facts) {
        Ok(slots) => slots,
        Err(CrossGapFactError::MissingHome) => {
            // 候选拒绝[ProofIncomplete]：gap source 缺可信 home 时，尚不能证明它不读取已删除的 iterator target；应由 promotion provenance 补齐。
            return false;
        }
        Err(CrossGapFactError::Observable) => {
            // 候选拒绝[SemanticBarrier:EvalOrder]：call、lookup、closure 或运算表达式跨 iterator producer 可执行 user code/读取可变状态；这里只移动字面量和可信直接 binding。
            return false;
        }
    };

    let mut iterator_target_slots = BTreeSet::new();
    let mut iterator_source_slots = BTreeSet::new();
    for stmt in assignments {
        let HirStmt::Assign(assign) = stmt else {
            return false;
        };
        if assign
            .values
            .tail
            .as_ref()
            .is_some_and(|tail| matches!(tail.as_expr(), HirExpr::Call(_)))
        {
            // 候选拒绝[SemanticBarrier:EvalOrder]：`factory()<exact:N>; gap; for ...` 合并后会把 factory call 延迟到 gap 后；factory 可观察 gap 前后的状态。
            return false;
        }
        for target in &assign.targets {
            let HirLValue::Temp(temp) = target else {
                return false;
            };
            let Some(slot) = context.facts.trusted_temp_home_slot(*temp) else {
                // 候选拒绝[ProofIncomplete]：iterator target 缺可信 home，无法排除与 gap assignment 同槽；应由 promotion provenance 补齐。
                return false;
            };
            iterator_target_slots.insert(slot);
        }
        let source_slots = match stable_value_home_slots(&assign.values.fixed, context.facts) {
            Ok(slots) => slots,
            Err(CrossGapFactError::MissingHome) => {
                // 候选拒绝[ProofIncomplete]：iterator source 缺可信 home 时，尚不能证明 gap 不会覆盖延迟读取；应由 promotion provenance 补齐。
                return false;
            }
            Err(CrossGapFactError::Observable) => {
                // 候选拒绝[SemanticBarrier:EvalOrder]：可观察 iterator RHS 延迟到 gap 后会重排 call/lookup/metamethod；只接纳字面量和可信直接 binding。
                return false;
            }
        };
        iterator_source_slots.extend(source_slots);
    }

    // 候选拒绝[SemanticBarrier:EvalOrder]：若 gap 读写槽与 iterator source/target 重叠，移动 pack 到 gap 后会改变被复制或被循环读取的值。
    iterator_target_slots.is_disjoint(&gap_target_slots)
        && iterator_source_slots.is_disjoint(&gap_target_slots)
        && iterator_target_slots.is_disjoint(&gap_source_slots)
}

#[derive(Clone, Copy)]
enum CrossGapFactError {
    MissingHome,
    Observable,
}

fn direct_target_home_slots(
    targets: &[HirLValue],
    facts: &ProtoPromotionFacts,
) -> Result<BTreeSet<HomeSlotKey>, CrossGapFactError> {
    let mut slots = BTreeSet::new();
    for target in targets {
        let slot = match target {
            HirLValue::Param(param) => facts.trusted_param_home_slot(*param),
            HirLValue::Local(local) => facts.trusted_local_home_slot(*local),
            HirLValue::Temp(temp) => facts.trusted_temp_home_slot(*temp),
            HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_) => {
                return Err(CrossGapFactError::Observable);
            }
        }
        .ok_or(CrossGapFactError::MissingHome)?;
        slots.insert(slot);
    }
    Ok(slots)
}

fn stable_value_home_slots(
    values: &[HirExpr],
    facts: &ProtoPromotionFacts,
) -> Result<BTreeSet<HomeSlotKey>, CrossGapFactError> {
    let mut slots = BTreeSet::new();
    for value in values {
        let slot = match value {
            HirExpr::ParamRef(param) => facts
                .trusted_param_home_slot(*param)
                .ok_or(CrossGapFactError::MissingHome)?,
            HirExpr::LocalRef(local) => facts
                .trusted_local_home_slot(*local)
                .ok_or(CrossGapFactError::MissingHome)?,
            HirExpr::TempRef(temp) => facts
                .trusted_temp_home_slot(*temp)
                .ok_or(CrossGapFactError::MissingHome)?,
            HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::Int64(_)
            | HirExpr::UInt64(_)
            | HirExpr::Complex { .. }
            | HirExpr::Vector(_)
            | HirExpr::UpvalueRef(_) => continue,
            HirExpr::GlobalRef(_)
            | HirExpr::TableAccess(_)
            | HirExpr::Unary(_)
            | HirExpr::Binary(_)
            | HirExpr::LogicalAnd(_)
            | HirExpr::LogicalOr(_)
            | HirExpr::Decision(_)
            | HirExpr::Call(_)
            | HirExpr::VarArg
            | HirExpr::TableConstructor(_)
            | HirExpr::Closure(_)
            | HirExpr::Unresolved(_) => return Err(CrossGapFactError::Observable),
        };
        slots.insert(slot);
    }
    Ok(slots)
}

fn assignments_match_iterator(
    assignments: &[HirStmt],
    generic_for: &HirGenericFor,
    context: &GenericForIteratorPass<'_>,
) -> bool {
    let mut expected = generic_for.iterator.fixed.iter();
    let mut protocol_prefix_width = 0;
    for (index, stmt) in assignments.iter().enumerate() {
        let HirStmt::Assign(assign) = stmt else {
            return false;
        };
        // 候选拒绝[SemanticBarrier:ValueArity]：target 之后的 fixed RHS 仍会求值但不占赋值槽；直接拼进 loop pack 会占据并移动后续 protocol 槽。
        if assign.values.fixed.len() > assign.targets.len() {
            return false;
        }
        // 候选拒绝[SemanticBarrier:ValueArity]：非末尾 open tail 在源码列表中会被后续表达式截成单值；两个 tail 也不能保持各自的展开边界。
        if assign.values.tail.is_some()
            && (index + 1 != assignments.len() || generic_for.iterator.tail.is_some())
        {
            return false;
        }
        if assign
            .values
            .tail
            .as_ref()
            .and_then(|tail| tail.exact_width())
            .is_some_and(|width| {
                protocol_prefix_width + assign.values.fixed.len() + width
                    < generic_for_protocol_width(context.dialect)
            })
        {
            // 候选拒绝[SemanticBarrier:ValueArity]：exact tail 未覆盖完整 generic-for 协议；改成 open tail 会把被截掉的返回值带入 control/closing 槽。
            return false;
        }
        // 候选拒绝[PolicyBoundary]：closure producer 保留命名 binding，避免把完整 child body 压成 loop head 内的多行 IIFE。
        if assign
            .values
            .fixed
            .iter()
            .any(|value| matches!(value, HirExpr::Closure(_)))
        {
            return false;
        }
        for target in &assign.targets {
            let (HirLValue::Temp(actual), Some(HirExpr::TempRef(expected))) =
                (target, expected.next())
            else {
                return false;
            };
            if actual != expected {
                return false;
            }
            if !iterator_target_can_be_deleted(*actual, context) {
                return false;
            }
        }
        protocol_prefix_width += assign.targets.len();
    }
    expected.next().is_none()
}

fn generic_for_protocol_width(dialect: DecompileDialect) -> usize {
    match dialect {
        DecompileDialect::Lua54 | DecompileDialect::Lua55 | DecompileDialect::Auto => 4,
        DecompileDialect::Lua51
        | DecompileDialect::Lua52
        | DecompileDialect::Lua53
        | DecompileDialect::Luajit
        | DecompileDialect::Luau => 3,
    }
}

fn iterator_target_can_be_deleted(target: TempId, context: &GenericForIteratorPass<'_>) -> bool {
    // 候选拒绝[SemanticBarrier:ValueFlow]：producer target 的额外读取仍需原 materialization；regress_343 的 loop 后 live-out 会变成未定义值。
    if context.use_counts.get(&target) != Some(&1) {
        return false;
    }
    // 候选拒绝[SemanticBarrier:Scope]：debug.getlocal 可观察 source iterator/state/control 的词法身份；见 regress_343。
    if context
        .debug_temps
        .get(target.index())
        .copied()
        .unwrap_or(false)
    {
        return false;
    }
    true
}

fn fold_front(pending: &mut VecDeque<HirStmt>, plan: FoldPlan, new_stmts: &mut Vec<HirStmt>) {
    let mut iterator = HirValuePack::default();
    for _ in 0..plan.assignment_count {
        let HirStmt::Assign(assign) = pending
            .pop_front()
            .expect("validated generic-for init assignment")
        else {
            unreachable!("fold plan only counts assignments");
        };
        let target_count = assign.targets.len();
        let fixed_count = assign.values.fixed.len();
        iterator.fixed.extend(assign.values.fixed);
        if let Some(tail) = assign.values.tail {
            iterator.tail = Some(tail.into_open());
        } else {
            iterator.fixed.resize(
                iterator.fixed.len() + target_count - fixed_count,
                HirExpr::Nil,
            );
        }
    }

    for _ in 0..plan.gap_count {
        new_stmts.push(
            pending
                .pop_front()
                .expect("validated generic-for assignment gap"),
        );
    }

    let Some(HirStmt::GenericFor(mut generic_for)) = pending.pop_front() else {
        unreachable!("validated generic-for owner");
    };
    if iterator.tail.is_none() {
        iterator.tail = generic_for.iterator.tail.take();
    } else {
        assert!(
            generic_for.iterator.tail.is_none(),
            "validated generic-for fold cannot merge two value-pack tails"
        );
    }
    trim_trailing_nil_iterators(&mut iterator);
    generic_for.iterator = iterator;
    new_stmts.push(HirStmt::GenericFor(generic_for));
}
