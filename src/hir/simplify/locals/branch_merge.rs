//! 这个文件负责 `locals` pass 内部的 if/else fallthrough 赋值汇总。
//!
//! 主 pass 在普通 temp 链之外，还需要识别一种稳定形状：`if` 的 then/else 两侧都给同一个
//! temp 赋值，合流之后又继续读取这个 temp。这里会把这种 temp 报告给主 pass，让主 pass
//! 在 if 前分配一个空 local，再由两条分支写回同一个 binding。
//!
//! 本文件只消费当前 HIR 树和 `TempTouchIndex`，不分配 local、不改写语句。分支摘要同时
//! 维护“所有合流路径都已写入”和“首次写入前可能读取”，因此主 pass 只会在声明可以
//! 支配所有读取时接受候选。常真 while 还会汇总所有 break 出口的 must-def；普通 while
//! 保留零次执行路径，不会把 body 写入误报成 loop fallthrough 写入。
//!
//! 输入形状：`if c then t1 = a else t1 = b end; use(t1)`。
//! 输出形状：候选 temp 集合 `{ t1 }`，后续由主 pass 物化成 `local l; if c then l = a else l = b end`。

use std::collections::BTreeSet;

use super::super::expr_facts::expr_truthiness;
use super::super::temp_touch::{
    TempTouchIndex, collect_temp_reads_by_stmt, collect_temp_refs_in_expr,
};
use crate::hir::common::{HirBlock, HirLValue, HirStmt, TempId};
use crate::hir::expr_safety::HirExprSafety;

#[derive(Debug, Clone, Default)]
struct FallthroughSummary {
    falls_through: bool,
    assigned_temps: BTreeSet<TempId>,
    reads_before_assignment: BTreeSet<TempId>,
    break_assigned_temps: Option<BTreeSet<TempId>>,
}

pub(super) fn candidate_temps(
    stmt: &HirStmt,
    temp_touches: &TempTouchIndex,
    stmt_index: usize,
    is_reserved: &dyn Fn(TempId) -> bool,
    safety: HirExprSafety,
) -> Vec<TempId> {
    let HirStmt::If(if_stmt) = stmt else {
        return Vec::new();
    };
    let Some(else_block) = &if_stmt.else_block else {
        return Vec::new();
    };

    let (Some(then_summary), Some(else_summary)) = (
        summarize_block_fallthrough_assignments(&if_stmt.then_block, safety),
        summarize_block_fallthrough_assignments(else_block, safety),
    ) else {
        // 候选拒绝[ProofIncomplete]：任一 arm 的 goto 可能重新汇入当前 if，也可能逃逸；
        // HIR 缺少目标到当前 region merge 的 owner/reaching-def，不能把 unknown arm 当作已终结。
        return Vec::new();
    };
    let Some(common_temps) = intersect_fallthrough_assignment_sets([&then_summary, &else_summary])
    else {
        return Vec::new();
    };
    let condition_reads = collect_temp_refs_in_expr(&if_stmt.cond);
    let reads_before_assignment = [&then_summary, &else_summary]
        .into_iter()
        .flat_map(|summary| summary.reads_before_assignment.iter())
        .copied()
        .chain(condition_reads)
        .collect::<BTreeSet<_>>();

    common_temps
        .into_iter()
        .filter(|temp| !is_reserved(*temp))
        .filter(|temp| !reads_before_assignment.contains(temp))
        // 候选拒绝[SemanticBarrier:Lifetime]：`t=obj; if c then t=a else t=b end; GC` 若在 if 前另建 local，旧 t 物理槽不再按原时点覆盖，弱表/`__gc` 可观察旧对象延寿。
        .filter(|temp| !temp_touches.touches_before(stmt_index, *temp))
        // 候选拒绝[LayerBoundary]：合流后没有 touch 的 branch temp 是 dead-temps 的删除候选，不应物化为空 local。
        .filter(|temp| temp_touches.touches_after(stmt_index + 1, *temp))
        .collect()
}

pub(super) fn definite_if_arm_temp_writes(stmt: &HirStmt) -> Option<[TempId; 2]> {
    let HirStmt::If(if_stmt) = stmt else {
        return None;
    };
    let else_block = if_stmt.else_block.as_ref()?;
    Some([
        single_scalar_temp_write(&if_stmt.then_block)?,
        single_scalar_temp_write(else_block)?,
    ])
}

fn single_scalar_temp_write(block: &HirBlock) -> Option<TempId> {
    let [HirStmt::Assign(assign)] = block.stmts.as_slice() else {
        return None;
    };
    let ([HirLValue::Temp(temp)], [_], None) = (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) else {
        return None;
    };
    Some(*temp)
}

fn summarize_block_fallthrough_assignments(
    block: &HirBlock,
    safety: HirExprSafety,
) -> Option<FallthroughSummary> {
    let mut assigned_temps = BTreeSet::new();
    let mut reads_before_assignment = BTreeSet::new();
    let mut break_assigned_temps = None;
    let mut falls_through = true;

    for stmt in &block.stmts {
        if !falls_through {
            break;
        }

        let stmt_summary = summarize_stmt_fallthrough_assignments(stmt, safety)?;
        reads_before_assignment.extend(
            stmt_summary
                .reads_before_assignment
                .difference(&assigned_temps)
                .copied(),
        );
        if let Some(mut break_assignments) = stmt_summary.break_assigned_temps {
            break_assignments.extend(assigned_temps.iter().copied());
            intersect_optional_assignment_set(&mut break_assigned_temps, break_assignments);
        }
        if stmt_summary.falls_through {
            assigned_temps.extend(stmt_summary.assigned_temps);
        } else {
            falls_through = false;
        }
    }

    Some(FallthroughSummary {
        falls_through,
        assigned_temps,
        reads_before_assignment,
        break_assigned_temps,
    })
}

fn summarize_stmt_fallthrough_assignments(
    stmt: &HirStmt,
    safety: HirExprSafety,
) -> Option<FallthroughSummary> {
    let reads = || {
        collect_temp_reads_by_stmt(std::slice::from_ref(stmt))
            .into_iter()
            .next()
            .unwrap_or_default()
    };
    match stmt {
        HirStmt::GlobalDecl(_) => None,
        HirStmt::LocalDecl(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Label(_) => Some(FallthroughSummary {
            falls_through: true,
            assigned_temps: BTreeSet::new(),
            reads_before_assignment: reads(),
            break_assigned_temps: None,
        }),
        HirStmt::Assign(assign) => Some(FallthroughSummary {
            falls_through: true,
            assigned_temps: assign
                .targets
                .iter()
                .filter_map(|target| match target {
                    HirLValue::Temp(temp) => Some(*temp),
                    HirLValue::Param(_)
                    | HirLValue::Local(_)
                    | HirLValue::Upvalue(_)
                    | HirLValue::Global(_)
                    | HirLValue::TableAccess(_) => None,
                })
                .collect(),
            // Lua 平行赋值先求完全部 RHS/复合左值，再提交直接 binding 写入。
            reads_before_assignment: reads(),
            break_assigned_temps: None,
        }),
        HirStmt::TableSetList(_) => Some(FallthroughSummary {
            falls_through: true,
            assigned_temps: BTreeSet::new(),
            reads_before_assignment: reads(),
            break_assigned_temps: None,
        }),
        HirStmt::Goto(_) => None,
        HirStmt::Break => Some(FallthroughSummary {
            falls_through: false,
            assigned_temps: BTreeSet::new(),
            reads_before_assignment: BTreeSet::new(),
            break_assigned_temps: Some(BTreeSet::new()),
        }),
        HirStmt::Return(_) | HirStmt::Continue => Some(FallthroughSummary {
            falls_through: false,
            assigned_temps: BTreeSet::new(),
            reads_before_assignment: reads(),
            break_assigned_temps: None,
        }),
        HirStmt::If(if_stmt) => {
            let then_summary =
                summarize_block_fallthrough_assignments(&if_stmt.then_block, safety)?;
            let else_summary = match if_stmt.else_block.as_ref() {
                Some(else_block) => summarize_block_fallthrough_assignments(else_block, safety)?,
                None => FallthroughSummary {
                    falls_through: true,
                    assigned_temps: BTreeSet::new(),
                    reads_before_assignment: BTreeSet::new(),
                    break_assigned_temps: None,
                },
            };
            let assigned_temps =
                intersect_fallthrough_assignment_sets([&then_summary, &else_summary])
                    .unwrap_or_default();
            let reads_before_assignment = collect_temp_refs_in_expr(&if_stmt.cond)
                .into_iter()
                .chain(then_summary.reads_before_assignment.iter().copied())
                .chain(else_summary.reads_before_assignment.iter().copied())
                .collect();
            let mut break_assigned_temps = None;
            if let Some(assignments) = then_summary.break_assigned_temps {
                intersect_optional_assignment_set(&mut break_assigned_temps, assignments);
            }
            if let Some(assignments) = else_summary.break_assigned_temps {
                intersect_optional_assignment_set(&mut break_assigned_temps, assignments);
            }

            Some(FallthroughSummary {
                falls_through: then_summary.falls_through || else_summary.falls_through,
                assigned_temps,
                reads_before_assignment,
                break_assigned_temps,
            })
        }
        HirStmt::Block(block) => summarize_block_fallthrough_assignments(block, safety),
        HirStmt::While(while_stmt) => {
            let body = summarize_block_fallthrough_assignments(&while_stmt.body, safety)?;
            let condition_is_true = expr_truthiness(&while_stmt.cond, safety) == Some(true);
            let assigned_temps = condition_is_true
                .then(|| body.break_assigned_temps.clone())
                .flatten()
                .unwrap_or_default();
            Some(FallthroughSummary {
                // 常真 while 只经 break 合流；其它 while 保留零次执行路径。
                falls_through: !condition_is_true || body.break_assigned_temps.is_some(),
                assigned_temps,
                reads_before_assignment: collect_temp_refs_in_expr(&while_stmt.cond)
                    .into_iter()
                    .chain(body.reads_before_assignment)
                    .collect(),
                // 当前 loop 消费 body 的 break，不能把它传播给外层 loop。
                break_assigned_temps: None,
            })
        }
        HirStmt::Repeat(repeat_stmt) => {
            let body = summarize_block_fallthrough_assignments(&repeat_stmt.body, safety)?;
            let mut reads_before_assignment = body.reads_before_assignment;
            if body.falls_through {
                reads_before_assignment.extend(
                    collect_temp_refs_in_expr(&repeat_stmt.cond)
                        .difference(&body.assigned_temps)
                        .copied(),
                );
            } else {
                // continue 也会到达 repeat condition；当前 summary 不区分 continue 与
                // return/break，因此无普通 fallthrough 时保守保留全部 condition 读取。
                reads_before_assignment.extend(collect_temp_refs_in_expr(&repeat_stmt.cond));
            }
            Some(FallthroughSummary {
                // break 路径可能绕过 body 后缀，当前摘要不把 body 写入承诺为 loop must-def。
                falls_through: true,
                assigned_temps: BTreeSet::new(),
                reads_before_assignment,
                break_assigned_temps: None,
            })
        }
        HirStmt::NumericFor(numeric_for) => {
            let body = summarize_block_fallthrough_assignments(&numeric_for.body, safety)?;
            Some(FallthroughSummary {
                falls_through: true,
                assigned_temps: BTreeSet::new(),
                reads_before_assignment: collect_temp_refs_in_expr(&numeric_for.start)
                    .into_iter()
                    .chain(collect_temp_refs_in_expr(&numeric_for.limit))
                    .chain(collect_temp_refs_in_expr(&numeric_for.step))
                    .chain(body.reads_before_assignment)
                    .collect(),
                break_assigned_temps: None,
            })
        }
        HirStmt::GenericFor(generic_for) => {
            let body = summarize_block_fallthrough_assignments(&generic_for.body, safety)?;
            let iterator_reads = generic_for
                .iterator
                .iter()
                .flat_map(collect_temp_refs_in_expr);
            Some(FallthroughSummary {
                falls_through: true,
                assigned_temps: BTreeSet::new(),
                reads_before_assignment: iterator_reads
                    .chain(body.reads_before_assignment)
                    .collect(),
                break_assigned_temps: None,
            })
        }
    }
}

fn intersect_optional_assignment_set(
    intersection: &mut Option<BTreeSet<TempId>>,
    assignments: BTreeSet<TempId>,
) {
    match intersection {
        Some(current) => current.retain(|temp| assignments.contains(temp)),
        None => *intersection = Some(assignments),
    }
}

fn intersect_fallthrough_assignment_sets<'a>(
    summaries: impl IntoIterator<Item = &'a FallthroughSummary>,
) -> Option<BTreeSet<TempId>> {
    let mut fallthrough_sets = summaries
        .into_iter()
        .filter(|summary| summary.falls_through)
        .map(|summary| summary.assigned_temps.clone());
    let mut intersection = fallthrough_sets.next()?;
    for set in fallthrough_sets {
        intersection = intersection
            .intersection(&set)
            .copied()
            .collect::<BTreeSet<_>>();
    }
    Some(intersection)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::common::{
        HirAssign, HirExpr, HirGoto, HirIf, HirLabelId, HirReturn, HirValuePack,
    };

    fn block(stmts: Vec<HirStmt>) -> HirBlock {
        HirBlock { stmts }
    }

    fn assign_temp(temp: TempId) -> HirStmt {
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(temp)],
            values: HirValuePack::fixed(vec![HirExpr::Integer(1)]),
        }))
    }

    fn branch(then_stmts: Vec<HirStmt>, else_stmts: Vec<HirStmt>) -> HirStmt {
        HirStmt::If(Box::new(HirIf {
            cond: HirExpr::Boolean(true),
            then_block: block(then_stmts),
            else_block: Some(block(else_stmts)),
        }))
    }

    fn candidates(stmt: &HirStmt, temp: TempId) -> Vec<TempId> {
        let stmt_refs = [BTreeSet::from([temp]), BTreeSet::from([temp])];
        candidate_temps(
            stmt,
            &TempTouchIndex::new(&stmt_refs),
            0,
            &|_| false,
            HirExprSafety::for_dialect(crate::decompile::DecompileDialect::Auto),
        )
    }

    #[test]
    fn goto_unknown_arm_cannot_be_ignored_during_merge() {
        let temp = TempId(0);
        let stmt = branch(
            vec![HirStmt::Goto(Box::new(HirGoto {
                target: HirLabelId(0),
            }))],
            vec![assign_temp(temp)],
        );

        assert!(candidates(&stmt, temp).is_empty());
    }

    #[test]
    fn proven_terminal_arm_does_not_block_clean_fallthrough_merge() {
        let temp = TempId(0);
        let stmt = branch(
            vec![HirStmt::Return(Box::new(HirReturn {
                values: HirValuePack::default(),
            }))],
            vec![assign_temp(temp)],
        );

        assert_eq!(candidates(&stmt, temp), vec![temp]);
    }
}
