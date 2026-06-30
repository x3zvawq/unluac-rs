//! 这个文件负责 `locals` pass 内部的 if/else fallthrough 赋值汇总。
//!
//! 主 pass 在普通 temp 链之外，还需要识别一种稳定形状：`if` 的 then/else 两侧都给同一个
//! temp 赋值，合流之后又继续读取这个 temp。这里会把这种 temp 报告给主 pass，让主 pass
//! 在 if 前分配一个空 local，再由两条分支写回同一个 binding。
//!
//! 本文件只消费当前 HIR 树和 `TempTouchIndex`，不分配 local、不改写语句，也不尝试恢复
//! StructureFacts 没有给出的 branch 语义。
//!
//! 输入形状：`if c then t1 = a else t1 = b end; use(t1)`。
//! 输出形状：候选 temp 集合 `{ t1 }`，后续由主 pass 物化成 `local l; if c then l = a else l = b end`。

use std::collections::BTreeSet;

use super::super::temp_touch::TempTouchIndex;
use crate::hir::common::{HirBlock, HirLValue, HirStmt, TempId};

#[derive(Debug, Clone, Default)]
struct FallthroughSummary {
    falls_through: bool,
    assigned_temps: BTreeSet<TempId>,
}

pub(super) fn candidate_temps(
    stmt: &HirStmt,
    temp_touches: &TempTouchIndex,
    stmt_index: usize,
    reserved_temps: &BTreeSet<TempId>,
) -> Vec<TempId> {
    let HirStmt::If(if_stmt) = stmt else {
        return Vec::new();
    };
    let Some(else_block) = &if_stmt.else_block else {
        return Vec::new();
    };

    let then_summary = summarize_block_fallthrough_assignments(&if_stmt.then_block);
    let else_summary = summarize_block_fallthrough_assignments(else_block);
    let Some(common_temps) =
        intersect_fallthrough_assignment_sets([then_summary.as_ref(), else_summary.as_ref()])
    else {
        return Vec::new();
    };

    common_temps
        .into_iter()
        .filter(|temp| !reserved_temps.contains(temp))
        .filter(|temp| !temp_touches.touches_before(stmt_index, *temp))
        .filter(|temp| temp_touches.touches_after(stmt_index + 1, *temp))
        .collect()
}

fn summarize_block_fallthrough_assignments(block: &HirBlock) -> Option<FallthroughSummary> {
    let mut assigned_temps = BTreeSet::new();
    let mut falls_through = true;

    for stmt in &block.stmts {
        if !falls_through {
            break;
        }

        let stmt_summary = summarize_stmt_fallthrough_assignments(stmt)?;
        if stmt_summary.falls_through {
            assigned_temps.extend(stmt_summary.assigned_temps);
        } else {
            falls_through = false;
        }
    }

    Some(FallthroughSummary {
        falls_through,
        assigned_temps,
    })
}

fn summarize_stmt_fallthrough_assignments(stmt: &HirStmt) -> Option<FallthroughSummary> {
    match stmt {
        HirStmt::LocalDecl(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Label(_) => Some(FallthroughSummary {
            falls_through: true,
            assigned_temps: BTreeSet::new(),
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
        }),
        HirStmt::TableSetList(_) => None,
        HirStmt::Return(_) | HirStmt::Goto(_) | HirStmt::Break | HirStmt::Continue => {
            Some(FallthroughSummary {
                falls_through: false,
                assigned_temps: BTreeSet::new(),
            })
        }
        HirStmt::If(if_stmt) => {
            let else_block = if_stmt.else_block.as_ref()?;
            let then_summary = summarize_block_fallthrough_assignments(&if_stmt.then_block)?;
            let else_summary = summarize_block_fallthrough_assignments(else_block)?;
            let assigned_temps =
                intersect_fallthrough_assignment_sets([Some(&then_summary), Some(&else_summary)])
                    .unwrap_or_default();

            Some(FallthroughSummary {
                falls_through: then_summary.falls_through || else_summary.falls_through,
                assigned_temps,
            })
        }
        HirStmt::Block(block) => summarize_block_fallthrough_assignments(block),
        HirStmt::While(_)
        | HirStmt::Repeat(_)
        | HirStmt::NumericFor(_)
        | HirStmt::GenericFor(_)
        | HirStmt::Unstructured(_) => None,
    }
}

fn intersect_fallthrough_assignment_sets<'a>(
    summaries: impl IntoIterator<Item = Option<&'a FallthroughSummary>>,
) -> Option<BTreeSet<TempId>> {
    let mut fallthrough_sets = summaries
        .into_iter()
        .flatten()
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
