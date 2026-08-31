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
    is_reserved: &dyn Fn(TempId) -> bool,
) -> Vec<TempId> {
    let HirStmt::If(if_stmt) = stmt else {
        return Vec::new();
    };
    let Some(else_block) = &if_stmt.else_block else {
        return Vec::new();
    };

    let then_summary = summarize_block_fallthrough_assignments(&if_stmt.then_block);
    let else_summary = summarize_block_fallthrough_assignments(else_block);
    // 证明缺陷[PotentialUnsoundness:ValueFlow]：summary 只证明两臂“曾写入”，未排除 condition/首次写前读取；`while t do if t then t=1 else t=2 end; use(t) end` 会在体内接受并把 if condition 改成读取新建的 nil local。
    let Some(common_temps) =
        intersect_fallthrough_assignment_sets([then_summary.as_ref(), else_summary.as_ref()])
    else {
        // 候选拒绝[ProofIncomplete]：两臂任一含当前 summary 不支持的 loop/SETLIST/nested-if-without-else 时整项放弃；应补 must-def/fallthrough CFG 摘要。
        return Vec::new();
    };

    common_temps
        .into_iter()
        .filter(|temp| !is_reserved(*temp))
        // 候选拒绝[SemanticBarrier:Lifetime]：`t=obj; if c then t=a else t=b end; GC` 若在 if 前另建 local，旧 t 物理槽不再按原时点覆盖，弱表/`__gc` 可观察旧对象延寿。
        .filter(|temp| !temp_touches.touches_before(stmt_index, *temp))
        // 候选拒绝[LayerBoundary]：合流后没有 touch 的 branch temp 是 dead-temps 的删除候选，不应物化为空 local。
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
        // 候选拒绝[ProofIncomplete]：SETLIST 本身不改 temp binding，但当前 summary 未证明其异常/控制效果后仍可继续收集 must-def；应接入语句 effect 摘要。
        HirStmt::TableSetList(_) => None,
        HirStmt::Return(_) | HirStmt::Goto(_) | HirStmt::Break | HirStmt::Continue => {
            Some(FallthroughSummary {
                falls_through: false,
                assigned_temps: BTreeSet::new(),
            })
        }
        HirStmt::If(if_stmt) => {
            // 候选拒绝[ProofIncomplete]：nested if 缺 else 时尚未计算其 fallthrough must-def，不能因为局部路径写入就宣称外层每条合流路径都有值。
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
        // 候选拒绝[ProofIncomplete]：loop 尚无 fallthrough 与 must-def 摘要；应复用 carried-locals 的结构化 exit 分析后继续扫描后缀。
        HirStmt::While(_)
        | HirStmt::Repeat(_)
        | HirStmt::NumericFor(_)
        | HirStmt::GenericFor(_) => None,
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
