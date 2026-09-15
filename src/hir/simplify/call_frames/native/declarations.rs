//! 同一 Luau local 声明的多个构造目标与共享 RHS 暂存区。
//!
//! Promotion 提供 allocation/record/SETLIST 的真实 home，构造器 owner 提供最后写入边界；
//! 本模块只组织完整帧事务，字段、Def 版本与事件仍由 FrameBuilder 核对，源码低槽
//! 前缀和被消费身份的后继使用仍由 native preview 核对。
//! 例如 r8/r9 两个外层表分别借用 r10 构造 nested，必须输出
//! `local a,b={nested={}},{nested={}}`；拆成两条声明会把第一份 scratch 移到 r9。
//! 开放数组同样预留整组目标，例如 `local a,b={f()},{g()}` 的两个 CALL/SETLIST
//! 都使用组末缓冲；buffer 高于第一个 table 不单独证明分组，仍须覆盖所有连续目标。
//! 整组目标连续且每个原 RHS 都在共同 top 求值时，才允许收回中间声明。扫描按完整
//! 构造区向前推进，不对每个嵌套 seed 反复重建同一窗口。

use super::*;
use crate::hir::simplify::table_constructors::{ConstructorWrite, constructor_write};

pub(super) fn collect(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    flat: &[Option<FlatStmt<'_>>],
    empty: &BTreeSet<usize>,
    ends: &BTreeMap<usize, usize>,
    arguments: &BTreeSet<LocalId>,
) -> Vec<Plan> {
    if dialect != DecompileDialect::Luau {
        return Vec::new();
    }
    let mut plans = Vec::new();
    let mut cursor = 0;
    while cursor < flat.len() {
        let start = cursor;
        cursor += 1;
        let Some(entry) = flat[start] else { continue };
        let Some((_, table)) = declaration(entry.stmt) else {
            continue;
        };
        let Some(base) = facts.allocation_result_home(table) else {
            continue;
        };
        let Some(&first_end) = ends.get(&start) else {
            continue;
        };
        let Some(write) = flat[first_end].and_then(|entry| constructor_write(entry.stmt)) else {
            continue;
        };
        let top = match write {
            ConstructorWrite::Record { access, .. } => {
                let Some(layout) = facts.native_table_write_layout(access) else {
                    continue;
                };
                if layout.base != base || layout.key.is_some() {
                    continue;
                }
                let Some(top) = layout.value else { continue };
                top
            }
            ConstructorWrite::Batch { batch, .. } => {
                let Some(layout) = facts.native_table_batch_layout(batch) else {
                    continue;
                };
                if layout.base != base {
                    continue;
                }
                layout.buffer
            }
        };
        if top.slot() <= base.slot() + 1 {
            continue;
        }
        let width = top.slot() - base.slot();
        let mut seeds = Vec::new();
        let mut next = start;
        for offset in 0..width {
            while flat
                .get(next)
                .and_then(|entry| *entry)
                .is_some_and(|entry| empty.contains(&entry.id))
            {
                next += 1;
            }
            let Some(entry) = flat.get(next).and_then(|entry| *entry) else {
                break;
            };
            let Some((local, table)) = declaration(entry.stmt) else {
                break;
            };
            let home = HomeSlotKey::new(base.slot() + offset, 0);
            if facts.trusted_local_home_slot(local) != Some(home)
                || facts.allocation_result_home(table) != Some(home)
                || arguments.contains(&local)
            {
                break;
            }
            let Some(&end) = ends.get(&next) else { break };
            seeds.push((next, local));
            next = end + 1;
        }
        // 即使整组拒绝，也不从其内部的每个 seed 重试同一增长窗口。
        cursor = cursor.max(next);
        if seeds.len() != width {
            continue;
        }
        let end = next - 1;
        let mut run = Vec::new();
        let mut positions = Vec::with_capacity(width);
        let mut seed_iter = seeds.iter().peekable();
        let mut boundary = false;
        for (offset, entry) in flat[start..=end].iter().enumerate() {
            let Some(entry) = entry else {
                boundary = true;
                break;
            };
            if seed_iter
                .peek()
                .is_some_and(|(seed, _)| *seed == start + offset)
            {
                positions.push(run.len());
                seed_iter.next();
            }
            if !empty.contains(&entry.id) {
                run.push(entry.stmt);
            }
        }
        if boundary {
            continue;
        }
        let Some(mut builder) = frame_builder(context, &run, facts, dialect, base.slot()) else {
            continue;
        };
        builder.constructor_reserved_top = Some(top.slot());
        let values = positions
            .iter()
            .enumerate()
            .map(|(offset, &seed)| {
                let (_, table) = declaration(run[seed])?;
                builder.constructor(seed, table, base.slot() + offset)
            })
            .collect::<Option<Vec<_>>>();
        let Some(values) = values else { continue };
        if builder.first_event != Some(0) || builder.next_event != run.len() {
            continue;
        }
        plans.push(Plan {
            start: flat[start].unwrap().id,
            sink: flat[end].unwrap().id,
            base,
            values: values.into(),
            result_locals: seeds.into_iter().map(|(_, local)| local).collect(),
            discarded_result: None,
            assignment_targets: Vec::new(),
            indexed_target: None,
            continuing_root: None,
            retained_copies: Vec::new(),
            removed: flat[start..end]
                .iter()
                .map(|entry| entry.unwrap().id)
                .collect(),
        });
    }
    plans
}

fn declaration(stmt: &HirStmt) -> Option<(LocalId, &crate::hir::common::HirTableConstructor)> {
    let HirStmt::LocalDecl(decl) = stmt else {
        return None;
    };
    let ([local], [HirExpr::TableConstructor(table)], None) = (
        decl.bindings.as_slice(),
        decl.values.fixed.as_slice(),
        &decl.values.tail,
    ) else {
        return None;
    };
    matches!(
        table.allocation,
        HirTableAllocation::LuauTemplate { .. } | HirTableAllocation::Luau(_)
    )
    .then_some((*local, table))
}
