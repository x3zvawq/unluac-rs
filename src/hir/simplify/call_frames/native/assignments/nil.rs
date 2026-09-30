//! 把原批量 nil 准备与逆序低槽写回恢复为单条并列赋值。
//! 消费 Promotion 的整组协议；准备声明和全部写回由同一次 native preview 退休。

use super::*;
use crate::hir::promotion::NativeNilAssignmentFrame;

pub(in crate::hir::simplify::call_frames::native) fn collect(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    flat: &[Option<FlatStmt<'_>>],
) -> Vec<Plan> {
    if dialect == DecompileDialect::Luau {
        // TargetConstraint：Luau 的并列写回协议不使用这组逆序 LOADNIL/MOVE 帧。
        return Vec::new();
    }
    let mut frames = BTreeMap::<LocalId, Option<&NativeNilAssignmentFrame>>::new();
    for frame in facts.nil_assignment_frames() {
        if let Some(local) = facts.promoted_local_for_temp(frame.writes[0].source) {
            frames
                .entry(local)
                .and_modify(|frame| *frame = None)
                .or_insert(Some(frame));
        }
    }
    let mut plans = Vec::new();
    let mut index = 0;
    while index < flat.len() {
        let start = index;
        index += 1;
        let Some(first) = flat[start] else { continue };
        let HirStmt::LocalDecl(decl) = first.stmt else {
            continue;
        };
        let Some(frame) = decl
            .bindings
            .first()
            .and_then(|local| frames.get(local))
            .copied()
            .flatten()
        else {
            continue;
        };
        let end = start + frame.writes.len() + 2;
        let Some(window) = flat.get(start..end) else {
            continue;
        };
        if let Some(plan) = candidate(context, facts, frame, window) {
            plans.push(plan);
            index = end;
        }
    }
    plans
}

fn candidate(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    frame: &NativeNilAssignmentFrame,
    window: &[Option<FlatStmt<'_>>],
) -> Option<Plan> {
    let first = window.first().copied().flatten()?;
    let HirStmt::LocalDecl(decl) = first.stmt else {
        return None;
    };
    let width = frame.writes.len();
    if decl.bindings.len() != width
        || decl.values.tail.is_some()
        || decl.values.fixed.len() != width
        || !decl.values.fixed.iter().all(|value| *value == HirExpr::Nil)
    {
        // ProofIncomplete：只能消费完整原批次；先核对宽度，扫描成本由当前声明大小界定。
        return None;
    }
    let entries = window.iter().copied().collect::<Option<Vec<_>>>()?;
    if !entries
        .iter()
        .enumerate()
        .all(|(offset, entry)| entry.id == first.id + offset && plain_copy(entry.stmt))
    {
        // SemanticBarrier:Scope：原写必须相邻，不跨词法边界或其它事件。
        return None;
    }
    let mut targets = Vec::with_capacity(width + 1);
    for ((local, write), entry) in decl
        .bindings
        .iter()
        .zip(&frame.writes)
        .zip(entries[2..].iter().rev())
    {
        let home = facts.trusted_temp_home_slot(write.source)?;
        let target = facts.promoted_local_for_temp(write.target)?;
        if facts.promoted_local_for_temp(write.source) != Some(*local)
            || facts.trusted_local_home_slot(*local) != Some(home)
            || facts.trusted_local_home_slot(target) != Some(write.home)
            || !facts
                .complete_local_definition_write_homes(*local)
                .iter()
                .copied()
                .eq([home])
            || context.barred.contains(&home)
            || context.closed.contains(&home)
            || context.proto.local_debug_hints[local.index()].is_some()
            || context.proto.local_debug_scopes[local.index()].is_some()
            || matches!(context.proto.inline_dispositions.local(*local),
                crate::hir::common::HirInlineDisposition::Preserve(reasons)
                    if reasons.iter().any(|reason| *reason != HirInlineRetentionReason::PhysicalFramePrefix))
            || !matches!(entry.stmt, HirStmt::Assign(assign)
                if assign.targets.as_slice() == [HirLValue::Local(target)]
                    && assign.values.fixed.as_slice() == [HirExpr::LocalRef(*local)]
                    && assign.values.tail.is_none())
        {
            // SemanticBarrier:Binding：只能退休匿名原准备；保留目标 identity 与原写入顺序。
            return None;
        }
        targets.push(HirLValue::Local(target));
    }
    let last = facts.promoted_local_for_temp(frame.last)?;
    if facts.trusted_local_home_slot(last) != Some(frame.last_home)
        || !matches!(entries[1].stmt, HirStmt::Assign(assign)
            if assign.targets.as_slice() == [HirLValue::Local(last)]
                && assign.values.fixed.as_slice() == [HirExpr::Nil]
                && assign.values.tail.is_none())
    {
        return None;
    }
    targets.push(HirLValue::Local(last));
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start: first.id,
        sink: entries.last()?.id,
        base: frame.base,
        values: vec![HirExpr::Nil; width + 1].into(),
        result_locals: Vec::new(),
        assignment_targets: targets,
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: entries[1..entries.len() - 1]
            .iter()
            .map(|entry| entry.id)
            .collect(),
        removed: entries[..entries.len() - 1]
            .iter()
            .map(|entry| entry.id)
            .collect(),
    })
}
