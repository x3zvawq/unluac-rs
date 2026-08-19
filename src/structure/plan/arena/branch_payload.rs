//! branch payload 的最终冻结。输入选定 condition、edge plan 与 branch evidence，输出唯一 BranchPlanData；不负责重新选择 condition。例如真假出口会在这里对齐 then polarity 与 continuation。

use super::*;

pub(super) fn freeze_branch_payload(
    cfg: &Cfg,
    edge_plans: &[EdgePlan],
    evidence: &super::super::BranchPlanInput,
    condition: super::super::ConditionPlanId,
    condition_plan: Option<&super::super::ConditionPlan>,
    single_pass_exit: Option<BlockRef>,
) -> Result<super::super::BranchPlanData, StructureError> {
    let condition_plan = condition_plan.ok_or_else(|| {
        StructureError::invalid("selected branch is missing its frozen condition plan")
    })?;
    let (truthy, falsy) = (condition_plan.truthy, condition_plan.falsy);
    let truthy_target =
        condition_transfer_target(cfg, condition_plan, truthy).ok_or_else(|| {
            StructureError::invalid("selected branch truthy transfer has no terminal condition arc")
        })?;
    let falsy_target = condition_transfer_target(cfg, condition_plan, falsy).ok_or_else(|| {
        StructureError::invalid("selected branch falsy transfer has no terminal condition arc")
    })?;
    let then_is_truthy = resolve_branch_then_polarity(
        &evidence.branch,
        truthy_target,
        falsy_target,
        condition_plan
            .blocks()
            .any(|block| block == evidence.branch.then_entry),
        single_pass_exit,
    )
    .ok_or_else(|| {
        StructureError::invalid(format!(
            "selected branch arm does not match its condition exits: header=#{} then-entry=#{} truthy-edge={} truthy-target=#{} falsy-edge={} falsy-target=#{}",
            evidence.branch.header.index(),
            evidence.branch.then_entry.index(),
            truthy,
            truthy_target.index(),
            falsy,
            falsy_target.index(),
        ))
    })?;
    let (condition_inverted, then_edge, else_edge) = if then_is_truthy {
        (false, truthy, falsy)
    } else {
        (true, falsy, truthy)
    };
    for edge in [then_edge, else_edge] {
        if edge_plans.get(edge.index()).is_none() {
            return Err(StructureError::invalid(
                "selected branch references a missing final edge plan",
            ));
        }
    }
    Ok(super::super::BranchPlanData {
        header: evidence.branch.header,
        kind: evidence.branch.kind,
        condition,
        condition_inverted,
        then_edge,
        else_edge,
        continuation: evidence.branch.merge,
        value_plan: evidence
            .value_merge
            .as_ref()
            .map(|value| super::super::BranchValuePlan {
                merge: value.merge,
                values: value.values.clone(),
            }),
    })
}

pub(super) fn condition_transfer_target(
    cfg: &Cfg,
    condition: &super::super::ConditionPlan,
    transfer: EdgeRef,
) -> Option<BlockRef> {
    condition
        .nodes
        .iter()
        .flat_map(|node| node.arcs.iter())
        .find(|arc| {
            arc.transfer == transfer
                && matches!(
                    arc.target,
                    super::super::ConditionTarget::Truthy | super::super::ConditionTarget::Falsy
                )
        })
        .and_then(|arc| arc.route.last())
        .and_then(|edge| cfg.edges.get(edge.index()))
        .map(|edge| edge.to)
}

pub(super) fn resolve_branch_then_polarity(
    branch: &BranchCandidate,
    truthy: BlockRef,
    falsy: BlockRef,
    then_entry_is_condition_block: bool,
    single_pass_exit: Option<BlockRef>,
) -> Option<bool> {
    if branch.then_entry == truthy {
        return Some(true);
    }
    if branch.then_entry == falsy {
        return Some(false);
    }
    if !then_entry_is_condition_block {
        return None;
    }

    // 短路折叠后，旧候选的 then_entry 可能成为 condition 内部节点。单臂分支的
    // continuation 才是此时可靠的边界：另一出口必须是源码 arm，不能继续沿用折叠前
    // 针对首个物理 branch 的 invert_hint。
    if branch.else_entry.is_none() {
        for boundary in [single_pass_exit, branch.merge].into_iter().flatten() {
            match (truthy == boundary, falsy == boundary) {
                (true, false) => return Some(false),
                (false, true) => return Some(true),
                _ => {}
            }
        }
    }
    Some(!branch.invert_hint)
}
