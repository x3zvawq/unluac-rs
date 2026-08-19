//! 校验作用域清理动作和关闭范围；依赖 lowered 指令、边计划与 scope payload，不负责推导清理；例如核对 TBC/CLOSE 的离开边。

use super::*;

pub(super) fn validate_cleanup(
    proto: &LoweredProto,
    cfg: &Cfg,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    if plan.cleanup_dispositions.len() != proto.instrs.len() {
        return Err(StructureError::invalid(
            "cleanup disposition length mismatch",
        ));
    }
    let mut lexical_scope_by_cleanup = vec![None; proto.instrs.len()];
    for (scope_index, scope) in plan.scopes.iter().enumerate() {
        let scope_id = ScopePlanId(scope_index);
        for close in &scope.close_points {
            let Some(slot) = lexical_scope_by_cleanup.get_mut(close.index()) else {
                return Err(StructureError::invalid(format!(
                    "lexical scope #{scope_index} cleanup is outside the instruction arena"
                )));
            };
            if slot.replace(scope_id).is_some() {
                return Err(StructureError::invalid(format!(
                    "cleanup instruction @{} has multiple lexical scope owners",
                    close.index()
                )));
            }
        }
    }
    let mut tbc_scope_by_cleanup = vec![None; proto.instrs.len()];
    for (scope_index, scope) in plan.tbc_scopes.iter().enumerate() {
        let scope_id = super::super::TbcScopePlanId(scope_index);
        if scope.origins.is_empty() || !scope.origins.windows(2).all(|pair| pair[0] < pair[1]) {
            return Err(StructureError::invalid(format!(
                "TBC scope #{scope_index} is not canonical"
            )));
        }
        for (close, boundary) in std::iter::once((scope.boundary, true))
            .chain(scope.exits.iter().copied().map(|close| (close, false)))
        {
            let Some(slot) = tbc_scope_by_cleanup.get_mut(close.index()) else {
                return Err(StructureError::invalid(format!(
                    "TBC scope #{scope_index} cleanup is outside the instruction arena"
                )));
            };
            if slot.replace((scope_id, boundary)).is_some() {
                return Err(StructureError::invalid(format!(
                    "cleanup instruction @{} has multiple TBC scope owners",
                    close.index()
                )));
            }
        }
    }
    for (index, instr) in proto.instrs.iter().enumerate() {
        let disposition = plan.cleanup_dispositions[index];
        let is_cleanup = matches!(instr, LowInstr::Close(_) | LowInstr::Tbc(_));
        if is_cleanup != disposition.is_some() {
            return Err(StructureError::invalid(format!(
                "cleanup instruction @{index} does not have one dense disposition"
            )));
        }
        if !is_cleanup {
            continue;
        }
        let reachable = cfg
            .instr_to_block
            .get(index)
            .is_some_and(|block| cfg.reachable_blocks.contains(block));
        if matches!(disposition, Some(CleanupDisposition::Unreachable)) == reachable {
            return Err(StructureError::invalid(format!(
                "cleanup instruction @{index} reachability disposition is stale"
            )));
        }
        if let Some(CleanupDisposition::LoopTbcBoundary(region)) = disposition
            && !matches!(plan.region(region), Some(RegionPlan::Loop { .. }))
        {
            return Err(StructureError::invalid(format!(
                "cleanup instruction @{index} references a non-loop region"
            )));
        }
        if let Some(CleanupDisposition::LexicalScope(scope)) = disposition
            && lexical_scope_by_cleanup[index] != Some(scope)
        {
            return Err(StructureError::invalid(format!(
                "cleanup instruction @{index} lexical scope owner is stale"
            )));
        }
        match disposition {
            Some(CleanupDisposition::ExplicitTbcBoundary(scope))
                if tbc_scope_by_cleanup[index] != Some((scope, true)) =>
            {
                return Err(StructureError::invalid(format!(
                    "cleanup instruction @{index} TBC boundary owner is stale"
                )));
            }
            Some(CleanupDisposition::ExplicitTbcExit(scope))
                if tbc_scope_by_cleanup[index] != Some((scope, false)) =>
            {
                return Err(StructureError::invalid(format!(
                    "cleanup instruction @{index} TBC exit owner is stale"
                )));
            }
            _ => {}
        }
    }
    for (loop_id, loop_) in plan.loops() {
        let Some(tail) = &loop_.exit_tail else {
            continue;
        };
        let actual_cleanup = (tail.range.start.index()..tail.range.end())
            .filter(|index| {
                matches!(
                    proto.instrs.get(*index),
                    Some(LowInstr::Close(_) | LowInstr::Tbc(_))
                )
            })
            .map(crate::transformer::InstrRef)
            .collect::<Vec<_>>();
        let has_control = (tail.range.start.index()..tail.range.end()).any(|index| {
            proto
                .instrs
                .get(index)
                .is_some_and(LowInstr::is_control_terminator)
        });
        let cleanup_shape_is_valid = if tail.cleanup_block == tail.block {
            actual_cleanup == tail.cleanup
        } else {
            actual_cleanup.is_empty()
                && tail.cleanup.iter().all(|instr| {
                    matches!(proto.instrs.get(instr.index()), Some(LowInstr::Close(_)))
                })
        };
        if !cleanup_shape_is_valid
            || tail.cleanup.is_empty()
            || has_control
            || tail.cleanup.iter().any(|instr| {
                matches!(
                    plan.cleanup_disposition(*instr),
                    None | Some(CleanupDisposition::Unreachable)
                )
            })
        {
            return Err(StructureError::invalid(format!(
                "loop payload #{} has a stale executable exit-tail range",
                loop_id.index()
            )));
        }
    }
    for (index, edge_plan) in plan.edge_plans.iter().enumerate() {
        let EdgeActionPlacement::BeforeTrailingCleanup { cleanup } = edge_plan.action_placement
        else {
            continue;
        };
        let edge = &cfg.edges[index];
        let block_range = cfg.blocks[edge.from.index()].instrs;
        let Some(terminator) = block_range.last() else {
            return Err(StructureError::invalid(format!(
                "edge #{index} cleanup placement source is empty"
            )));
        };
        let cleanup_is_exact = cleanup.end() == terminator.index()
            && (cleanup.start.index()..cleanup.end()).all(|instr| {
                matches!(
                    proto.instrs.get(instr),
                    Some(LowInstr::Close(_) | LowInstr::Tbc(_))
                )
            })
            && cleanup.start.index() > block_range.start.index()
            && !matches!(
                proto.instrs.get(cleanup.start.index() - 1),
                Some(LowInstr::Close(_) | LowInstr::Tbc(_))
            );
        if edge_plan.phi_copies.is_empty()
            || !matches!(
                proto.instrs.get(terminator.index()),
                Some(LowInstr::Jump(_))
            )
            || !cleanup_is_exact
            || (cleanup.start.index()..cleanup.end()).any(|instr| {
                matches!(
                    plan.cleanup_disposition(crate::transformer::InstrRef(instr)),
                    None | Some(CleanupDisposition::Unreachable)
                )
            })
        {
            return Err(StructureError::invalid(format!(
                "edge #{index} trailing-cleanup action contract is stale"
            )));
        }
    }
    Ok(())
}
