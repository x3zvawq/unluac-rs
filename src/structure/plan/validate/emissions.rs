//! 校验最终基本块发射计划；依赖 CFG 块表，不负责控制流边分类；例如拒绝缺失或重复的块发射项。

use super::*;

pub(super) fn validate_block_emissions(
    cfg: &Cfg,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    if plan.block_emissions.len() != cfg.blocks.len() {
        return Err(StructureError::invalid(
            "block emission arena length mismatch",
        ));
    }
    for index in 0..cfg.blocks.len() {
        let block = BlockRef(index);
        let expected = super::super::expected_block_emission(cfg, plan, block)?;
        let actual = plan.block_emissions[index];
        if actual != expected {
            return Err(StructureError::invalid(format!(
                "block {block} emission is stale: actual={actual:?}, expected={expected:?}"
            )));
        }
        if matches!(actual, BlockEmissionPlan::ForwardedControl { .. })
            && plan.label_for_block(block).is_some()
        {
            return Err(StructureError::invalid(format!(
                "forwarded block {block} owns a planned label"
            )));
        }
    }
    Ok(())
}
