//! 校验作用域清理动作和关闭范围；依赖 lowered 指令、边计划与 scope payload，不负责推导清理；例如核对 TBC/CLOSE 的离开边。

use super::*;

pub(super) fn validate_cleanup(
    proto: &LoweredProto,
    cfg: &Cfg,
    plan: &StructurePlan,
) -> Result<(), StructureError> {
    crate::structure::scope::validate_cleanup_dispositions(proto, cfg, plan)?;
    for (loop_id, loop_) in plan.loops() {
        let Some(tail) = &loop_.exit_tail else {
            continue;
        };
        let has_control = (tail.range.start.index()..tail.range.end()).any(|index| {
            proto
                .instrs
                .get(index)
                .is_some_and(LowInstr::is_control_terminator)
        });
        // 位置/连续性由 loop validator 核对；这里只允许吞掉终末 Close，不能将
        // range 中的 TBC 注册或较早的独立 Close 按“cleanup 指令”一并删除。
        let cleanup_shape_is_valid = tail
            .cleanup
            .iter()
            .all(|instr| matches!(proto.instrs.get(instr.index()), Some(LowInstr::Close(_))));
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
    Ok(())
}
