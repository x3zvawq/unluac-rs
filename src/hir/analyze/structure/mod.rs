//! HIR 结构恢复 facade：只消费最终 StructurePlan。

mod generic_for;
mod plan_body;

use crate::hir::HirLowerError;
use crate::hir::common::{HirBlock, HirProtoRef};

use super::lower::ProtoLowering;

/// 基于 StructurePlan 恢复一个更接近源码的 HIR block。
pub(super) fn build_structured_body(
    proto: HirProtoRef,
    lowering: &ProtoLowering<'_>,
) -> Result<HirBlock, HirLowerError> {
    plan_body::build_planned_body(proto, lowering)
}
