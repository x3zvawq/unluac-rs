//! 这个文件实现区域事实提取。
//!
//! 可规约的 loop/branch 已由各自候选和 StructurePlan 表达；这里仅把不可规约 SCC
//! 收敛为 `RegionFact`，供后续 HIR 查询 entry/exit 与成员边界。
//! 它不会重复保存线性块或可结构化区域，也不会越权恢复最终语法。
//!
//! 例子：
//! - 一个自然循环或普通 if/else 不会再额外产出 RegionFact
//! - 一个多入口 SCC 会产出一条 RegionFact

use crate::structure::Cfg;

use super::common::{IrreducibleRegion, RegionFact};
use super::helpers::collect_region_exits;

pub(super) fn analyze_regions(
    cfg: &Cfg,
    irreducible_regions: &[IrreducibleRegion],
) -> Vec<RegionFact> {
    let mut regions = irreducible_regions
        .iter()
        .map(|irreducible| RegionFact {
            blocks: irreducible.blocks.clone(),
            entry: irreducible.entry,
            exits: collect_region_exits(cfg, &irreducible.blocks),
        })
        .collect::<Vec<_>>();

    regions.sort_by_key(|region| region.entry);
    regions
}
