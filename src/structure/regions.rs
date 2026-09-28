//! 从不可规约 SCC 提取区域成员与出入边事实。
//!
//! 向最终结构计划发布 RegionFact，可规约的 loop/branch 仍由各自 owner 表达。

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
