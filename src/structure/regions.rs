//! 这个文件实现区域事实提取。
//!
//! 它依赖 loop/branch/irreducible region 已经给好的结构边界，负责把这些候选收敛成
//! `RegionFact` 这张“结构地图”，供后续 HIR 直接查询 entry/exit、reducible 和
//! structureable 等稳定事实。
//! 它不会越权恢复最终语法，只表达区域边界和可结构化程度。
//!
//! 例子：
//! - 一个自然循环会产出 `LoopRegion`
//! - 一个多入口 SCC 会产出 `Irreducible`
//! - 一个有明确 merge 的普通 if/else 区域会产出 `BranchRegion`

use std::collections::BTreeSet;

use crate::cfg::Cfg;

use super::common::{BranchRegionFact, IrreducibleRegion, LoopCandidate, RegionFact, RegionKind};
use super::helpers::collect_region_exits;

pub(super) fn analyze_regions(
    cfg: &Cfg,
    loop_candidates: &[LoopCandidate],
    branch_regions: &[BranchRegionFact],
    irreducible_regions: &[IrreducibleRegion],
) -> Vec<RegionFact> {
    let mut regions = Vec::new();
    let mut covered = BTreeSet::new();

    for loop_candidate in loop_candidates {
        covered.extend(loop_candidate.blocks.iter().copied());
        regions.push(RegionFact {
            blocks: loop_candidate.blocks.clone(),
            entry: loop_candidate.header,
            exits: loop_candidate.exits.clone(),
            kind: RegionKind::LoopRegion,
            reducible: loop_candidate.reducible,
            structureable: loop_candidate.reducible,
        });
    }

    for irreducible in irreducible_regions {
        covered.extend(irreducible.blocks.iter().copied());
        regions.push(RegionFact {
            blocks: irreducible.blocks.clone(),
            entry: irreducible.entry,
            exits: collect_region_exits(cfg, &irreducible.blocks),
            kind: RegionKind::Irreducible,
            reducible: false,
            structureable: false,
        });
    }

    for branch_region in branch_regions {
        if branch_region.structured_blocks.len() <= 1 {
            continue;
        }

        covered.extend(branch_region.structured_blocks.iter().copied());
        regions.push(RegionFact {
            blocks: branch_region.structured_blocks.clone(),
            entry: branch_region.header,
            exits: BTreeSet::from([branch_region.merge]),
            kind: RegionKind::BranchRegion,
            reducible: true,
            structureable: true,
        });
    }

    for block in cfg.block_order.iter().copied() {
        if !cfg.reachable_blocks.contains(&block) || covered.contains(&block) {
            continue;
        }

        let exits = cfg.succs[block.index()]
            .iter()
            .map(|edge_ref| cfg.edges[edge_ref.index()].to)
            .filter(|to| cfg.reachable_blocks.contains(to))
            .collect();
        regions.push(RegionFact {
            blocks: BTreeSet::from([block]),
            entry: block,
            exits,
            kind: RegionKind::Linear,
            reducible: true,
            structureable: true,
        });
    }

    regions.sort_by_key(|region| (region.entry, region.kind));
    regions
}
