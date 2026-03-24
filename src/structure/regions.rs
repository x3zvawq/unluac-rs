//! 这个文件实现区域事实提取。
//!
//! RegionFact 是后续 HIR 决策的“地图”，因此这里保持保守，只产出 entry/exit、
//! reducible 和 structureable 等稳定事实。

use std::collections::BTreeSet;

use crate::cfg::{Cfg, GraphFacts};

use super::branches::collect_branch_region_blocks;
use super::common::{BranchCandidate, LoopCandidate, RegionFact, RegionKind};
use super::helpers::{IrreducibleRegion, collect_region_exits};

pub(super) fn analyze_regions(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    loop_candidates: &[LoopCandidate],
    branch_candidates: &[BranchCandidate],
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

    for branch_candidate in branch_candidates {
        let Some(merge) = branch_candidate.merge else {
            continue;
        };

        let region_blocks = collect_branch_region_blocks(
            cfg,
            branch_candidate,
            merge,
            Some(&graph_facts.dominator_tree.parent),
        );
        if region_blocks.len() <= 1 {
            continue;
        }

        covered.extend(region_blocks.iter().copied());
        regions.push(RegionFact {
            blocks: region_blocks,
            entry: branch_candidate.header,
            exits: BTreeSet::from([merge]),
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
