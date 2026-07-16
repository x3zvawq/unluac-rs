//! 这个文件把平铺的结构候选收敛成可按索引查询的执行 owner 计划。
//!
//! 候选提取允许 branch、loop 与 irreducible region 重叠；这里为每个 block 和 edge
//! 选择唯一的直接 owner，并保留 same-header loop 的稳定 candidate identity。HIR 只应
//! 消费这个计划，不能再用临时 map 的覆盖顺序代替结构决策。
//!
//! 输入形状：一个 branch region 与多入口 SCC 在部分 block 上重叠。
//! 输出形状：SCC membership 与直接 owner 分开；其中可规约 header 仍归 `Branch/Loop`，
//! 其余成员归 `Unstructured`，每条 CFG edge 同时得到唯一 owner。

use std::{cmp::Reverse, collections::BTreeMap};

use super::{
    BlockRef, BranchCandidate, BranchValueMergeCandidate, Cfg, EdgeKind, GotoRequirement,
    GraphFacts, LoopCandidate, RegionFact, StructurePlan, UnstructuredRegionLayout,
};
use crate::transformer::{LowInstr, LoweredProto};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BranchCandidateId(pub usize);

impl BranchCandidateId {
    pub const fn index(self) -> usize {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BranchValueMergeId(pub usize);

impl BranchValueMergeId {
    pub const fn index(self) -> usize {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GotoRequirementId(pub usize);

impl GotoRequirementId {
    pub const fn index(self) -> usize {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LoopCandidateId(pub usize);

impl LoopCandidateId {
    pub const fn index(self) -> usize {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RegionId(pub usize);

impl RegionId {
    pub const fn index(self) -> usize {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ScopeCandidateId(pub usize);

impl ScopeCandidateId {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// 一条 cleanup 指令的唯一语义归属；不可达指令也显式分类。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CleanupDisposition {
    Unreachable,
    ExplicitTbc,
    GenericFor(LoopCandidateId),
    ExplicitTbcBoundary,
    LexicalScope(ScopeCandidateId),
}

/// 一个 block 的直接 lowering owner；父子 region 包含关系不在这里重复表达。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockOwner {
    Unreachable,
    Linear,
    Branch(BranchCandidateId),
    Loop(LoopCandidateId),
    Unstructured(RegionId),
    Exit,
}

/// 一条 CFG edge 的唯一控制 owner。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EdgeOwner {
    Unreachable,
    Linear,
    Branch(BranchCandidateId),
    Loop(LoopCandidateId),
    Unstructured(RegionId),
    Goto(GotoRequirementId),
    Terminal,
}

/// 一个 canonical phi incoming 的唯一执行归属。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PhiIncomingDisposition {
    /// 整个 phi 没有可观察消费者，不生成任何写回。
    Dead,
    /// incoming 对应不可达 CFG 边，不参与生成。
    Unreachable,
    /// 显式 goto / island 边在离开 predecessor 时写入 phi target。
    EdgeCopy,
    /// 由目标 block 的 branch/loop/short-circuit/generic merge owner 消费。
    Merge,
}

pub(super) fn build_structure_plan(
    cfg: &Cfg,
    branch_candidates: &[BranchCandidate],
    branch_value_merges: &[BranchValueMergeCandidate],
    loop_candidates: &[LoopCandidate],
    goto_requirements: &[GotoRequirement],
    regions: &[RegionFact],
    cleanup_dispositions: Vec<Option<CleanupDisposition>>,
) -> StructurePlan {
    let branch_by_header = branch_candidates
        .iter()
        .enumerate()
        .map(|(index, candidate)| (candidate.header, BranchCandidateId(index)))
        .collect::<BTreeMap<_, _>>();
    assert_eq!(
        branch_by_header.len(),
        branch_candidates.len(),
        "branch headers must be unique"
    );
    let branch_value_merge_by_region = branch_value_merges
        .iter()
        .enumerate()
        .map(|(index, candidate)| {
            (
                (candidate.header, candidate.merge),
                BranchValueMergeId(index),
            )
        })
        .collect::<BTreeMap<_, _>>();
    assert_eq!(
        branch_value_merge_by_region.len(),
        branch_value_merges.len(),
        "branch value merge regions must be unique"
    );
    let branch_value_merge_by_header = branch_candidates
        .iter()
        .filter_map(|branch| {
            let merge = branch.merge?;
            branch_value_merge_by_region
                .get(&(branch.header, merge))
                .copied()
                .map(|id| (branch.header, id))
        })
        .collect::<BTreeMap<_, _>>();

    let mut loops_by_header = BTreeMap::<BlockRef, Vec<LoopCandidateId>>::new();
    for (index, candidate) in loop_candidates.iter().enumerate() {
        loops_by_header
            .entry(candidate.header)
            .or_default()
            .push(LoopCandidateId(index));
    }

    let mut block_owners = vec![BlockOwner::Unreachable; cfg.blocks.len()];
    for block in &cfg.reachable_blocks {
        block_owners[block.index()] = BlockOwner::Linear;
    }
    if let Some(owner) = block_owners.get_mut(cfg.exit_block.index()) {
        *owner = BlockOwner::Exit;
    }

    let mut unstructured_region_by_block = vec![None; cfg.blocks.len()];
    for (index, region) in regions.iter().enumerate() {
        if region.structureable {
            continue;
        }
        let region_id = RegionId(index);
        for block in &region.blocks {
            assert!(
                unstructured_region_by_block[block.index()].is_none(),
                "unstructured regions must not overlap at block {block}"
            );
            unstructured_region_by_block[block.index()] = Some(region_id);
        }
    }

    for (index, candidate) in branch_candidates.iter().enumerate() {
        let owner = &mut block_owners[candidate.header.index()];
        match owner {
            BlockOwner::Linear => *owner = BlockOwner::Branch(BranchCandidateId(index)),
            BlockOwner::Branch(_) => panic!("branch headers must be unique: {}", candidate.header),
            BlockOwner::Unreachable
            | BlockOwner::Loop(_)
            | BlockOwner::Unstructured(_)
            | BlockOwner::Exit => {
                panic!(
                    "branch header owner assigned out of order: {}",
                    candidate.header
                )
            }
        }
    }

    for (header, candidate_ids) in &loops_by_header {
        let selected = candidate_ids
            .iter()
            .copied()
            .max_by_key(|id| {
                (
                    loop_candidates[id.index()].blocks.len(),
                    Reverse(id.index()),
                )
            })
            .expect("loop header must have at least one candidate");
        let owner = &mut block_owners[header.index()];
        match owner {
            BlockOwner::Linear | BlockOwner::Branch(_) | BlockOwner::Loop(_) => {
                *owner = BlockOwner::Loop(selected);
            }
            BlockOwner::Unreachable | BlockOwner::Unstructured(_) | BlockOwner::Exit => {
                panic!("loop header must be a reachable non-exit block: {header}");
            }
        }
    }

    for (index, region) in unstructured_region_by_block.iter().copied().enumerate() {
        let Some(region) = region else {
            continue;
        };
        match &mut block_owners[index] {
            owner @ BlockOwner::Linear => *owner = BlockOwner::Unstructured(region),
            BlockOwner::Branch(_) | BlockOwner::Loop(_) => {}
            BlockOwner::Unreachable | BlockOwner::Unstructured(_) | BlockOwner::Exit => {
                panic!("invalid unstructured region member block #{index}");
            }
        }
    }

    let mut edge_owners = cfg
        .edges
        .iter()
        .map(|edge| match block_owners[edge.from.index()] {
            BlockOwner::Unreachable => EdgeOwner::Unreachable,
            BlockOwner::Branch(id) => EdgeOwner::Branch(id),
            BlockOwner::Loop(id) => EdgeOwner::Loop(id),
            BlockOwner::Unstructured(id) => EdgeOwner::Unstructured(id),
            BlockOwner::Linear | BlockOwner::Exit => match edge.kind {
                EdgeKind::Return | EdgeKind::TailCall => EdgeOwner::Terminal,
                _ => EdgeOwner::Linear,
            },
        })
        .collect::<Vec<_>>();

    let mut loop_ids = (0..loop_candidates.len())
        .map(LoopCandidateId)
        .collect::<Vec<_>>();
    loop_ids.sort_by_key(|id| (loop_candidates[id.index()].blocks.len(), id.index()));
    for id in loop_ids {
        let candidate = &loop_candidates[id.index()];
        for edge in candidate
            .backedges
            .iter()
            .chain(candidate.continue_edges.iter())
        {
            if !matches!(
                edge_owners[edge.index()],
                EdgeOwner::Unreachable | EdgeOwner::Unstructured(_) | EdgeOwner::Loop(_)
            ) {
                edge_owners[edge.index()] = EdgeOwner::Loop(id);
            }
        }
    }

    for (index, requirement) in goto_requirements.iter().enumerate() {
        let owner = &mut edge_owners[requirement.edge.index()];
        assert!(
            !matches!(owner, EdgeOwner::Goto(_)),
            "a CFG edge must have at most one goto requirement: {}",
            requirement.edge
        );
        *owner = EdgeOwner::Goto(GotoRequirementId(index));
    }

    validate_plan(
        cfg,
        goto_requirements,
        &unstructured_region_by_block,
        &block_owners,
        &edge_owners,
        &cleanup_dispositions,
    );

    StructurePlan {
        branch_by_header,
        branch_value_merge_by_header,
        branch_value_merge_by_region,
        loops_by_header,
        unstructured_region_by_block,
        unstructured_layouts: Vec::new(),
        unstructured_layout_by_block: Vec::new(),
        block_owners,
        edge_owners,
        cleanup_dispositions,
        generic_phi_materializations: Vec::new(),
        generic_phi_materializations_by_block: Vec::new(),
        phi_incoming_dispositions: Vec::new(),
        phi_edge_copies: Vec::new(),
    }
}

pub(super) fn install_unstructured_region_layouts(
    plan: &mut StructurePlan,
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    regions: &[RegionFact],
) {
    let mut layouts = vec![None; regions.len()];
    let mut layout_by_block = vec![None; cfg.blocks.len()];
    for (index, region) in regions.iter().enumerate() {
        if region.structureable {
            continue;
        }
        let region_id = RegionId(index);
        let Some(layout) = build_unstructured_region_layout(plan, proto, cfg, graph_facts, region)
        else {
            continue;
        };
        for block in &layout.blocks {
            let owner = &mut layout_by_block[block.index()];
            assert!(
                owner.is_none() || *owner == Some(region_id),
                "unstructured layouts must not overlap at {block}"
            );
            *owner = Some(region_id);
        }
        layouts[index] = Some(layout);
    }
    plan.unstructured_layouts = layouts;
    plan.unstructured_layout_by_block = layout_by_block;
}

fn build_unstructured_region_layout(
    plan: &StructurePlan,
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    region: &RegionFact,
) -> Option<UnstructuredRegionLayout> {
    let mut continuation = region.entry;
    while region.blocks.contains(&continuation) {
        continuation = graph_facts.post_dominator_tree.parent[continuation.index()]?;
    }

    let mut blocks = region.blocks.clone();
    for exit in &region.exits {
        let mut block = *exit;
        while block != continuation {
            if blocks.contains(&block) {
                break;
            }
            if !matches!(plan.block_owners[block.index()], BlockOwner::Linear)
                || !unstructured_exit_pad_prefix_is_cleanup(plan, proto, cfg, block)
            {
                return None;
            }
            blocks.insert(block);
            block = cfg.unique_reachable_successor(block)?;
        }
    }
    blocks.remove(&continuation);
    Some(UnstructuredRegionLayout {
        blocks,
        continuation,
    })
}

fn unstructured_exit_pad_prefix_is_cleanup(
    plan: &StructurePlan,
    proto: &LoweredProto,
    cfg: &Cfg,
    block: BlockRef,
) -> bool {
    let range = cfg.blocks[block.index()].instrs;
    let end = range.last().map_or(range.end(), |last| {
        if proto.instrs[last.index()].is_control_terminator() {
            range.end() - 1
        } else {
            range.end()
        }
    });
    (range.start.index()..end).all(|index| {
        let disposition = plan.cleanup_dispositions[index];
        match proto.instrs[index] {
            LowInstr::Close(_) => matches!(
                disposition,
                Some(
                    CleanupDisposition::LexicalScope(_)
                        | CleanupDisposition::Unreachable
                        | CleanupDisposition::ExplicitTbcBoundary
                )
            ),
            LowInstr::Tbc(_) => matches!(
                disposition,
                Some(CleanupDisposition::LexicalScope(_) | CleanupDisposition::Unreachable)
            ),
            _ => false,
        }
    })
}

pub(super) fn install_phi_incoming_dispositions(
    plan: &mut StructurePlan,
    dispositions: Vec<Vec<PhiIncomingDisposition>>,
    edge_copies: Vec<Vec<super::PhiEdgeCopy>>,
) {
    assert_eq!(edge_copies.len(), plan.edge_owners.len());
    plan.phi_incoming_dispositions = dispositions;
    plan.phi_edge_copies = edge_copies;
}

pub(super) fn install_generic_phi_materializations(
    plan: &mut StructurePlan,
    block_count: usize,
    phi_count: usize,
    materializations: Vec<super::GenericPhiMaterialization>,
) {
    let mut by_phi = vec![None; phi_count];
    for materialization in materializations {
        let slot = by_phi
            .get_mut(materialization.phi_id.index())
            .expect("generic phi materialization id must exist");
        assert!(slot.is_none(), "generic phi must have one materialization");
        *slot = Some(materialization);
    }
    let mut by_block = vec![Vec::new(); block_count];
    for materialization in by_phi.iter().copied().flatten() {
        by_block[materialization.block.index()].push(materialization);
    }
    plan.generic_phi_materializations = by_phi;
    plan.generic_phi_materializations_by_block = by_block;
}

fn validate_plan(
    cfg: &Cfg,
    goto_requirements: &[GotoRequirement],
    unstructured_region_by_block: &[Option<RegionId>],
    block_owners: &[BlockOwner],
    edge_owners: &[EdgeOwner],
    cleanup_dispositions: &[Option<CleanupDisposition>],
) {
    assert_eq!(block_owners.len(), cfg.blocks.len());
    assert_eq!(edge_owners.len(), cfg.edges.len());
    assert_eq!(unstructured_region_by_block.len(), cfg.blocks.len());
    assert_eq!(cleanup_dispositions.len(), cfg.instr_to_block.len());
    assert!(matches!(
        block_owners[cfg.exit_block.index()],
        BlockOwner::Exit
    ));

    for block in cfg
        .reachable_blocks
        .iter()
        .copied()
        .filter(|block| *block != cfg.exit_block)
    {
        assert!(
            !matches!(
                block_owners[block.index()],
                BlockOwner::Unreachable | BlockOwner::Exit
            ),
            "reachable block {block} must have a non-exit owner"
        );
    }
    for block in cfg
        .block_order
        .iter()
        .copied()
        .filter(|block| !cfg.reachable_blocks.contains(block))
    {
        assert_eq!(
            block_owners[block.index()],
            BlockOwner::Unreachable,
            "unreachable block {block} must retain unreachable owner"
        );
    }
    for (index, owner) in block_owners.iter().copied().enumerate() {
        if let BlockOwner::Unstructured(region) = owner {
            assert_eq!(
                unstructured_region_by_block[index],
                Some(region),
                "direct unstructured owner must match region membership"
            );
        }
    }
    for (index, requirement) in goto_requirements.iter().enumerate() {
        assert_eq!(
            edge_owners[requirement.edge.index()],
            EdgeOwner::Goto(GotoRequirementId(index)),
            "goto requirement must own its exact CFG edge"
        );
    }
}
