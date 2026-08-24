use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

use super::{
    ControlFlowFeature, EdgeActionPlacement, EdgePlan, EdgeTransfer, FinalPlanInput,
    ForwardRouteId, ForwardRouteKind, ForwardRoutePlan, LabelPlacement, LabelPlan, LabelPlanId,
    LoopNormalTailPlan, PlanRequirement, PlanRequirementId, PlanRequirements, RegionId,
    RegionNavigation, RegionPlan, StructureError, UnstructuredLayoutItem,
};
use crate::decompile::ControlFlowCaps;
use crate::structure::{
    BlockRef, BranchCandidate, BranchKind, BranchRegionFact, Cfg, DataflowFacts, EdgeKind, EdgeRef,
    GraphFacts, ShortCircuitExit, SsaValue, StructurePlan,
};
use crate::transformer::{BranchSubject, InstrRef, LowInstr, LoweredProto};

use super::super::common::{BranchRegionDomain, BranchRegionSpan};
use super::super::helpers::{control_prefix_is_movable, shared_pure_terminal_kind};
use super::super::loops::branch_conditions_share_subject;

mod branch_payload;
mod condition_routes;
mod container_insert;
mod container_topology;
mod edge_semantics;
mod forward_routes;
mod layout;
mod loop_canonicalize;
mod loop_exits;
mod loop_partition;
mod loop_payload;
mod loop_query;
mod loop_rewrite;
mod payload_select;
mod region_build;
mod unknown_loop;
mod value_decision;

use branch_payload::*;
use condition_routes::*;
use container_insert::*;
use container_topology::*;
use forward_routes::*;
pub(super) use layout::{LayoutEdgeFact, layout_edge_facts};
use layout::{build_requirements, freeze_labels};
use loop_canonicalize::*;
use loop_exits::*;
use loop_partition::*;
use loop_payload::*;
use loop_query::*;
use loop_rewrite::*;
use payload_select::*;
use region_build::*;
use unknown_loop::*;
use value_decision::*;

#[derive(Debug, Clone, Copy)]
enum ContainerKind {
    SinglePass(super::BranchPlanId),
    Branch(super::BranchPlanId),
    ValueDecision(super::ValueDecisionPlanId),
    Loop(super::LoopPlanId),
    Island(usize),
    Residual(BlockRef),
}

struct ContainerSpec {
    kind: ContainerKind,
    blocks: BTreeSet<BlockRef>,
    ranges: Vec<std::ops::Range<usize>>,
    block_count: usize,
    representative: BlockRef,
    first_rank: usize,
    parent: Option<usize>,
}

struct PendingContainer {
    kind: ContainerKind,
    blocks: BTreeSet<BlockRef>,
    ranges: Vec<std::ops::Range<usize>>,
    block_count: usize,
    representative: BlockRef,
}

impl PendingContainer {
    fn exact(
        kind: ContainerKind,
        blocks: BTreeSet<BlockRef>,
        graph_facts: &GraphFacts,
    ) -> Result<Self, StructureError> {
        let ranges = preorder_ranges_for_blocks(graph_facts, &blocks)?;
        Self::from_parts(kind, blocks, ranges, graph_facts)
    }

    fn intervals(
        kind: ContainerKind,
        ranges: Vec<std::ops::Range<usize>>,
        graph_facts: &GraphFacts,
    ) -> Result<Self, StructureError> {
        Self::from_parts(
            kind,
            BTreeSet::new(),
            merge_preorder_ranges(ranges),
            graph_facts,
        )
    }

    fn from_parts(
        kind: ContainerKind,
        blocks: BTreeSet<BlockRef>,
        ranges: Vec<std::ops::Range<usize>>,
        graph_facts: &GraphFacts,
    ) -> Result<Self, StructureError> {
        let block_count = ranges.iter().try_fold(0usize, |count, range| {
            count
                .checked_add(range.len())
                .ok_or_else(|| StructureError::invalid("container block count overflowed"))
        })?;
        let first = ranges
            .first()
            .and_then(|range| graph_facts.dominator_tree.order.get(range.start))
            .copied()
            .ok_or_else(|| StructureError::invalid("empty container reached pending arena"))?;
        Ok(Self {
            kind,
            blocks,
            ranges,
            block_count,
            representative: first,
        })
    }

    fn materialize_blocks(
        &self,
        graph_facts: &GraphFacts,
    ) -> Result<BTreeSet<BlockRef>, StructureError> {
        materialize_preorder_ranges(graph_facts, &self.ranges)
    }

    fn into_spec(self) -> ContainerSpec {
        ContainerSpec {
            kind: self.kind,
            blocks: self.blocks,
            ranges: self.ranges,
            block_count: self.block_count,
            representative: self.representative,
            first_rank: usize::MAX,
            parent: None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RangeOwnerState {
    Uniform(Option<usize>),
    Mixed,
}

struct RangeOwnerTree {
    len: usize,
    states: Vec<RangeOwnerState>,
}

impl RangeOwnerTree {
    fn new(len: usize) -> Self {
        Self {
            len,
            states: vec![RangeOwnerState::Uniform(None); len.saturating_mul(4).max(1)],
        }
    }

    fn uniform_owner(
        &self,
        ranges: &[std::ops::Range<usize>],
    ) -> Result<RangeOwnerState, StructureError> {
        let mut owner = None;
        let mut initialized = false;
        for range in ranges {
            if range.is_empty() {
                continue;
            }
            if range.end > self.len {
                return Err(StructureError::invalid(
                    "container range exceeds the owner index",
                ));
            }
            let state = self.query(1, 0, self.len, range.start, range.end)?;
            let RangeOwnerState::Uniform(current) = state else {
                return Ok(RangeOwnerState::Mixed);
            };
            if initialized && owner != current {
                return Ok(RangeOwnerState::Mixed);
            }
            owner = current;
            initialized = true;
        }
        initialized
            .then_some(RangeOwnerState::Uniform(owner))
            .ok_or_else(|| StructureError::invalid("empty container reached range owner index"))
    }

    fn assign(
        &mut self,
        ranges: &[std::ops::Range<usize>],
        owner: usize,
    ) -> Result<(), StructureError> {
        for range in ranges {
            if range.is_empty() {
                continue;
            }
            if range.end > self.len {
                return Err(StructureError::invalid(
                    "container range exceeds the owner index",
                ));
            }
            self.update(1, 0, self.len, range.start, range.end, owner)?;
        }
        Ok(())
    }

    fn materialize(&self) -> Result<Vec<Option<usize>>, StructureError> {
        let mut owners = vec![None; self.len];
        self.fill(1, 0, self.len, &mut owners)?;
        Ok(owners)
    }

    fn query(
        &self,
        node: usize,
        start: usize,
        end: usize,
        query_start: usize,
        query_end: usize,
    ) -> Result<RangeOwnerState, StructureError> {
        if query_end <= start || end <= query_start {
            return Err(StructureError::invalid(
                "range owner query reached a disjoint node",
            ));
        }
        let state = *self
            .states
            .get(node)
            .ok_or_else(|| StructureError::invalid("range owner query overflowed its tree"))?;
        if query_start <= start && end <= query_end {
            return Ok(state);
        }
        if let RangeOwnerState::Uniform(owner) = state {
            return Ok(RangeOwnerState::Uniform(owner));
        }
        let middle = start + (end - start) / 2;
        let left = (query_start < middle)
            .then(|| self.query(node * 2, start, middle, query_start, query_end))
            .transpose()?;
        let right = (middle < query_end)
            .then(|| self.query(node * 2 + 1, middle, end, query_start, query_end))
            .transpose()?;
        match (left, right) {
            (Some(left), Some(right)) if left == right => Ok(left),
            (Some(_), Some(_)) => Ok(RangeOwnerState::Mixed),
            (Some(state), None) | (None, Some(state)) => Ok(state),
            (None, None) => Err(StructureError::invalid(
                "range owner query selected no child",
            )),
        }
    }

    fn update(
        &mut self,
        node: usize,
        start: usize,
        end: usize,
        query_start: usize,
        query_end: usize,
        owner: usize,
    ) -> Result<(), StructureError> {
        if query_start <= start && end <= query_end {
            let slot = self
                .states
                .get_mut(node)
                .ok_or_else(|| StructureError::invalid("range owner update overflowed its tree"))?;
            *slot = RangeOwnerState::Uniform(Some(owner));
            return Ok(());
        }
        let middle = start + (end - start) / 2;
        let state = *self
            .states
            .get(node)
            .ok_or_else(|| StructureError::invalid("range owner update overflowed its tree"))?;
        if let RangeOwnerState::Uniform(owner) = state {
            *self.states.get_mut(node * 2).ok_or_else(|| {
                StructureError::invalid("range owner left child overflowed its tree")
            })? = RangeOwnerState::Uniform(owner);
            *self.states.get_mut(node * 2 + 1).ok_or_else(|| {
                StructureError::invalid("range owner right child overflowed its tree")
            })? = RangeOwnerState::Uniform(owner);
        }
        if query_start < middle {
            self.update(node * 2, start, middle, query_start, query_end, owner)?;
        }
        if middle < query_end {
            self.update(node * 2 + 1, middle, end, query_start, query_end, owner)?;
        }
        let left = self.states[node * 2];
        let right = self.states[node * 2 + 1];
        self.states[node] = if left == right {
            left
        } else {
            RangeOwnerState::Mixed
        };
        Ok(())
    }

    fn fill(
        &self,
        node: usize,
        start: usize,
        end: usize,
        owners: &mut [Option<usize>],
    ) -> Result<(), StructureError> {
        match self
            .states
            .get(node)
            .copied()
            .ok_or_else(|| StructureError::invalid("range owner projection overflowed its tree"))?
        {
            RangeOwnerState::Uniform(owner) => {
                owners[start..end].fill(owner);
            }
            RangeOwnerState::Mixed => {
                let middle = start + (end - start) / 2;
                self.fill(node * 2, start, middle, owners)?;
                self.fill(node * 2 + 1, middle, end, owners)?;
            }
        }
        Ok(())
    }
}

fn preorder_ranges_for_blocks(
    graph_facts: &GraphFacts,
    blocks: &BTreeSet<BlockRef>,
) -> Result<Vec<std::ops::Range<usize>>, StructureError> {
    preorder_ranges_for_block_iter(graph_facts, blocks.iter().copied())
}

fn materialize_preorder_ranges(
    graph_facts: &GraphFacts,
    ranges: &[std::ops::Range<usize>],
) -> Result<BTreeSet<BlockRef>, StructureError> {
    let mut blocks = BTreeSet::new();
    for range in ranges {
        let slice = graph_facts
            .dominator_tree
            .order
            .get(range.clone())
            .ok_or_else(|| StructureError::invalid("container range exceeds dominator preorder"))?;
        blocks.extend(slice.iter().copied());
    }
    Ok(blocks)
}

fn preorder_ranges_intersect_prefix(
    ranges: &[std::ops::Range<usize>],
    prefix: &[usize],
) -> Result<bool, StructureError> {
    let len = prefix
        .len()
        .checked_sub(1)
        .ok_or_else(|| StructureError::invalid("missing preorder membership prefix"))?;
    for range in ranges {
        if range.start > range.end || range.end > len {
            return Err(StructureError::invalid(
                "container range exceeds preorder membership prefix",
            ));
        }
        let start = prefix[range.start];
        let end = prefix[range.end];
        if start < end {
            return Ok(true);
        }
    }
    Ok(false)
}

fn preorder_ranges_for_block_iter(
    graph_facts: &GraphFacts,
    blocks: impl IntoIterator<Item = BlockRef>,
) -> Result<Vec<std::ops::Range<usize>>, StructureError> {
    let mut positions = blocks
        .into_iter()
        .map(|block| {
            graph_facts
                .dominator_tree
                .preorder_index
                .get(block.index())
                .copied()
                .flatten()
                .ok_or_else(|| {
                    StructureError::invalid(format!(
                        "container references unreachable block {block}"
                    ))
                })
        })
        .collect::<Result<Vec<_>, _>>()?;
    positions.sort_unstable();
    positions.dedup();
    let mut ranges = Vec::<std::ops::Range<usize>>::new();
    for position in positions {
        if let Some(last) = ranges.last_mut()
            && last.end == position
        {
            last.end += 1;
        } else {
            ranges.push(position..position + 1);
        }
    }
    Ok(ranges)
}

fn merge_preorder_ranges(mut ranges: Vec<std::ops::Range<usize>>) -> Vec<std::ops::Range<usize>> {
    ranges.retain(|range| !range.is_empty());
    ranges.sort_unstable_by_key(|range| (range.start, range.end));
    let mut merged = Vec::<std::ops::Range<usize>>::with_capacity(ranges.len());
    for range in ranges {
        if let Some(last) = merged.last_mut()
            && range.start <= last.end
        {
            last.end = last.end.max(range.end);
        } else {
            merged.push(range);
        }
    }
    merged
}

fn exclude_preorder_position(
    ranges: Vec<std::ops::Range<usize>>,
    excluded: Option<usize>,
) -> Vec<std::ops::Range<usize>> {
    let Some(excluded) = excluded else {
        return ranges;
    };
    ranges
        .into_iter()
        .flat_map(|range| {
            if !range.contains(&excluded) {
                return [Some(range), None];
            }
            [
                (range.start < excluded).then_some(range.start..excluded),
                (excluded + 1 < range.end).then_some(excluded + 1..range.end),
            ]
        })
        .flatten()
        .collect()
}

fn intersect_preorder_ranges(
    left: &[std::ops::Range<usize>],
    right: &[std::ops::Range<usize>],
) -> Vec<std::ops::Range<usize>> {
    let mut result = Vec::new();
    let mut left_index = 0;
    let mut right_index = 0;
    while left_index < left.len() && right_index < right.len() {
        let start = left[left_index].start.max(right[right_index].start);
        let end = left[left_index].end.min(right[right_index].end);
        if start < end {
            result.push(start..end);
        }
        if left[left_index].end <= right[right_index].end {
            left_index += 1;
        } else {
            right_index += 1;
        }
    }
    result
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ResidualSeedId(usize);

impl ResidualSeedId {
    const fn index(self) -> usize {
        self.0
    }
}

struct ResidualSeed {
    id: ResidualSeedId,
    entry: BlockRef,
    blocks: BTreeSet<BlockRef>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AggregateSeedDisposition {
    Residual(usize),
    Island(usize),
}

struct AggregateSeedDispositions {
    residuals: Vec<AggregateSeedDisposition>,
    islands: Vec<Option<usize>>,
}

struct ResidualComponent {
    blocks: BTreeSet<BlockRef>,
    seeds: Vec<ResidualSeedId>,
}

struct DisjointSet {
    parent: Vec<usize>,
    size: Vec<usize>,
}

struct DenseIntersectionWorkspace {
    epochs: Vec<u32>,
    counts: Vec<usize>,
    touched: Vec<usize>,
    epoch: u32,
}

impl DenseIntersectionWorkspace {
    fn new(component_count: usize) -> Self {
        Self {
            epochs: vec![0; component_count],
            counts: vec![0; component_count],
            touched: Vec::new(),
            epoch: 0,
        }
    }

    fn populate(&mut self, blocks: &BTreeSet<BlockRef>, component_by_block: &[Option<usize>]) {
        self.touched.clear();
        self.epoch = self.epoch.wrapping_add(1);
        if self.epoch == 0 {
            self.epochs.fill(0);
            self.epoch = 1;
        }
        for block in blocks {
            let Some(component) = component_by_block[block.index()] else {
                continue;
            };
            if self.epochs[component] != self.epoch {
                self.epochs[component] = self.epoch;
                self.counts[component] = 0;
                self.touched.push(component);
            }
            self.counts[component] += 1;
        }
    }
}

impl DisjointSet {
    fn new(len: usize) -> Self {
        Self {
            parent: (0..len).collect(),
            size: vec![1; len],
        }
    }

    fn find(&mut self, mut item: usize) -> usize {
        let mut root = item;
        while self.parent[root] != root {
            root = self.parent[root];
        }
        while self.parent[item] != item {
            let parent = self.parent[item];
            self.parent[item] = root;
            item = parent;
        }
        root
    }

    fn union(&mut self, left: usize, right: usize) -> usize {
        let mut left = self.find(left);
        let mut right = self.find(right);
        if left == right {
            return left;
        }
        if self.size[left] < self.size[right] || self.size[left] == self.size[right] && left > right
        {
            std::mem::swap(&mut left, &mut right);
        }
        self.parent[right] = left;
        self.size[left] += self.size[right];
        left
    }
}

#[derive(Debug, Clone)]
struct LoopPartitions {
    preheader: Option<BlockRef>,
    control: BTreeSet<BlockRef>,
    body: BTreeSet<BlockRef>,
    owned: BTreeSet<BlockRef>,
    continuation: Option<BlockRef>,
    continues: BTreeSet<EdgeRef>,
    break_routes: BTreeMap<EdgeRef, Vec<EdgeRef>>,
    normal_tail: Option<NormalTailPartition>,
}

struct LoopPartitionContext {
    forwarding_barriers: BTreeSet<BlockRef>,
    label_targets: BTreeSet<BlockRef>,
    branch_merge_by_header: Vec<Option<BlockRef>>,
    reachable_by_block: Vec<bool>,
    unstructured_by_block: Vec<bool>,
    residual_incidents_by_block: Vec<Vec<EdgeRef>>,
}

struct LoopPartitionInputs<'a> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    graph_facts: &'a GraphFacts,
    caps: ControlFlowCaps,
    input: &'a FinalPlanInput,
}

struct LoopPartitionWorkspaces {
    exit_pad: LoopExitPadWorkspace,
    while_arm: WhileLexicalArmWorkspace,
}

const WHILE_ARM_OWNED: u8 = 1 << 0;
const WHILE_ARM_EXCLUDED: u8 = 1 << 1;
const WHILE_ARM_QUEUED: u8 = 1 << 2;

struct WhileLexicalArmWorkspace {
    block_flags: Vec<u8>,
    attempted_edges: Vec<bool>,
    visited: Vec<bool>,
    touched_blocks: Vec<BlockRef>,
    touched_edges: Vec<EdgeRef>,
    touched_visits: Vec<BlockRef>,
    pending: VecDeque<BlockRef>,
    arm_pending: Vec<BlockRef>,
    arm_blocks: Vec<BlockRef>,
}

impl WhileLexicalArmWorkspace {
    fn new(block_count: usize, edge_count: usize) -> Self {
        Self {
            block_flags: vec![0; block_count],
            attempted_edges: vec![false; edge_count],
            visited: vec![false; block_count],
            touched_blocks: Vec::new(),
            touched_edges: Vec::new(),
            touched_visits: Vec::new(),
            pending: VecDeque::new(),
            arm_pending: Vec::new(),
            arm_blocks: Vec::new(),
        }
    }

    fn begin_loop(&mut self) {
        for block in self.touched_blocks.drain(..) {
            self.block_flags[block.index()] = 0;
        }
        for edge in self.touched_edges.drain(..) {
            self.attempted_edges[edge.index()] = false;
        }
        self.pending.clear();
        self.begin_arm();
    }

    fn begin_arm(&mut self) {
        for block in self.touched_visits.drain(..) {
            self.visited[block.index()] = false;
        }
        self.arm_pending.clear();
        self.arm_blocks.clear();
    }

    fn contains(&self, block: BlockRef, flag: u8) -> Result<bool, StructureError> {
        self.block_flags
            .get(block.index())
            .map(|flags| flags & flag != 0)
            .ok_or_else(|| {
                StructureError::invalid(
                    "while lexical arm references a block outside the CFG arena",
                )
            })
    }

    fn insert(&mut self, block: BlockRef, flag: u8) -> Result<bool, StructureError> {
        let flags = self.block_flags.get_mut(block.index()).ok_or_else(|| {
            StructureError::invalid("while lexical arm references a block outside the CFG arena")
        })?;
        if *flags == 0 {
            self.touched_blocks.push(block);
        }
        let inserted = *flags & flag == 0;
        *flags |= flag;
        Ok(inserted)
    }

    fn remove(&mut self, block: BlockRef, flag: u8) -> Result<(), StructureError> {
        let flags = self.block_flags.get_mut(block.index()).ok_or_else(|| {
            StructureError::invalid("while lexical arm references a block outside the CFG arena")
        })?;
        *flags &= !flag;
        Ok(())
    }

    fn mark_attempted(&mut self, edge: EdgeRef) -> Result<bool, StructureError> {
        let attempted = self.attempted_edges.get_mut(edge.index()).ok_or_else(|| {
            StructureError::invalid("while lexical arm references an edge outside the CFG arena")
        })?;
        if *attempted {
            return Ok(false);
        }
        *attempted = true;
        self.touched_edges.push(edge);
        Ok(true)
    }

    fn visit(&mut self, block: BlockRef) -> Result<bool, StructureError> {
        let visited = self.visited.get_mut(block.index()).ok_or_else(|| {
            StructureError::invalid("while lexical arm references a block outside the CFG arena")
        })?;
        if *visited {
            return Ok(false);
        }
        *visited = true;
        self.touched_visits.push(block);
        Ok(true)
    }

    fn is_visited(&self, block: BlockRef) -> Result<bool, StructureError> {
        self.visited.get(block.index()).copied().ok_or_else(|| {
            StructureError::invalid("while lexical arm references a block outside the CFG arena")
        })
    }
}

#[derive(Debug, Clone)]
struct NormalTailPartition {
    blocks: BTreeSet<BlockRef>,
    contract: LoopNormalTailPlan,
}

#[derive(Debug, Clone, Copy)]
enum ContainerSlots {
    SinglePass {
        region: RegionId,
    },
    Branch {
        region: RegionId,
        condition: RegionId,
        then_arm: RegionId,
        else_arm: Option<RegionId>,
    },
    Loop {
        region: RegionId,
        preheader: Option<RegionId>,
        control: RegionId,
        body: RegionId,
        normal_tail: Option<RegionId>,
    },
    ValueDecision {
        region: RegionId,
    },
    Island {
        region: RegionId,
    },
}

impl ContainerSlots {
    const fn region(self) -> RegionId {
        match self {
            Self::SinglePass { region }
            | Self::Branch { region, .. }
            | Self::ValueDecision { region }
            | Self::Loop { region, .. }
            | Self::Island { region } => region,
        }
    }
}

struct RegionArena {
    regions: Vec<RegionPlan>,
    region_by_block: Vec<Option<RegionId>>,
    navigation: RegionNavigation,
    loop_region_by_plan: Vec<RegionId>,
    value_decision_region_by_plan: Vec<RegionId>,
    single_passes: Vec<super::SinglePassPlan>,
    single_pass_by_region: Vec<Option<super::SinglePassPlanId>>,
    specs: Vec<ContainerSpec>,
    slots: Vec<ContainerSlots>,
}

pub(super) fn build(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    caps: ControlFlowCaps,
    mut input: FinalPlanInput,
) -> Result<StructurePlan, StructureError> {
    let block_terminators = super::terminator::freeze(proto, cfg)?;
    let (loops, loop_residuals) = canonicalize_loops(cfg, input.loops);
    input.loops = loops;
    input.unstructured.extend(loop_residuals);
    align_loop_condition_references(cfg, &mut input)?;
    normalize_repeat_condition_routes(proto, cfg, &mut input)?;
    legalize_conditional_continues(proto, cfg, graph_facts, caps, &mut input)?;
    let mut loop_partitions = build_loop_partitions(proto, cfg, graph_facts, caps, &input)?;
    if normalize_effectful_unknown_loop_conditions(cfg, graph_facts, &mut input, &loop_partitions)?
    {
        loop_partitions = build_loop_partitions(proto, cfg, graph_facts, caps, &input)?;
    }
    let mut arena = build_regions(cfg, graph_facts, &input, &loop_partitions)?;
    prune_non_iteration_branch_tail_continues(
        proto,
        cfg,
        caps,
        &arena,
        &input,
        &mut loop_partitions,
    )?;
    let root = RegionId(0);

    let mut residual_reason_by_edge = vec![None; cfg.edges.len()];
    for residual in &input.residual_transfers {
        let slot = residual_reason_by_edge
            .get_mut(residual.edge.index())
            .ok_or_else(|| {
                StructureError::invalid(format!(
                    "residual transfer references missing edge {}",
                    residual.edge
                ))
            })?;
        if slot.replace(residual.reason).is_some() {
            return Err(StructureError::invalid(format!(
                "edge {} has multiple residual transfer evidence",
                residual.edge
            )));
        }
    }

    let mut semantics = EdgeSemantics::new(proto, cfg, dataflow, &arena, &input, &loop_partitions)?;
    let mut edge_plans = cfg
        .edges
        .iter()
        .enumerate()
        .map(|(index, _edge)| {
            let edge_ref = EdgeRef(index);
            let relation = arena.navigation.edge_relation(edge_ref).unwrap_or_default();
            let (owner, transfer) = semantics.classify(
                cfg,
                edge_ref,
                residual_reason_by_edge[index],
                caps,
                relation.lca.unwrap_or(root),
            );
            let forward_route = semantics
                .forward_routes
                .binding_for_transfer(edge_ref, transfer);
            let action_placement =
                freeze_edge_action_placement(proto, cfg, &arena, &input, edge_ref, transfer);
            EdgePlan {
                edge: edge_ref,
                owner,
                transfer,
                action_placement,
                forward_route,
                phi_copies: Vec::new(),
                iteration: Vec::new(),
            }
        })
        .collect::<Vec<_>>();
    let tbc_flow = crate::structure::scope::analyze_tbc_flow(proto, cfg);
    let (labels, label_by_block) = freeze_labels(cfg, &arena, &mut edge_plans, &tbc_flow)?;

    let requirements = build_requirements(cfg, caps, &arena, &edge_plans)?;

    let selected = compact_selected_payloads(
        &mut arena,
        PayloadSelectionContext {
            proto,
            cfg,
            dataflow,
            input: &input,
            partitions: &loop_partitions,
            propagated_break_by_region: &semantics.loops.propagated_break_by_region,
            edge_plans: &edge_plans,
            tbc_flow: &tbc_flow,
        },
    )?;
    semantics
        .forward_routes
        .remap_conditions(&selected.condition_map)?;
    let forward_routes = semantics.forward_routes.freeze(&mut edge_plans)?;
    let LoopExitTailIndex {
        by_block: loop_exit_tail_by_block,
        by_edge: loop_exit_tail_by_edge,
        by_cleanup_instr: loop_exit_tail_by_cleanup_instr,
    } = index_loop_exit_tails(cfg, &selected.loops)?;
    let condition_value_by_phi =
        index_condition_values(dataflow.phi_candidates.len(), &selected.conditions)?;
    let absorbed_condition_by_block =
        index_absorbed_condition_blocks(cfg.blocks.len(), &selected.conditions)?;
    let value_decision_by_phi =
        index_value_decisions(dataflow.phi_candidates.len(), &selected.value_decisions)?;
    let region_count = arena.regions.len();
    Ok(StructurePlan {
        root,
        regions: arena.regions,
        region_by_block: arena.region_by_block,
        navigation: arena.navigation,
        block_terminators,
        block_emissions: vec![super::BlockEmissionPlan::Emit; cfg.blocks.len()],
        edge_plans,
        forward_routes: forward_routes.routes,
        forward_next: forward_routes.next,
        forward_preorder: forward_routes.preorder,
        forward_subtree_end: forward_routes.subtree_end,
        forward_depth: forward_routes.depth,
        forward_owner_by_edge: forward_routes.owner_by_edge,
        forward_kind_by_edge: forward_routes.kind_by_edge,
        forward_action_head: vec![None; cfg.edges.len()],
        requirements,
        labels,
        label_by_block,
        branches: selected.branches,
        single_passes: arena.single_passes,
        single_pass_by_region: arena.single_pass_by_region,
        loops: selected.loops,
        loop_region_by_plan: selected.loop_regions,
        loop_exit_tail_by_block,
        loop_exit_tail_by_edge,
        loop_exit_tail_by_cleanup_instr,
        conditions: selected.conditions,
        condition_value_by_phi,
        absorbed_condition_by_block,
        value_decisions: selected.value_decisions,
        value_decision_region_by_plan: selected.value_decision_regions,
        value_decision_by_phi,
        scopes: input.scopes,
        tbc_scopes: Vec::new(),
        phis: Vec::new(),
        phis_by_block: vec![Vec::new(); cfg.blocks.len()],
        phis_by_region: vec![Vec::new(); region_count],
        cleanup_dispositions: vec![None; cfg.instr_to_block.len()],
    })
}

struct EdgeSemantics {
    single_pass_breaks: Vec<Option<RegionId>>,
    backedges: Vec<Option<RegionId>>,
    breaks: Vec<Option<RegionId>>,
    continues: Vec<Option<RegionId>>,
    syntax_arms: Vec<Option<(RegionId, super::BranchArm)>>,
    forced_gotos: Vec<Option<crate::structure::GotoReason>>,
    branch_by_header: Vec<Option<RegionId>>,
    loops: LoopQueryIndex,
    forward_routes: ForwardRouteBuilder,
    early_continues: Vec<bool>,
    internal_transitions: Vec<Option<RegionId>>,
    preheader_edges: Vec<bool>,
    for_syntax_edges: Vec<bool>,
    normal_tail_edges: Vec<bool>,
    natural_edges: Vec<bool>,
    crosses_island_layout: Vec<bool>,
    value_decision_edges: Vec<Option<RegionId>>,
}
