use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

use super::{
    ControlFlowFeature, EdgeActionPlacement, EdgePlan, EdgeTransfer, FinalPlanInput,
    ForwardRouteId, ForwardRouteKind, ForwardRoutePlan, LabelPlacement, LabelPlan, LabelPlanId,
    PlanRequirement, PlanRequirementId, PlanRequirements, RegionId, RegionNavigation, RegionPlan,
    StructureError, UnstructuredLayoutItem,
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
    while_break: WhileBreakArmWorkspace,
}

const WHILE_BREAK_OWNED: u8 = 1 << 0;
const WHILE_BREAK_EXCLUDED: u8 = 1 << 1;
const WHILE_BREAK_QUEUED: u8 = 1 << 2;

struct WhileBreakArmWorkspace {
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

impl WhileBreakArmWorkspace {
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
                StructureError::invalid("while break-arm references a block outside the CFG arena")
            })
    }

    fn insert(&mut self, block: BlockRef, flag: u8) -> Result<bool, StructureError> {
        let flags = self.block_flags.get_mut(block.index()).ok_or_else(|| {
            StructureError::invalid("while break-arm references a block outside the CFG arena")
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
            StructureError::invalid("while break-arm references a block outside the CFG arena")
        })?;
        *flags &= !flag;
        Ok(())
    }

    fn mark_attempted(&mut self, edge: EdgeRef) -> Result<bool, StructureError> {
        let attempted = self.attempted_edges.get_mut(edge.index()).ok_or_else(|| {
            StructureError::invalid("while break-arm references an edge outside the CFG arena")
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
            StructureError::invalid("while break-arm references a block outside the CFG arena")
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
            StructureError::invalid("while break-arm references a block outside the CFG arena")
        })
    }
}

#[derive(Debug, Clone)]
struct NormalTailPartition {
    entry: BlockRef,
    blocks: BTreeSet<BlockRef>,
    continuation: BlockRef,
    early_exits: Vec<EdgeRef>,
    normal_exits: Vec<EdgeRef>,
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

fn prune_non_iteration_branch_tail_continues(
    proto: &LoweredProto,
    cfg: &Cfg,
    caps: ControlFlowCaps,
    arena: &RegionArena,
    input: &FinalPlanInput,
    partitions: &mut [LoopPartitions],
) -> Result<(), StructureError> {
    if input.loops.len() != partitions.len() {
        return Err(StructureError::invalid(
            "loop evidence and partition arenas have different lengths",
        ));
    }
    let branch_tail_edges = index_branch_tail_edges(cfg, arena)?;
    for (loop_, partition) in input.loops.iter().zip(partitions) {
        let candidate = &loop_.candidate;
        let body = &partition.body;
        partition.continues.retain(|edge| {
            !branch_tail_edges[edge.index()]
                || loop_.semantic_continue_edges.contains(edge)
                || caps.continue_stmt
                    && continue_edge_bypasses_body_parts(cfg, body, *edge)
                    && !(candidate.kind_hint == crate::structure::LoopKindHint::RepeatLike
                        && candidate.continue_target.is_some_and(|target| {
                            branch_conditions_share_subject(
                                proto,
                                cfg,
                                cfg.edges[edge.index()].from,
                                target,
                            )
                        }))
        });
    }
    Ok(())
}

fn index_branch_tail_edges(cfg: &Cfg, arena: &RegionArena) -> Result<Vec<bool>, StructureError> {
    #[derive(Clone, Copy)]
    struct ActiveBranch {
        end: usize,
        continuation: BlockRef,
        previous: Option<RegionId>,
    }

    let mut blocks_by_owner = vec![Vec::new(); arena.regions.len()];
    for (index, owner) in arena.region_by_block.iter().copied().enumerate() {
        if let Some(owner) = owner {
            blocks_by_owner[owner.index()].push(BlockRef(index));
        }
    }
    let mut active_by_continuation = vec![None; cfg.blocks.len()];
    let mut active = Vec::<ActiveBranch>::new();
    let mut tail_edges = vec![false; cfg.edges.len()];
    for (position, region) in arena.navigation.preorder.iter().copied().enumerate() {
        while active.last().is_some_and(|frame| frame.end <= position) {
            let frame = active
                .pop()
                .ok_or_else(|| StructureError::invalid("branch tail active stack underflowed"))?;
            active_by_continuation[frame.continuation.index()] = frame.previous;
        }
        if let Some(RegionPlan::Branch {
            continuation: Some(continuation),
            ..
        }) = arena.regions.get(region.index())
        {
            let slot = active_by_continuation
                .get_mut(continuation.index())
                .ok_or_else(|| {
                    StructureError::invalid("branch continuation is outside the block arena")
                })?;
            let previous = slot.replace(region);
            active.push(ActiveBranch {
                end: arena.navigation.subtree_end[region.index()],
                continuation: *continuation,
                previous,
            });
        }
        for block in &blocks_by_owner[region.index()] {
            for edge in &cfg.succs[block.index()] {
                let target = cfg.edges[edge.index()].to;
                if active_by_continuation[target.index()].is_some() {
                    tail_edges[edge.index()] = true;
                }
            }
        }
    }
    Ok(tail_edges)
}

/// 同一个物理 loop condition 可能同时留下 loop 与普通 branch 两份 owner 引用。
/// 在 region 冲突消解前把 branch 引用对齐到 loop 的 closed DAG identity，避免最终
/// plan 为同一对 CFG branch edge 冻结两个 condition owner。
fn align_loop_condition_references(
    cfg: &Cfg,
    input: &mut FinalPlanInput,
) -> Result<(), StructureError> {
    let mut by_header = vec![None; cfg.blocks.len()];
    for loop_ in &input.loops {
        let Some(condition_id) = loop_.condition else {
            continue;
        };
        let condition = input.conditions.get(condition_id.index()).ok_or_else(|| {
            StructureError::invalid("loop condition is outside the evidence arena")
        })?;
        let Some(slot) = by_header.get_mut(condition.candidate.header.index()) else {
            return Err(StructureError::invalid(
                "loop condition header is outside the CFG arena",
            ));
        };
        if slot.is_some_and(|existing| existing != condition_id) {
            return Err(StructureError::invalid(
                "one physical condition header belongs to multiple loop DAGs",
            ));
        }
        *slot = Some(condition_id);
    }
    for branch in &mut input.branches {
        let Some(condition_id) = by_header
            .get(branch.branch.header.index())
            .copied()
            .flatten()
        else {
            continue;
        };
        if branch.condition.is_some() {
            branch.condition = Some(condition_id);
        }
    }
    Ok(())
}

/// 把 repeat condition 到 header 之间的纯 jump pad 固化进 condition route。
///
/// Luau 会把 `until` 的回边拆成 `branch -> jump pad -> body header`。若 pad 留在
/// body residual 中，region builder 会把同一可规约 repeat 误判成多入口 island。
/// 这里只吸收无副作用、单后继且完全落在该 loop 词法域内的 jump 链。
fn normalize_repeat_condition_routes(
    proto: &LoweredProto,
    cfg: &Cfg,
    input: &mut FinalPlanInput,
) -> Result<(), StructureError> {
    let mut visit = BlockVisitWorkspace::new(cfg.blocks.len());
    let mut condition_owners = vec![0usize; input.conditions.len()];
    for loop_ in &input.loops {
        if let Some(condition) = loop_.condition {
            let Some(slot) = condition_owners.get_mut(condition.index()) else {
                return Err(StructureError::invalid(
                    "loop references a condition outside the evidence arena",
                ));
            };
            *slot = slot
                .checked_add(1)
                .ok_or_else(|| StructureError::invalid("condition owner count overflows"))?;
        }
    }
    for loop_ in &input.loops {
        if loop_.candidate.kind_hint != crate::structure::LoopKindHint::RepeatLike {
            continue;
        }
        let Some(condition_id) = loop_.condition else {
            continue;
        };
        if condition_owners.get(condition_id.index()).copied() != Some(1) {
            continue;
        }
        let condition = input
            .conditions
            .get_mut(condition_id.index())
            .ok_or_else(|| {
                StructureError::invalid("repeat loop condition disappeared during normalization")
            })?;
        let ShortCircuitExit::BranchExit { truthy, falsy } = condition.candidate.exit else {
            continue;
        };
        let mut allowed = loop_.candidate.blocks.clone();
        allowed.extend(loop_.candidate.body_scope_blocks.iter().copied());
        allowed.extend(loop_.candidate.control_blocks.iter().copied());
        let truthy_route = pure_jump_route_to(
            proto,
            cfg,
            truthy,
            loop_.candidate.header,
            &allowed,
            &mut visit,
        );
        let falsy_route = pure_jump_route_to(
            proto,
            cfg,
            falsy,
            loop_.candidate.header,
            &allowed,
            &mut visit,
        );
        let (truthy_backedge, old_target, connectors, route) = match (truthy_route, falsy_route) {
            (Some((connectors, route)), None) => (true, truthy, connectors, route),
            (None, Some((connectors, route))) => (false, falsy, connectors, route),
            (None, None) | (Some(_), Some(_)) => continue,
        };

        let mut extended = false;
        for arc in &mut condition.arcs {
            let targets_backedge = matches!(
                (&arc.target, truthy_backedge),
                (
                    crate::structure::common::ShortCircuitTarget::TruthyExit,
                    true
                ) | (
                    crate::structure::common::ShortCircuitTarget::FalsyExit,
                    false
                )
            );
            if !targets_backedge {
                continue;
            }
            let Some(last) = arc.edges.last().copied() else {
                return Err(StructureError::invalid(
                    "repeat condition contains an empty exit route",
                ));
            };
            if cfg.edges.get(last.index()).map(|edge| edge.to) != Some(old_target) {
                return Err(StructureError::invalid(
                    "repeat condition exit route changed before normalization",
                ));
            }
            arc.connector_blocks.extend(connectors.iter().copied());
            arc.edges.extend(route.iter().copied());
            extended = true;
        }
        if !extended {
            return Err(StructureError::invalid(
                "repeat condition has no semantic arc for its backedge exit",
            ));
        }
        condition.candidate.blocks.extend(connectors);
        condition.candidate.exit = if truthy_backedge {
            ShortCircuitExit::BranchExit {
                truthy: loop_.candidate.header,
                falsy,
            }
        } else {
            ShortCircuitExit::BranchExit {
                truthy,
                falsy: loop_.candidate.header,
            }
        };
    }
    Ok(())
}

fn pure_jump_route_to(
    proto: &LoweredProto,
    cfg: &Cfg,
    start: BlockRef,
    target: BlockRef,
    allowed: &BTreeSet<BlockRef>,
    visit: &mut BlockVisitWorkspace,
) -> Option<(Vec<BlockRef>, Vec<EdgeRef>)> {
    if start == target {
        return None;
    }
    let mut connectors = Vec::new();
    let mut route = Vec::new();
    visit.begin();
    let mut block = start;
    while block != target {
        if !visit.mark(block) || !allowed.contains(&block) {
            return None;
        }
        let range = cfg.blocks.get(block.index())?.instrs;
        let [edge] = cfg.succs.get(block.index())?.as_slice() else {
            return None;
        };
        if range.len != 1
            || !matches!(
                proto.instrs.get(range.start.index()),
                Some(LowInstr::Jump(_))
            )
            || cfg.edges.get(edge.index())?.kind != EdgeKind::Jump
        {
            return None;
        }
        connectors.push(block);
        route.push(*edge);
        block = cfg.edges[edge.index()].to;
    }
    Some((connectors, route))
}

struct BlockVisitWorkspace {
    seen_at: Vec<u32>,
    epoch: u32,
}

impl BlockVisitWorkspace {
    fn new(block_count: usize) -> Self {
        Self {
            seen_at: vec![0; block_count],
            epoch: 0,
        }
    }

    fn begin(&mut self) {
        self.epoch = self.epoch.wrapping_add(1);
        if self.epoch == 0 {
            self.seen_at.fill(0);
            self.epoch = 1;
        }
    }

    fn mark(&mut self, block: BlockRef) -> bool {
        let Some(seen_at) = self.seen_at.get_mut(block.index()) else {
            return false;
        };
        std::mem::replace(seen_at, self.epoch) != self.epoch
    }
}

fn repeat_condition_route_kind(
    cfg: &Cfg,
    input: &FinalPlanInput,
    condition_id: Option<super::ConditionPlanId>,
    route: &[EdgeRef],
) -> Result<Option<ForwardRouteKind>, StructureError> {
    let condition_id = condition_id.ok_or_else(|| {
        StructureError::invalid("repeat continue route has no frozen condition owner")
    })?;
    let condition = input.conditions.get(condition_id.index()).ok_or_else(|| {
        StructureError::invalid("repeat continue route references a missing condition")
    })?;
    let mut matching = condition.arcs.iter().filter(|arc| arc.edges == route);
    let Some(arc) = matching.next() else {
        return Ok(None);
    };
    if matching.next().is_some() {
        return Err(StructureError::invalid(
            "repeat continue route matches multiple condition arcs",
        ));
    }
    let first = route
        .first()
        .and_then(|edge| cfg.edges.get(edge.index()))
        .ok_or_else(|| StructureError::invalid("repeat continue route is empty or stale"))?;
    let polarity = match first.kind {
        EdgeKind::BranchTrue => super::ConditionArcPolarity::BranchTrue,
        EdgeKind::BranchFalse => super::ConditionArcPolarity::BranchFalse,
        _ => {
            return Err(StructureError::invalid(
                "repeat continue route does not start with a branch edge",
            ));
        }
    };
    Ok(Some(ForwardRouteKind::RepeatConditionArc(
        super::ConditionArcRef {
            condition: condition_id,
            node: super::ConditionNodeId(arc.source.index()),
            polarity,
        },
    )))
}

fn freeze_edge_action_placement(
    proto: &LoweredProto,
    cfg: &Cfg,
    arena: &RegionArena,
    input: &FinalPlanInput,
    edge_ref: EdgeRef,
    transfer: EdgeTransfer,
) -> EdgeActionPlacement {
    let EdgeTransfer::LoopBack(loop_region) = transfer else {
        return EdgeActionPlacement::BeforeTransfer;
    };
    let Some(edge) = cfg.edges.get(edge_ref.index()) else {
        return EdgeActionPlacement::BeforeTransfer;
    };
    if edge.kind != EdgeKind::Jump
        || cfg.succs.get(edge.from.index()).map(Vec::as_slice) != Some(&[edge_ref])
    {
        return EdgeActionPlacement::BeforeTransfer;
    }
    let Some(RegionPlan::Loop { plan: loop_id, .. }) = arena.regions.get(loop_region.index())
    else {
        return EdgeActionPlacement::BeforeTransfer;
    };
    let has_carried_action = input.loops.get(loop_id.index()).is_some_and(|loop_| {
        loop_
            .carried_values
            .iter()
            .any(|value| value.inside_arm.contains_pred(edge.from))
    });
    if !has_carried_action {
        return EdgeActionPlacement::BeforeTransfer;
    }

    let Some(block_range) = cfg.blocks.get(edge.from.index()).map(|block| block.instrs) else {
        return EdgeActionPlacement::BeforeTransfer;
    };
    let Some(terminator) = block_range.last() else {
        return EdgeActionPlacement::BeforeTransfer;
    };
    if !matches!(
        proto.instrs.get(terminator.index()),
        Some(LowInstr::Jump(_))
    ) {
        return EdgeActionPlacement::BeforeTransfer;
    }

    let cleanup_end = terminator.index();
    let mut cleanup_start = cleanup_end;
    while cleanup_start > block_range.start.index()
        && matches!(
            proto.instrs.get(cleanup_start - 1),
            Some(LowInstr::Close(_) | LowInstr::Tbc(_))
        )
    {
        cleanup_start -= 1;
    }
    if cleanup_start == cleanup_end || cleanup_start == block_range.start.index() {
        return EdgeActionPlacement::BeforeTransfer;
    }

    EdgeActionPlacement::BeforeTrailingCleanup {
        cleanup: crate::structure::InstrRange::new(
            InstrRef(cleanup_start),
            cleanup_end - cleanup_start,
        ),
    }
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

struct LoopQueryIndex {
    innermost_by_block: Vec<Option<RegionId>>,
    control_by_block: Vec<Option<RegionId>>,
    loop_parent: Vec<Option<RegionId>>,
    spec_by_region: Vec<Option<usize>>,
    continuation: Vec<Option<BlockRef>>,
    normal_tail_entry: Vec<Option<BlockRef>>,
    break_owner_by_edge: Vec<Option<RegionId>>,
    continue_owner_by_edge: Vec<Option<RegionId>>,
    leaves_innermost_loop: Vec<bool>,
    propagated_break_by_region: Vec<Option<RegionId>>,
    propagated_break_target_by_region: Vec<Option<RegionId>>,
}

impl LoopQueryIndex {
    fn build(
        cfg: &Cfg,
        arena: &RegionArena,
        input: &FinalPlanInput,
        partitions: &[LoopPartitions],
        layout_edges: &[LayoutEdgeFact],
    ) -> Result<Self, StructureError> {
        let region_count = arena.regions.len();
        let mut spec_by_region = vec![None; region_count];
        let mut continuation = vec![None; region_count];
        let mut continue_target = vec![None; region_count];
        let mut normal_tail_entry = vec![None; region_count];
        let mut control_marker = vec![None; region_count];
        for (spec_index, spec) in arena.specs.iter().enumerate() {
            let ContainerKind::Loop(id) = spec.kind else {
                continue;
            };
            let region = arena.slots[spec_index].region();
            let loop_ = input
                .loops
                .get(id.index())
                .ok_or_else(|| StructureError::invalid("loop query references missing evidence"))?;
            let partition = partitions.get(id.index()).ok_or_else(|| {
                StructureError::invalid("loop query references missing partition")
            })?;
            spec_by_region[region.index()] = Some(spec_index);
            continuation[region.index()] = partition.continuation;
            continue_target[region.index()] = loop_.candidate.continue_target;
            normal_tail_entry[region.index()] =
                partition.normal_tail.as_ref().map(|tail| tail.entry);
            let Some(RegionPlan::Loop {
                preheader, control, ..
            }) = arena.regions.get(region.index())
            else {
                return Err(StructureError::invalid("loop query region is not a loop"));
            };
            control_marker[control.index()] = Some(region);
            if let Some(preheader) = preheader {
                control_marker[preheader.index()] = Some(region);
            }
        }

        let mut nearest_by_region = vec![None; region_count];
        let mut control_by_region = vec![None; region_count];
        let mut loop_parent = vec![None; region_count];
        for region in &arena.navigation.preorder {
            let inherited_loop = arena.navigation.parent[region.index()]
                .and_then(|parent| nearest_by_region[parent.index()]);
            let inherited_control = arena.navigation.parent[region.index()]
                .and_then(|parent| control_by_region[parent.index()]);
            if spec_by_region[region.index()].is_some() {
                loop_parent[region.index()] = inherited_loop;
                nearest_by_region[region.index()] = Some(*region);
            } else {
                nearest_by_region[region.index()] = inherited_loop;
            }
            control_by_region[region.index()] =
                control_marker[region.index()].or(inherited_control);
        }

        let mut blocks_by_owner = vec![Vec::new(); region_count];
        let mut innermost_by_block = vec![None; cfg.blocks.len()];
        let mut control_by_block = vec![None; cfg.blocks.len()];
        for (index, owner) in arena.region_by_block.iter().copied().enumerate() {
            let Some(owner) = owner else { continue };
            let block = BlockRef(index);
            blocks_by_owner[owner.index()].push(block);
            innermost_by_block[index] = nearest_by_region[owner.index()];
            control_by_block[index] = control_by_region[owner.index()];
        }

        #[derive(Clone, Copy)]
        struct ActiveLoopTargets {
            end: usize,
            break_target: Option<(BlockRef, Option<RegionId>)>,
            continue_target: Option<(BlockRef, Option<RegionId>)>,
        }
        let mut active_break = vec![None; cfg.blocks.len()];
        let mut active_continue = vec![None; cfg.blocks.len()];
        let mut active = Vec::<ActiveLoopTargets>::new();
        let mut break_owner_by_edge = vec![None; cfg.edges.len()];
        let mut continue_owner_by_edge = vec![None; cfg.edges.len()];
        for (position, region) in arena.navigation.preorder.iter().copied().enumerate() {
            while active.last().is_some_and(|frame| frame.end <= position) {
                let frame = active.pop().ok_or_else(|| {
                    StructureError::invalid("loop query active stack underflowed")
                })?;
                if let Some((target, previous)) = frame.break_target {
                    active_break[target.index()] = previous;
                }
                if let Some((target, previous)) = frame.continue_target {
                    active_continue[target.index()] = previous;
                }
            }
            if spec_by_region[region.index()].is_some() {
                let break_target = continuation[region.index()].map(|target| {
                    let previous = active_break[target.index()];
                    active_break[target.index()] = previous.or(Some(region));
                    (target, previous)
                });
                let continue_target = continue_target[region.index()].map(|target| {
                    let previous = active_continue[target.index()];
                    active_continue[target.index()] = Some(region);
                    (target, previous)
                });
                active.push(ActiveLoopTargets {
                    end: arena.navigation.subtree_end[region.index()],
                    break_target,
                    continue_target,
                });
            }
            for block in &blocks_by_owner[region.index()] {
                for edge in &cfg.succs[block.index()] {
                    let target = cfg.edges[edge.index()].to;
                    break_owner_by_edge[edge.index()] = active_break[target.index()];
                    continue_owner_by_edge[edge.index()] = active_continue[target.index()];
                }
            }
        }

        let mut leaves_innermost_loop = vec![false; cfg.edges.len()];
        for (index, edge) in cfg.edges.iter().enumerate() {
            let Some(loop_region) = innermost_by_block[edge.from.index()] else {
                continue;
            };
            leaves_innermost_loop[index] = arena
                .region_by_block
                .get(edge.to.index())
                .copied()
                .flatten()
                .is_none_or(|target| !arena.navigation.contains(loop_region, target));
        }

        let mut propagated_break_by_region = vec![None; region_count];
        for (region_index, spec) in spec_by_region.iter().copied().enumerate() {
            let Some(spec) = spec else { continue };
            let region = RegionId(region_index);
            let ContainerKind::Loop(loop_id) = arena.specs[spec].kind else {
                continue;
            };
            let partition = &partitions[loop_id.index()];
            let mut target = None;
            let mut valid = true;
            for block in &partition.owned {
                for edge_ref in &cfg.succs[block.index()] {
                    let edge = cfg.edges[edge_ref.index()];
                    if partition.owned.contains(&edge.to)
                        || matches!(edge.kind, EdgeKind::Return | EdgeKind::TailCall)
                        || (!layout_edges
                            .get(edge_ref.index())
                            .is_some_and(|fact| fact.natural)
                            && shared_pure_terminal_kind(cfg, edge.to).is_some())
                    {
                        continue;
                    }
                    let Some(owner) = break_owner_by_edge[edge_ref.index()] else {
                        valid = false;
                        target = None;
                        break;
                    };
                    if owner == region
                        || target.replace(owner).is_some_and(|target| target != owner)
                    {
                        valid = false;
                        target = None;
                        break;
                    }
                }
                if !valid {
                    break;
                }
            }
            if valid && target.is_some() {
                propagated_break_by_region[region.index()] = target;
            }
        }
        // `propagates_break` 位于逐 edge 分类热路径。把“从当前最内 loop 到目标
        // loop 的每一层都声明相同 propagated break”在 loop preorder 中压缩一次，
        // 避免每条跨层 break 再按嵌套深度上爬。
        let mut propagated_break_target_by_region = vec![None; region_count];
        for region in arena.navigation.preorder.iter().copied() {
            let Some(target) = propagated_break_by_region[region.index()] else {
                continue;
            };
            let parent = loop_parent[region.index()];
            if parent == Some(target)
                || parent.is_some_and(|parent| {
                    propagated_break_target_by_region[parent.index()] == Some(target)
                })
            {
                propagated_break_target_by_region[region.index()] = Some(target);
            }
        }

        Ok(Self {
            innermost_by_block,
            control_by_block,
            loop_parent,
            spec_by_region,
            continuation,
            normal_tail_entry,
            break_owner_by_edge,
            continue_owner_by_edge,
            leaves_innermost_loop,
            propagated_break_by_region,
            propagated_break_target_by_region,
        })
    }

    fn innermost(&self, block: BlockRef) -> Option<RegionId> {
        self.innermost_by_block
            .get(block.index())
            .copied()
            .flatten()
    }

    fn innermost_spec(&self, block: BlockRef) -> Option<(usize, RegionId)> {
        let region = self.innermost(block)?;
        self.loop_parent.get(region.index())?;
        self.spec_by_region[region.index()].map(|spec| (spec, region))
    }

    fn propagates_break(&self, source: BlockRef, target: RegionId) -> bool {
        self.innermost(source).is_some_and(|region| {
            region == target
                || self
                    .propagated_break_target_by_region
                    .get(region.index())
                    .copied()
                    .flatten()
                    == Some(target)
        })
    }
}

struct ForwardRouteBuilder {
    routes: Vec<ForwardRoutePlan>,
    next: Vec<Option<EdgeRef>>,
    next_assigned: Vec<bool>,
    remaining_len: Vec<usize>,
    last_by_edge: Vec<Option<EdgeRef>>,
    route_by_first: Vec<Option<ForwardRouteId>>,
    owner_by_edge: Vec<Option<RegionId>>,
    kind_by_edge: Vec<Option<ForwardRouteKind>>,
    edges_by_owner: Vec<Vec<EdgeRef>>,
    binding_by_entry: Vec<Option<ForwardRouteId>>,
    visit_epoch: Vec<usize>,
    next_epoch: usize,
}

#[derive(Debug, Clone, Copy)]
struct FunctionalForwardPath {
    first: EdgeRef,
    last: EdgeRef,
    len: usize,
}

struct FunctionalForwardPathEdges<'a> {
    cfg: &'a Cfg,
    next: Option<EdgeRef>,
    remaining: usize,
}

impl<'a> FunctionalForwardPathEdges<'a> {
    fn new(cfg: &'a Cfg, path: FunctionalForwardPath) -> Self {
        Self {
            cfg,
            next: Some(path.first),
            remaining: path.len,
        }
    }
}

impl Iterator for FunctionalForwardPathEdges<'_> {
    type Item = EdgeRef;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        let edge = self.next?;
        self.remaining -= 1;
        self.next = if self.remaining == 0 {
            None
        } else {
            let target = self.cfg.edges[edge.index()].to;
            let [next] = self.cfg.succs[target.index()].as_slice() else {
                self.next = None;
                return Some(edge);
            };
            Some(*next)
        };
        Some(edge)
    }
}

impl ForwardRouteBuilder {
    fn new(edge_count: usize, region_count: usize) -> Self {
        Self {
            routes: Vec::new(),
            next: vec![None; edge_count],
            next_assigned: vec![false; edge_count],
            remaining_len: vec![0; edge_count],
            last_by_edge: vec![None; edge_count],
            route_by_first: vec![None; edge_count],
            owner_by_edge: vec![None; edge_count],
            kind_by_edge: vec![None; edge_count],
            edges_by_owner: vec![Vec::new(); region_count],
            binding_by_entry: vec![None; edge_count],
            visit_epoch: vec![0; edge_count],
            next_epoch: 0,
        }
    }

    fn binding(&self, entry: EdgeRef) -> Option<ForwardRouteId> {
        self.binding_by_entry.get(entry.index()).copied().flatten()
    }

    fn contains_edge(&self, edge: EdgeRef) -> bool {
        self.next_assigned
            .get(edge.index())
            .copied()
            .unwrap_or(false)
    }

    fn binding_for_transfer(
        &self,
        entry: EdgeRef,
        transfer: EdgeTransfer,
    ) -> Option<ForwardRouteId> {
        let route = self.binding(entry)?;
        let kind = self.routes.get(route.index())?.kind;
        matches!(
            (transfer, kind),
            (EdgeTransfer::Break(_), ForwardRouteKind::ExclusiveBreak)
                | (
                    EdgeTransfer::Continue(_),
                    ForwardRouteKind::ContinueToTarget
                )
                | (EdgeTransfer::Continue(_), ForwardRouteKind::ContinueLatch)
                | (
                    EdgeTransfer::Continue(_),
                    ForwardRouteKind::RepeatConditionArc(_)
                )
        )
        .then_some(route)
    }

    fn remap_conditions(
        &mut self,
        condition_map: &[Option<super::ConditionPlanId>],
    ) -> Result<(), StructureError> {
        let remap = |kind: ForwardRouteKind| -> Result<ForwardRouteKind, StructureError> {
            let ForwardRouteKind::RepeatConditionArc(mut arc) = kind else {
                return Ok(kind);
            };
            arc.condition = condition_map
                .get(arc.condition.index())
                .copied()
                .flatten()
                .ok_or_else(|| {
                    StructureError::invalid(
                        "repeat forward route condition was not selected into the final plan",
                    )
                })?;
            Ok(ForwardRouteKind::RepeatConditionArc(arc))
        };
        for route in &mut self.routes {
            route.kind = remap(route.kind)?;
        }
        for kind in self.kind_by_edge.iter_mut().flatten() {
            *kind = remap(*kind)?;
        }
        Ok(())
    }

    fn bind(&mut self, entry: EdgeRef, route: ForwardRouteId) -> Result<(), StructureError> {
        let slot = self
            .binding_by_entry
            .get_mut(entry.index())
            .ok_or_else(|| StructureError::invalid("forward route entry is outside the CFG"))?;
        if slot.replace(route).is_some_and(|old| old != route) {
            return Err(StructureError::invalid(format!(
                "{entry} is bound to conflicting forwarding routes"
            )));
        }
        Ok(())
    }

    fn install(
        &mut self,
        cfg: &Cfg,
        kind: ForwardRouteKind,
        loop_region: RegionId,
        edges: &[EdgeRef],
    ) -> Result<Option<ForwardRouteId>, StructureError> {
        let Some((&first, &last)) = edges.first().zip(edges.last()) else {
            return Ok(None);
        };
        self.install_iter(
            cfg,
            kind,
            loop_region,
            FunctionalForwardPath {
                first,
                last,
                len: edges.len(),
            },
            edges.iter().copied(),
        )
    }

    fn install_functional(
        &mut self,
        cfg: &Cfg,
        kind: ForwardRouteKind,
        loop_region: RegionId,
        path: FunctionalForwardPath,
    ) -> Result<Option<ForwardRouteId>, StructureError> {
        self.install_iter(
            cfg,
            kind,
            loop_region,
            path,
            FunctionalForwardPathEdges::new(cfg, path),
        )
    }

    fn install_functional_composed(
        &mut self,
        cfg: &Cfg,
        kind: ForwardRouteKind,
        loop_region: RegionId,
        prefix: FunctionalForwardPath,
        suffix: &[EdgeRef],
    ) -> Result<Option<ForwardRouteId>, StructureError> {
        let len = prefix
            .len
            .checked_add(suffix.len())
            .ok_or_else(|| StructureError::invalid("forward route length overflow"))?;
        let last = suffix.last().copied().unwrap_or(prefix.last);
        self.install_iter(
            cfg,
            kind,
            loop_region,
            FunctionalForwardPath {
                first: prefix.first,
                last,
                len,
            },
            FunctionalForwardPathEdges::new(cfg, prefix).chain(suffix.iter().copied()),
        )
    }

    fn install_iter<I>(
        &mut self,
        cfg: &Cfg,
        kind: ForwardRouteKind,
        loop_region: RegionId,
        path: FunctionalForwardPath,
        edges: I,
    ) -> Result<Option<ForwardRouteId>, StructureError>
    where
        I: Iterator<Item = EdgeRef>,
    {
        let FunctionalForwardPath { first, last, len } = path;
        let first_cfg = cfg.edges.get(first.index()).ok_or_else(|| {
            StructureError::invalid(format!("forward route references missing {first}"))
        })?;
        let last_cfg = cfg.edges.get(last.index()).ok_or_else(|| {
            StructureError::invalid(format!("forward route references missing {last}"))
        })?;
        let candidate = ForwardRoutePlan {
            kind,
            loop_region,
            first,
            last,
            start: first_cfg.from,
            target: last_cfg.to,
            len,
        };
        if let Some(existing) = self.route_by_first.get(first.index()).copied().flatten() {
            if self.routes.get(existing.index()) == Some(&candidate) {
                return Ok(Some(existing));
            }
            return Err(StructureError::invalid(format!(
                "{first} starts conflicting forwarding routes: existing={:?}, candidate={candidate:?}",
                self.routes[existing.index()],
            )));
        }
        self.next_epoch = self
            .next_epoch
            .checked_add(1)
            .ok_or_else(|| StructureError::invalid("forward route epoch overflow"))?;

        let mut edges = edges.peekable();
        let mut position = 0usize;
        let mut reused_suffix = false;
        while let Some(edge) = edges.next() {
            let cfg_edge = cfg.edges.get(edge.index()).ok_or_else(|| {
                StructureError::invalid(format!("forward route references missing {edge}"))
            })?;
            let expected_next = edges.peek().copied();
            if let Some(next) = expected_next {
                let next_cfg = cfg.edges.get(next.index()).ok_or_else(|| {
                    StructureError::invalid(format!("forward route references missing {next}"))
                })?;
                if cfg_edge.to != next_cfg.from {
                    return Err(StructureError::invalid(format!(
                        "forward route is not contiguous between {edge} and {next}"
                    )));
                }
            }
            let visit = self.visit_epoch.get_mut(edge.index()).ok_or_else(|| {
                StructureError::invalid(format!("forward route references missing {edge}"))
            })?;
            if std::mem::replace(visit, self.next_epoch) == self.next_epoch {
                return Err(StructureError::invalid(format!(
                    "forward route contains a cycle at {edge}"
                )));
            }
            let expected_remaining = len.checked_sub(position).ok_or_else(|| {
                StructureError::invalid("forward route contains more edges than its frozen length")
            })?;
            let next_slot = self.next.get_mut(edge.index()).ok_or_else(|| {
                StructureError::invalid(format!("forward route references missing {edge}"))
            })?;
            let assigned = self.next_assigned.get_mut(edge.index()).ok_or_else(|| {
                StructureError::invalid(format!("forward route references missing {edge}"))
            })?;
            if *assigned {
                if *next_slot != expected_next
                    || self.remaining_len[edge.index()] != expected_remaining
                    || self.last_by_edge[edge.index()] != Some(last)
                    || self.owner_by_edge[edge.index()] != Some(loop_region)
                    || self.kind_by_edge[edge.index()] != Some(kind)
                {
                    return Err(StructureError::invalid(format!(
                        "{edge} has a conflicting forwarding suffix"
                    )));
                }
                // `next` is functional. Matching the first shared edge, its next edge,
                // remaining length and terminal proves that the already frozen suffix
                // is the same route, so shared pads are never walked again.
                reused_suffix = true;
                break;
            }
            *next_slot = expected_next;
            *assigned = true;
            self.remaining_len[edge.index()] = expected_remaining;
            self.last_by_edge[edge.index()] = Some(last);
            let owner = self.owner_by_edge.get_mut(edge.index()).ok_or_else(|| {
                StructureError::invalid(format!("forward route references missing {edge}"))
            })?;
            if owner.is_some_and(|owner| owner != loop_region) {
                return Err(StructureError::invalid(format!(
                    "{edge} is shared by forwarding routes from different loops"
                )));
            }
            *owner = Some(loop_region);
            let edge_kind = self.kind_by_edge.get_mut(edge.index()).ok_or_else(|| {
                StructureError::invalid(format!("forward route references missing {edge}"))
            })?;
            if edge_kind.is_some_and(|edge_kind| edge_kind != kind) {
                return Err(StructureError::invalid(format!(
                    "{edge} is shared by forwarding routes with different semantics"
                )));
            }
            *edge_kind = Some(kind);
            self.edges_by_owner
                .get_mut(loop_region.index())
                .ok_or_else(|| {
                    StructureError::invalid("forward route owner is outside the region arena")
                })?
                .push(edge);
            position += 1;
        }
        if !reused_suffix && position != len {
            return Err(StructureError::invalid(
                "forward route ended before its frozen length",
            ));
        }
        let id = ForwardRouteId(self.routes.len());
        self.route_by_first[first.index()] = Some(id);
        self.routes.push(candidate);
        Ok(Some(id))
    }

    fn freeze(mut self, edge_plans: &mut [EdgePlan]) -> Result<ForwardRouteArena, StructureError> {
        let mut used = vec![false; self.routes.len()];
        for edge in edge_plans.iter() {
            if let Some(route) = edge.forward_route {
                let slot = used.get_mut(route.index()).ok_or_else(|| {
                    StructureError::invalid("forward route entry references a missing route")
                })?;
                *slot = true;
            }
        }
        let mut remap = vec![None; self.routes.len()];
        let mut routes = Vec::new();
        for (index, route) in self.routes.iter().copied().enumerate() {
            if used[index] {
                let id = ForwardRouteId(routes.len());
                remap[index] = Some(id);
                routes.push(route);
            }
        }
        for edge in edge_plans.iter_mut() {
            if let Some(route) = edge.forward_route {
                edge.forward_route = remap.get(route.index()).copied().flatten();
            }
        }

        let mut retained = vec![0usize; self.next.len()];
        for (index, route) in self.routes.iter().enumerate() {
            if used[index] {
                retained[route.first.index()] = retained[route.first.index()]
                    .checked_add(1)
                    .ok_or_else(|| {
                        StructureError::invalid("forward route retain count overflow")
                    })?;
            }
        }
        let mut full_children = vec![Vec::<usize>::new(); self.next.len()];
        let mut full_roots = Vec::new();
        for (index, assigned) in self.next_assigned.iter().copied().enumerate() {
            if !assigned {
                continue;
            }
            if let Some(next) = self.next[index] {
                full_children[next.index()].push(index);
            } else {
                full_roots.push(index);
            }
        }
        let mut full_order = Vec::new();
        let mut full_seen = vec![false; self.next.len()];
        let mut full_stack = full_roots;
        while let Some(index) = full_stack.pop() {
            if std::mem::replace(&mut full_seen[index], true) {
                return Err(StructureError::invalid(
                    "forward route graph contains a cycle or duplicate parent",
                ));
            }
            full_order.push(index);
            full_stack.extend(full_children[index].iter().copied());
        }
        if self
            .next_assigned
            .iter()
            .enumerate()
            .any(|(index, assigned)| *assigned && !full_seen[index])
        {
            return Err(StructureError::invalid(
                "forward route graph contains a cycle",
            ));
        }
        for index in full_order.into_iter().rev() {
            if retained[index] == 0 {
                continue;
            }
            if let Some(next) = self.next[index] {
                retained[next.index()] = retained[next.index()]
                    .checked_add(retained[index])
                    .ok_or_else(|| {
                        StructureError::invalid("forward route retain count overflow")
                    })?;
            }
        }
        for (index, retained) in retained.iter().copied().enumerate() {
            if retained == 0 {
                self.next[index] = None;
                self.next_assigned[index] = false;
                self.owner_by_edge[index] = None;
                self.kind_by_edge[index] = None;
            }
        }

        let mut children = vec![Vec::<EdgeRef>::new(); self.next.len()];
        let mut roots = Vec::new();
        for (index, assigned) in self.next_assigned.iter().copied().enumerate() {
            if !assigned {
                continue;
            }
            let edge = EdgeRef(index);
            if let Some(next) = self.next[index] {
                let slot = children.get_mut(next.index()).ok_or_else(|| {
                    StructureError::invalid(format!("{edge} has a missing forward successor"))
                })?;
                slot.push(edge);
            } else {
                roots.push(edge);
            }
        }
        let mut preorder = vec![usize::MAX; self.next.len()];
        let mut subtree_end = vec![usize::MAX; self.next.len()];
        let mut depth = vec![usize::MAX; self.next.len()];
        let mut clock = 0usize;
        let mut stack = Vec::new();
        for root in roots {
            depth[root.index()] = 0;
            stack.push((root, false));
            while let Some((edge, exiting)) = stack.pop() {
                if exiting {
                    subtree_end[edge.index()] = clock;
                    continue;
                }
                if preorder[edge.index()] != usize::MAX {
                    return Err(StructureError::invalid(format!(
                        "forward route graph contains a cycle or duplicate parent at {edge}"
                    )));
                }
                preorder[edge.index()] = clock;
                clock = clock
                    .checked_add(1)
                    .ok_or_else(|| StructureError::invalid("forward route rank overflow"))?;
                stack.push((edge, true));
                for child in children[edge.index()].iter().rev().copied() {
                    depth[child.index()] = depth[edge.index()]
                        .checked_add(1)
                        .ok_or_else(|| StructureError::invalid("forward route depth overflow"))?;
                    stack.push((child, false));
                }
            }
        }
        if let Some(index) = self
            .next_assigned
            .iter()
            .enumerate()
            .find_map(|(index, assigned)| {
                (*assigned && preorder[index] == usize::MAX).then_some(index)
            })
        {
            return Err(StructureError::invalid(format!(
                "forward route graph contains a cycle at edge #{index}"
            )));
        }
        Ok(ForwardRouteArena {
            routes,
            next: self.next,
            preorder,
            subtree_end,
            depth,
            owner_by_edge: self.owner_by_edge,
            kind_by_edge: self.kind_by_edge,
        })
    }
}

struct ForwardRouteArena {
    routes: Vec<ForwardRoutePlan>,
    next: Vec<Option<EdgeRef>>,
    preorder: Vec<usize>,
    subtree_end: Vec<usize>,
    depth: Vec<usize>,
    owner_by_edge: Vec<Option<RegionId>>,
    kind_by_edge: Vec<Option<ForwardRouteKind>>,
}

impl EdgeSemantics {
    fn new(
        proto: &LoweredProto,
        cfg: &Cfg,
        dataflow: &DataflowFacts,
        arena: &RegionArena,
        input: &FinalPlanInput,
        partitions: &[LoopPartitions],
    ) -> Result<Self, StructureError> {
        let layout_edges = layout_edge_facts(cfg, &arena.regions, &arena.navigation)?;
        let loops = LoopQueryIndex::build(cfg, arena, input, partitions, &layout_edges)?;
        let mut planned_breaks = vec![None; cfg.edges.len()];
        for (spec_index, spec) in arena.specs.iter().enumerate() {
            let ContainerKind::Loop(loop_id) = spec.kind else {
                continue;
            };
            let region = arena.slots[spec_index].region();
            for edge in partitions
                .get(loop_id.index())
                .ok_or_else(|| StructureError::invalid("selected loop has no frozen partitions"))?
                .break_routes
                .keys()
                .copied()
            {
                let slot = planned_breaks.get_mut(edge.index()).ok_or_else(|| {
                    StructureError::invalid("loop break route starts outside the CFG arena")
                })?;
                match *slot {
                    Some(owner) if arena.navigation.contains(owner, region) => {
                        *slot = Some(region);
                    }
                    Some(owner) if !arena.navigation.contains(region, owner) => {
                        return Err(StructureError::invalid(
                            "one CFG edge starts break routes for unrelated loops",
                        ));
                    }
                    Some(_) => {}
                    None => *slot = Some(region),
                }
            }
        }
        let mut semantics = Self {
            single_pass_breaks: vec![None; cfg.edges.len()],
            backedges: vec![None; cfg.edges.len()],
            breaks: planned_breaks,
            continues: vec![None; cfg.edges.len()],
            syntax_arms: vec![None; cfg.edges.len()],
            forced_gotos: vec![None; cfg.edges.len()],
            branch_by_header: vec![None; cfg.blocks.len()],
            loops,
            forward_routes: ForwardRouteBuilder::new(cfg.edges.len(), arena.regions.len()),
            early_continues: vec![false; cfg.edges.len()],
            internal_transitions: vec![None; cfg.edges.len()],
            preheader_edges: vec![false; cfg.edges.len()],
            for_syntax_edges: vec![false; cfg.edges.len()],
            normal_tail_edges: vec![false; cfg.edges.len()],
            natural_edges: layout_edges.iter().map(|fact| fact.natural).collect(),
            crosses_island_layout: layout_edges
                .iter()
                .map(|fact| fact.crosses_island_layout)
                .collect(),
            value_decision_edges: vec![None; cfg.edges.len()],
        };
        let forwarding_barriers = input
            .scopes
            .iter()
            .flat_map(|scope| {
                scope
                    .exit
                    .into_iter()
                    .chain(std::iter::once(scope.entry))
                    .chain(
                        scope
                            .close_points
                            .iter()
                            .filter_map(|close| cfg.instr_to_block.get(close.index()).copied()),
                    )
            })
            .collect::<BTreeSet<_>>();
        let label_targets = input
            .residual_transfers
            .iter()
            .filter_map(|residual| cfg.edges.get(residual.edge.index()))
            .map(|edge| edge.to)
            .collect::<BTreeSet<_>>();
        for (index, spec) in arena.specs.iter().enumerate() {
            let region = arena.slots[index].region();
            match spec.kind {
                ContainerKind::SinglePass(id) => {
                    let branch = input.branches.get(id.index()).ok_or_else(|| {
                        StructureError::invalid("single-pass region references missing branch")
                    })?;
                    let fence = branch
                        .region
                        .as_ref()
                        .and_then(|region| region.single_pass_fence.as_ref())
                        .ok_or_else(|| {
                            StructureError::invalid(
                                "single-pass region has no frozen fence evidence",
                            )
                        })?;
                    for edge in &fence.escape_edges {
                        let slot = semantics
                            .single_pass_breaks
                            .get_mut(edge.index())
                            .ok_or_else(|| {
                                StructureError::invalid(
                                    "single-pass fence references an edge outside the CFG arena",
                                )
                            })?;
                        if slot.replace(region).is_some() {
                            return Err(StructureError::invalid(
                                "one CFG edge belongs to multiple single-pass fences",
                            ));
                        }
                    }
                }
                ContainerKind::Branch(id) => {
                    let branch = &input.branches[id.index()];
                    semantics.branch_by_header[branch.branch.header.index()] = Some(region);
                    if let Some(condition) = branch
                        .condition
                        .and_then(|condition| input.conditions.get(condition.index()))
                        && let ShortCircuitExit::BranchExit { truthy, falsy } =
                            condition.candidate.exit
                    {
                        for arc in &condition.arcs {
                            let internal_len = match arc.target {
                                crate::structure::ShortCircuitTarget::Node(_) => arc.edges.len(),
                                crate::structure::ShortCircuitTarget::Value(_)
                                | crate::structure::ShortCircuitTarget::TruthyExit
                                | crate::structure::ShortCircuitTarget::FalsyExit => {
                                    arc.edges.len().saturating_sub(1)
                                }
                            };
                            for &edge in arc.edges.iter().take(internal_len) {
                                let slot = semantics
                                        .internal_transitions
                                        .get_mut(edge.index())
                                        .ok_or_else(|| {
                                            StructureError::invalid(
                                                "condition route references an edge outside the CFG arena",
                                            )
                                        })?;
                                *slot = Some(region);
                            }
                        }
                        for block in &condition.candidate.blocks {
                            for edge in &cfg.succs[block.index()] {
                                let target = cfg.edges[edge.index()].to;
                                let arm = if target == truthy {
                                    Some(super::BranchArm::Truthy)
                                } else if target == falsy {
                                    Some(super::BranchArm::Falsy)
                                } else {
                                    None
                                };
                                if let Some(arm) = arm {
                                    semantics.syntax_arms[edge.index()] = Some((region, arm));
                                    let target_is_inside = arena.region_by_block[target.index()]
                                        .is_some_and(|target_region| {
                                            arena.navigation.contains(region, target_region)
                                        });
                                    if !target_is_inside && branch.branch.merge != Some(target) {
                                        // condition evidence 只能决定真假语义，不能把
                                        // 跳回 branch containment 外的边一律当空 arm；
                                        // 只有布局紧邻的 sibling 可以自然承接，其余仍
                                        // 由 forced-goto 保留显式 transfer。
                                        semantics.forced_gotos[edge.index()] =
                                            Some(crate::structure::GotoReason::IrreducibleFlow);
                                    }
                                }
                            }
                        }
                    }
                }
                ContainerKind::Loop(id) => {
                    let loop_ = &input.loops[id.index()].candidate;
                    let partition = partitions.get(id.index()).ok_or_else(|| {
                        StructureError::invalid("selected loop has no frozen partitions")
                    })?;
                    for edge in &loop_.backedges {
                        semantics.backedges[edge.index()] = Some(region);
                    }
                    for (edge, route) in &partition.break_routes {
                        if route
                            .iter()
                            .any(|edge| semantics.single_pass_breaks[edge.index()].is_some())
                        {
                            // 同一路径先退出内层 loop、随后退出 single-pass fence 时，
                            // 两个词法 transfer 必须分别由各自 region 发射；forwarding
                            // 不能把后一个 break 吞进前一个 edge。
                            continue;
                        }
                        if let Some(route) = semantics.forward_routes.install(
                            cfg,
                            ForwardRouteKind::ExclusiveBreak,
                            region,
                            route,
                        )? {
                            semantics.forward_routes.bind(*edge, route)?;
                        }
                    }
                    let continue_reachable = loop_
                        .continue_target
                        .map(|target| body_blocks_reaching_target(cfg, &partition.body, target))
                        .unwrap_or_default();
                    let continue_forward_index = loop_
                        .continue_target
                        .map(|target| {
                            PureContinueForwardIndex::build(
                                cfg,
                                arena,
                                partition,
                                target,
                                &forwarding_barriers,
                                &label_targets,
                            )
                        })
                        .transpose()?;
                    let direct_latch_edges = if let Some(target) = loop_.continue_target
                        && target != loop_.header
                        && !matches!(
                            loop_.kind_hint,
                            crate::structure::LoopKindHint::RepeatLike
                                | crate::structure::LoopKindHint::NumericForLike
                                | crate::structure::LoopKindHint::GenericForLike
                        )
                        && let Some(route) = direct_continue_latch_route(
                            cfg,
                            arena,
                            partition,
                            loop_.header,
                            target,
                            &forwarding_barriers,
                        ) {
                        Some(route)
                    } else {
                        None
                    };
                    let mut direct_latch_route = None;
                    let repeat_condition_route =
                        if loop_.kind_hint == crate::structure::LoopKindHint::RepeatLike {
                            loop_
                                .continue_target
                                .and_then(|target| {
                                    repeat_continue_forwarding_route(
                                        cfg,
                                        arena,
                                        partition,
                                        loop_,
                                        target,
                                        &forwarding_barriers,
                                        &label_targets,
                                    )
                                })
                                .map(|route| {
                                    let kind = repeat_condition_route_kind(
                                        cfg,
                                        input,
                                        input.loops[id.index()].condition,
                                        &route,
                                    )?;
                                    Ok::<_, StructureError>(kind.map(|kind| (route, kind)))
                                })
                                .transpose()?
                                .flatten()
                        } else {
                            None
                        };
                    let mut repeat_condition_route_id = None;
                    for edge in &partition.continues {
                        if semantics.breaks[edge.index()].is_some_and(|owner| owner != region)
                            || semantics
                                .break_region(*edge)
                                .is_some_and(|owner| owner != region)
                        {
                            // 同一条物理边可以先退出内层 loop，再自然进入当前
                            // repeat 的尾条件。它的显式语义属于内层 break；不能再把
                            // 整条尾条件路径绑定成外层 continue forwarding route。
                            continue;
                        }
                        if semantics.forward_routes.contains_edge(*edge) {
                            continue;
                        }
                        let Some(target) = loop_.continue_target else {
                            continue;
                        };
                        let direct = cfg.edges[edge.index()].to == target;
                        let forwarding_route = (!direct)
                            .then(|| {
                                continue_forward_index
                                    .as_ref()
                                    .and_then(|index| index.route(cfg, *edge))
                            })
                            .flatten();
                        let reaches_target = direct || forwarding_route.is_some();
                        let source_edges = &cfg.succs[cfg.edges[edge.index()].from.index()];
                        let explicit_continue = source_edges.len() == 1
                            || source_edges.iter().any(|candidate| {
                                *candidate != *edge
                                    && continue_reachable.contains(&cfg.edges[candidate.index()].to)
                            });
                        let natural_repeat_tail = loop_.kind_hint
                            == crate::structure::LoopKindHint::RepeatLike
                            && direct
                            && semantics.natural_edges[edge.index()];
                        if !natural_repeat_tail
                            && reaches_target
                            && explicit_continue
                            && (continue_edge_bypasses_body(cfg, partition, *edge)
                                || (loop_.continue_edges.contains(edge)
                                    || input.loops[id.index()]
                                        .semantic_continue_edges
                                        .contains(edge))
                                    && source_edges.len() == 1)
                        {
                            if let Some(route) = forwarding_route {
                                let installed =
                                    if let Some((suffix, kind)) = repeat_condition_route.as_ref() {
                                        semantics.forward_routes.install_functional_composed(
                                            cfg, *kind, region, route, suffix,
                                        )?
                                    } else {
                                        semantics.forward_routes.install_functional(
                                            cfg,
                                            ForwardRouteKind::ContinueToTarget,
                                            region,
                                            route,
                                        )?
                                    };
                                if let Some(route_id) = installed {
                                    semantics.forward_routes.bind(*edge, route_id)?;
                                }
                            }
                            if direct {
                                if loop_.kind_hint == crate::structure::LoopKindHint::RepeatLike {
                                    let Some((route, kind)) = repeat_condition_route.as_ref()
                                    else {
                                        continue;
                                    };
                                    let route_id = if let Some(route_id) = repeat_condition_route_id
                                    {
                                        route_id
                                    } else {
                                        let Some(route_id) = semantics
                                            .forward_routes
                                            .install(cfg, *kind, region, route)?
                                        else {
                                            continue;
                                        };
                                        repeat_condition_route_id = Some(route_id);
                                        route_id
                                    };
                                    semantics.forward_routes.bind(*edge, route_id)?;
                                } else if matches!(
                                    loop_.kind_hint,
                                    crate::structure::LoopKindHint::NumericForLike
                                        | crate::structure::LoopKindHint::GenericForLike
                                ) {
                                    // VM for 的 target 已由协议 lowering 吸收，不需要额外 route。
                                } else if target != loop_.header {
                                    let Some(edges) = direct_latch_edges.as_deref() else {
                                        continue;
                                    };
                                    let route = if let Some(route) = direct_latch_route {
                                        route
                                    } else {
                                        let Some(route) = semantics.forward_routes.install(
                                            cfg,
                                            ForwardRouteKind::ContinueLatch,
                                            region,
                                            edges,
                                        )?
                                        else {
                                            continue;
                                        };
                                        direct_latch_route = Some(route);
                                        route
                                    };
                                    semantics.forward_routes.bind(*edge, route)?;
                                }
                            }
                            semantics.continues[edge.index()] = Some(region);
                            semantics.early_continues[edge.index()] = true;
                        }
                    }
                    let forwarded_edges = std::mem::take(
                        &mut semantics.forward_routes.edges_by_owner[region.index()],
                    );
                    for forwarded in forwarded_edges {
                        if semantics.forward_routes.kind_by_edge[forwarded.index()]
                            == Some(ForwardRouteKind::ExclusiveBreak)
                        {
                            continue;
                        }
                        semantics.internal_transitions[forwarded.index()] = Some(region);
                        let pad = cfg.edges[forwarded.index()].from;
                        for incoming in &cfg.preds[pad.index()] {
                            let source = cfg.edges[incoming.index()].from;
                            if partition.body.contains(&source) {
                                semantics.internal_transitions[incoming.index()] = Some(region);
                            }
                        }
                    }
                    for block in &partition.body {
                        for edge in &cfg.succs[block.index()] {
                            if partition.control.contains(&cfg.edges[edge.index()].to) {
                                semantics.internal_transitions[edge.index()] = Some(region);
                            }
                        }
                    }
                    for block in &partition.control {
                        for edge in &cfg.succs[block.index()] {
                            if partition.control.contains(&cfg.edges[edge.index()].to) {
                                semantics.internal_transitions[edge.index()] = Some(region);
                            }
                        }
                    }
                    if let Some(normal_tail) = &partition.normal_tail {
                        for block in &normal_tail.blocks {
                            for edge in &cfg.succs[block.index()] {
                                semantics.internal_transitions[edge.index()] = Some(region);
                                semantics.normal_tail_edges[edge.index()] = true;
                            }
                        }
                    }
                    let condition_terminals = input.loops[id.index()]
                        .condition
                        .and_then(|condition| input.conditions.get(condition.index()))
                        .map(|condition| freeze_condition(proto, cfg, dataflow, condition, None))
                        .transpose()?
                        .map(|condition| [condition.truthy, condition.falsy]);
                    let control_edges =
                        freeze_loop_control_edges(cfg, loop_, partition, condition_terminals)?;
                    for edge in [control_edges.preheader_body, control_edges.preheader_exit]
                        .into_iter()
                        .flatten()
                    {
                        semantics.preheader_edges[edge.index()] = true;
                    }
                    let is_for_loop = matches!(
                        loop_.kind_hint,
                        crate::structure::LoopKindHint::NumericForLike
                            | crate::structure::LoopKindHint::GenericForLike
                    );
                    for edge in control_edges
                        .preheader_body
                        .into_iter()
                        .chain(control_edges.body)
                    {
                        semantics.syntax_arms[edge.index()] =
                            Some((region, super::BranchArm::LoopBody));
                        semantics.for_syntax_edges[edge.index()] = is_for_loop;
                    }
                    for edge in control_edges
                        .preheader_exit
                        .into_iter()
                        .chain(control_edges.exit)
                    {
                        semantics.syntax_arms[edge.index()] =
                            Some((region, super::BranchArm::LoopExit));
                        semantics.for_syntax_edges[edge.index()] = is_for_loop;
                    }
                }
                ContainerKind::ValueDecision(id) => {
                    let decision = &input.value_decisions[id.index()].candidate;
                    let ShortCircuitExit::ValueMerge(continuation) = decision.exit else {
                        return Err(StructureError::invalid(
                            "selected value decision has no merge continuation",
                        ));
                    };
                    for block in &spec.blocks {
                        for edge in &cfg.succs[block.index()] {
                            let target = cfg.edges[edge.index()].to;
                            if !spec.blocks.contains(&target) && target != continuation {
                                return Err(StructureError::invalid(
                                    "value decision has an undeclared exit",
                                ));
                            }
                            let slot = &mut semantics.value_decision_edges[edge.index()];
                            if slot.replace(region).is_some() {
                                return Err(StructureError::invalid(
                                    "one CFG edge belongs to multiple value decisions",
                                ));
                            }
                        }
                    }
                }
                ContainerKind::Island(_) | ContainerKind::Residual(_) => {}
            }
        }
        Ok(semantics)
    }

    fn classify(
        &self,
        cfg: &Cfg,
        edge_ref: EdgeRef,
        goto_reason: Option<crate::structure::GotoReason>,
        caps: ControlFlowCaps,
        default_owner: RegionId,
    ) -> (RegionId, EdgeTransfer) {
        let edge = cfg.edges[edge_ref.index()];
        if !cfg.reachable_blocks.contains(&edge.from) {
            return (default_owner, EdgeTransfer::Unreachable);
        }
        match edge.kind {
            EdgeKind::Return => return (default_owner, EdgeTransfer::Return),
            EdgeKind::TailCall => return (default_owner, EdgeTransfer::TailCall),
            EdgeKind::Fallthrough
            | EdgeKind::Jump
            | EdgeKind::BranchTrue
            | EdgeKind::BranchFalse
            | EdgeKind::LoopBody
            | EdgeKind::LoopExit => {}
        }
        if self.forward_routes.kind_by_edge[edge_ref.index()]
            == Some(ForwardRouteKind::ExclusiveBreak)
            && let Some(region) = self.forward_routes.owner_by_edge[edge_ref.index()]
        {
            // entry edge 已唯一持有语义 break；route 内部 jump 只承载 move/phi
            // forwarding。若末边同时是祖先 loop backedge，则只保留祖先的迭代
            // 语义，不能再次把同一条物理边解释成内层或 single-pass break。
            return match self.backedges[edge_ref.index()] {
                Some(ancestor) if ancestor != region => {
                    (ancestor, EdgeTransfer::LoopBack(ancestor))
                }
                _ => (region, EdgeTransfer::Fallthrough),
            };
        }
        if let Some(region) = self.single_pass_breaks[edge_ref.index()] {
            return (region, EdgeTransfer::Break(region));
        }
        if self.breaks[edge_ref.index()].is_none()
            && self.break_region(edge_ref).is_none()
            && !self.natural_edges[edge_ref.index()]
            && let Some(kind) = shared_pure_terminal_kind(cfg, edge.to)
        {
            return (
                default_owner,
                if kind == EdgeKind::Return {
                    EdgeTransfer::Return
                } else {
                    EdgeTransfer::TailCall
                },
            );
        }
        if let Some(region) = self.value_decision_edges[edge_ref.index()] {
            return (region, EdgeTransfer::Fallthrough);
        }
        if caps.continue_stmt
            && self.early_continues[edge_ref.index()]
            && let Some(region) = self.continues[edge_ref.index()]
            && !self.is_nested_loop_exit_to_ancestor(edge_ref, edge.from, region)
            && !self.exits_nested_loop_before_continue(edge_ref, edge.from, region)
            && (!self.natural_edges[edge_ref.index()]
                || self.loops.control_by_block[edge.to.index()] == Some(region))
        {
            // 显式 continue 可以同时是物理 backedge；语义 transfer 必须先于
            // natural-loop latch 分类，否则 HIR 会把条件 arm 静默吞成隐式回边。
            return (region, EdgeTransfer::Continue(region));
        }
        if let Some(region) = self.backedges[edge_ref.index()] {
            let source_loop = self.loops.innermost(edge.from);
            if self.for_syntax_edges[edge_ref.index()]
                && let Some(source) = source_loop
                && source != region
                && self.syntax_arms[edge_ref.index()] == Some((source, super::BranchArm::LoopExit))
            {
                // VM-for 的正常 exhaustion 可以和祖先 loop backedge 共用物理边。
                // child 语法先吸收 LoopExit；祖先迭代由外围 loop 隐式完成。
                return (source, EdgeTransfer::BranchArm(super::BranchArm::LoopExit));
            }
            let propagated_break =
                source_loop
                    .filter(|source| *source != region)
                    .and_then(|source| {
                        self.loops
                            .propagated_break_by_region
                            .get(source.index())
                            .copied()
                            .flatten()
                    });
            if let Some(target) = propagated_break
                && !self.normal_tail_edges[edge_ref.index()]
                && self.break_region(edge_ref) == Some(target)
            {
                return (target, EdgeTransfer::Break(target));
            }
            // 同一条物理边可以先离开内层 loop，再自然落到祖先 loop 的 latch。
            // 源码在此必须先发射内层 break；祖先回边由外围 loop 语法隐式完成。
            // normal-tail 自身的出边已经位于内层 loop 之后，不能再次解释成 break。
            if !self.normal_tail_edges[edge_ref.index()]
                && let Some(inner) = self.break_region(edge_ref)
                && inner != region
                && self.loops.innermost(edge.from) == Some(inner)
            {
                return (inner, EdgeTransfer::Break(inner));
            }
            // Luau 可把内层空 generic-for 的 VM exit 与祖先 loop backedge 合并成
            // 同一条物理边；祖先回边负责最终 transfer，内层 VM protocol 隐式吸收语法边。
            return (region, EdgeTransfer::LoopBack(region));
        }
        if self.for_syntax_edges[edge_ref.index()]
            && let Some((region, arm)) = self.syntax_arms[edge_ref.index()]
        {
            // VM-for 的 body/exit edge 先由最内层语法 owner 吸收，不能再被外层
            // break/continue 推导抢占。离开 child 后的自然布局仍由 continuation 决定。
            if arm == super::BranchArm::LoopExit
                && self.loops.propagated_break_by_region[region.index()]
                    .is_some_and(|target| self.break_region(edge_ref) == Some(target))
            {
                // 全部语法出口已证明共享同一外层 break 时，物理 exit 只结束当前
                // VM-for；外层 transfer 由 loop completion 统一发射一次。
                return (region, EdgeTransfer::BranchArm(arm));
            }
            if arm == super::BranchArm::LoopExit
                && let Some(target) = self.break_region(edge_ref)
                && target != region
                && self.loops.innermost(edge.from) == Some(region)
                && !self.break_requires_island_goto(edge_ref, edge.to, target)
            {
                // VM-for 的正常 exit 可以同时结束包含它的外层 loop。VM 语法角色
                // 已冻结在 LoopControlEdges；最终源码 transfer 必须保留外层 break，
                // 否则 HIR 会在 for 后继续执行仅供其它 exit 使用的 sibling tail。
                return (region, EdgeTransfer::Break(target));
            }
            if arm == super::BranchArm::LoopExit
                && !self.natural_edges[edge_ref.index()]
                && self.breaks[edge_ref.index()].is_none()
                && (self.crosses_island_layout[edge_ref.index()]
                    || self
                        .loops
                        .innermost_spec(edge.from)
                        .is_some_and(|(_, owner)| {
                            self.loops.continuation[owner.index()] != Some(edge.to)
                                && self.loops.normal_tail_entry[owner.index()] != Some(edge.to)
                        }))
            {
                return (
                    region,
                    EdgeTransfer::Goto(
                        LabelPlanId(edge.to.index()),
                        goto_reason.unwrap_or(crate::structure::GotoReason::IrreducibleFlow),
                    ),
                );
            }
            return (region, EdgeTransfer::BranchArm(arm));
        }
        if let Some(region) = self.breaks[edge_ref.index()] {
            if self.break_requires_island_goto(edge_ref, edge.to, region) {
                return (
                    region,
                    EdgeTransfer::Goto(
                        LabelPlanId(edge.to.index()),
                        goto_reason.unwrap_or(crate::structure::GotoReason::IrreducibleFlow),
                    ),
                );
            }
            return (region, EdgeTransfer::Break(region));
        }
        if !self.for_syntax_edges[edge_ref.index()]
            && !self.normal_tail_edges[edge_ref.index()]
            && !self.preheader_edges[edge_ref.index()]
            && let Some(region) = self.break_region(edge_ref)
        {
            let innermost = self.loops.innermost(edge.from);
            let exits_innermost_control = innermost != Some(region)
                && innermost.is_some()
                && self.loops.control_by_block[edge.from.index()] == innermost;
            if innermost != Some(region) && !exits_innermost_control {
                if self.loops.propagates_break(edge.from, region)
                    && !self.break_requires_island_goto(edge_ref, edge.to, region)
                {
                    return (region, EdgeTransfer::Break(region));
                }
                return (
                    default_owner,
                    EdgeTransfer::Goto(
                        LabelPlanId(edge.to.index()),
                        crate::structure::GotoReason::UnstructuredBreakLike,
                    ),
                );
            }
            if self.break_requires_island_goto(edge_ref, edge.to, region) {
                return (
                    region,
                    EdgeTransfer::Goto(
                        LabelPlanId(edge.to.index()),
                        goto_reason.unwrap_or(crate::structure::GotoReason::IrreducibleFlow),
                    ),
                );
            }
            return (region, EdgeTransfer::Break(region));
        }
        let branch_owner = self.branch_by_header[edge.from.index()];
        let loop_owner = self.loops.control_by_block[edge.from.index()];
        let structured_branch_arm = branch_owner.is_some()
            && matches!(edge.kind, EdgeKind::BranchTrue | EdgeKind::BranchFalse);
        let mut branch_around_continue = false;
        if let Some(region) = self.continues[edge_ref.index()]
            && self.early_continues[edge_ref.index()]
            && !self.is_nested_loop_exit_to_ancestor(edge_ref, edge.from, region)
            && !self.exits_nested_loop_before_continue(edge_ref, edge.from, region)
            && (!self.natural_edges[edge_ref.index()]
                || self.loops.control_by_block[edge.to.index()] == Some(region))
        {
            if caps.continue_stmt {
                return (region, EdgeTransfer::Continue(region));
            } else if structured_branch_arm {
                // 条件 continue 总能等价写成 branch-around-tail；即使目标支持
                // continue 不可用，也只允许已经有结构化 arm ownership 的 tail 改写。
                branch_around_continue = true;
            } else {
                return (
                    region,
                    EdgeTransfer::Goto(
                        LabelPlanId(edge.to.index()),
                        crate::structure::GotoReason::UnstructuredContinueLike,
                    ),
                );
            }
        }
        if let Some((_, region)) = self.loops.innermost_spec(edge.from)
            && !matches!(
                self.syntax_arms[edge_ref.index()],
                Some((owner, super::BranchArm::LoopBody | super::BranchArm::LoopExit))
                    if owner == region
            )
            && self.loops.leaves_innermost_loop[edge_ref.index()]
            && self.loops.continuation[region.index()] != Some(edge.to)
        {
            // island 的下一个 layout item 不等于结构化 loop body 内部 edge 的自然
            // fallthrough。离开 for child 且不去其声明 continuation 的边必须在 loop
            // 语法体内显式发射，否则条件 goto 会被静默吞掉。
            return (
                region,
                EdgeTransfer::Goto(
                    LabelPlanId(edge.to.index()),
                    goto_reason.unwrap_or(crate::structure::GotoReason::UnstructuredBreakLike),
                ),
            );
        }
        if let Some(reason) = self.forced_gotos[edge_ref.index()] {
            let natural_tail_to_latch =
                structured_branch_arm && self.continue_target_region(edge_ref).is_some();
            let natural_empty_arm = self.natural_edges[edge_ref.index()]
                && self.syntax_arms[edge_ref.index()].is_some();
            let selected_loop_arm = matches!(
                self.syntax_arms[edge_ref.index()],
                Some((_, super::BranchArm::LoopBody | super::BranchArm::LoopExit))
            );
            let internal_transition = self.internal_transitions[edge_ref.index()].is_some();
            if !branch_around_continue
                && !natural_tail_to_latch
                && !natural_empty_arm
                && !selected_loop_arm
                && !internal_transition
            {
                return (
                    default_owner,
                    EdgeTransfer::Goto(LabelPlanId(edge.to.index()), reason),
                );
            }
        }
        if self.crosses_island_layout[edge_ref.index()] && !self.natural_edges[edge_ref.index()] {
            return (
                default_owner,
                EdgeTransfer::Goto(
                    LabelPlanId(edge.to.index()),
                    goto_reason.unwrap_or(crate::structure::GotoReason::IrreducibleFlow),
                ),
            );
        }
        if let Some((region, arm)) = self.syntax_arms[edge_ref.index()] {
            return (region, EdgeTransfer::BranchArm(arm));
        }
        if let Some(region) = self.internal_transitions[edge_ref.index()] {
            return (region, EdgeTransfer::Fallthrough);
        }
        match (edge.kind, branch_owner, loop_owner) {
            (EdgeKind::BranchTrue, Some(owner), _) | (EdgeKind::BranchTrue, None, Some(owner)) => {
                return (owner, EdgeTransfer::BranchArm(super::BranchArm::Truthy));
            }
            (EdgeKind::BranchFalse, Some(owner), _)
            | (EdgeKind::BranchFalse, None, Some(owner)) => {
                return (owner, EdgeTransfer::BranchArm(super::BranchArm::Falsy));
            }
            (EdgeKind::LoopBody, _, Some(owner)) => {
                return (owner, EdgeTransfer::BranchArm(super::BranchArm::LoopBody));
            }
            (EdgeKind::LoopExit, _, Some(owner)) => {
                return (owner, EdgeTransfer::BranchArm(super::BranchArm::LoopExit));
            }
            _ => {}
        }
        if let Some(reason) = goto_reason {
            if caps.continue_stmt
                && matches!(
                    reason,
                    crate::structure::GotoReason::UnstructuredContinueLike
                        | crate::structure::GotoReason::CrossLoopContinueLike
                )
                && let Some(region) = self.continue_target_region(edge_ref)
            {
                return (region, EdgeTransfer::Continue(region));
            }
            return (
                default_owner,
                EdgeTransfer::Goto(LabelPlanId(edge.to.index()), reason),
            );
        }
        if matches!(
            edge.kind,
            EdgeKind::BranchTrue | EdgeKind::BranchFalse | EdgeKind::LoopBody | EdgeKind::LoopExit
        ) {
            if self.natural_edges[edge_ref.index()] {
                return (default_owner, EdgeTransfer::Fallthrough);
            }
            return (
                default_owner,
                EdgeTransfer::Goto(
                    LabelPlanId(edge.to.index()),
                    crate::structure::GotoReason::IrreducibleFlow,
                ),
            );
        }
        if self.natural_edges[edge_ref.index()] {
            (default_owner, EdgeTransfer::Fallthrough)
        } else {
            (
                default_owner,
                EdgeTransfer::Goto(
                    LabelPlanId(edge.to.index()),
                    crate::structure::GotoReason::IrreducibleFlow,
                ),
            )
        }
    }

    fn break_region(&self, edge_ref: EdgeRef) -> Option<RegionId> {
        // 多层循环可能共享同一个 continuation。直接边必须退出所有这些循环，因此
        // 选择覆盖最大的最外层 region；HIR 会逐层把该 transfer 物化成 break。
        self.loops
            .break_owner_by_edge
            .get(edge_ref.index())
            .copied()
            .flatten()
    }

    fn break_requires_island_goto(
        &self,
        edge_ref: EdgeRef,
        target: BlockRef,
        region: RegionId,
    ) -> bool {
        self.loops
            .continuation
            .get(region.index())
            .copied()
            .flatten()
            == Some(target)
            && self.crosses_island_layout[edge_ref.index()]
            && !self.natural_edges[edge_ref.index()]
    }

    fn continue_target_region(&self, edge: EdgeRef) -> Option<RegionId> {
        self.loops
            .continue_owner_by_edge
            .get(edge.index())
            .copied()
            .flatten()
    }

    fn is_nested_loop_exit_to_ancestor(
        &self,
        edge: EdgeRef,
        source: BlockRef,
        target: RegionId,
    ) -> bool {
        matches!(
            self.syntax_arms.get(edge.index()).copied().flatten(),
            Some((owner, super::BranchArm::LoopExit))
                if owner != target
                    && self.loops.innermost(source) == Some(owner)
        )
    }

    fn exits_nested_loop_before_continue(
        &self,
        edge: EdgeRef,
        source: BlockRef,
        continue_target: RegionId,
    ) -> bool {
        self.break_region(edge).is_some_and(|break_target| {
            break_target != continue_target && self.loops.innermost(source) == Some(break_target)
        })
    }
}

/// 先把复合 condition 的语义出口固化到 branch，再按目标能力规划 continue。
///
/// raw BranchCandidate 的 local join 可能落在 condition DAG 内部，不能拿它决定共享尾。
/// 原生 continue 目标保留已证明的 transfer；其余目标才把 Guard 改写为包住 tail 的
/// 单臂 branch。
struct LoopRewriteIndex {
    containing_by_block: Vec<Vec<usize>>,
    preorder: Vec<usize>,
    subtree_end: Vec<usize>,
    loops_by_header: Vec<Vec<usize>>,
}

impl LoopRewriteIndex {
    fn build(cfg: &Cfg, loops: &[super::LoopPlanInput]) -> Result<Self, StructureError> {
        let score = |index: usize| {
            (
                loops[index].candidate.body_scope_blocks.len(),
                loops[index].candidate.blocks.len(),
                index,
            )
        };
        let mut loop_header_by_block = vec![false; cfg.blocks.len()];
        for loop_ in loops {
            let Some(slot) = loop_header_by_block.get_mut(loop_.candidate.header.index()) else {
                return Err(StructureError::invalid(
                    "loop rewrite header is outside the CFG block arena",
                ));
            };
            *slot = true;
        }
        let mut owners_by_loop_header = vec![Vec::new(); cfg.blocks.len()];
        let mut containing_by_block = vec![Vec::new(); cfg.blocks.len()];
        let mut epoch_by_block = vec![0u32; cfg.blocks.len()];
        let mut epoch = 0u32;
        for (index, loop_) in loops.iter().enumerate() {
            epoch = epoch.wrapping_add(1);
            if epoch == 0 {
                epoch_by_block.fill(0);
                epoch = 1;
            }
            for block in loop_
                .candidate
                .blocks
                .iter()
                .chain(&loop_.candidate.body_scope_blocks)
            {
                let Some(seen) = epoch_by_block.get_mut(block.index()) else {
                    return Err(StructureError::invalid(
                        "loop rewrite index references a block outside the CFG arena",
                    ));
                };
                if *seen == epoch {
                    continue;
                }
                *seen = epoch;
                containing_by_block[block.index()].push(index);
                if loop_header_by_block[block.index()] {
                    owners_by_loop_header[block.index()].push(index);
                }
            }
        }

        let mut parent = vec![None; loops.len()];
        for (header, owners) in owners_by_loop_header.iter_mut().enumerate() {
            owners.sort_unstable_by_key(|index| score(*index));
            owners.dedup();
            if loop_header_by_block[header] && owners.is_empty() {
                return Err(StructureError::invalid(format!(
                    "loop rewrite header block #{header} has no owning loop"
                )));
            }
        }
        for (index, loop_) in loops.iter().enumerate() {
            let owners = owners_by_loop_header
                .get(loop_.candidate.header.index())
                .ok_or_else(|| {
                    StructureError::invalid("loop rewrite header is outside the CFG block arena")
                })?;
            let self_position = owners.binary_search_by_key(&score(index), |owner| score(*owner));
            let Ok(self_position) = self_position else {
                return Err(StructureError::invalid(format!(
                    "loop rewrite node #{index} is absent from its header owner index"
                )));
            };
            parent[index] = owners.get(self_position + 1).copied();
        }
        let mut children = vec![Vec::new(); loops.len()];
        for (index, parent) in parent.iter().copied().enumerate() {
            if let Some(parent) = parent {
                children[parent].push(index);
            }
        }
        for children in &mut children {
            children.sort_unstable_by_key(|index| score(*index));
        }

        let mut preorder = vec![usize::MAX; loops.len()];
        let mut subtree_end = vec![usize::MAX; loops.len()];
        let mut order = Vec::with_capacity(loops.len());
        let mut pending = parent
            .iter()
            .enumerate()
            .filter_map(|(index, parent)| parent.is_none().then_some(index))
            .rev()
            .map(|root| (root, false))
            .collect::<Vec<_>>();
        while let Some((node, leaving)) = pending.pop() {
            if leaving {
                subtree_end[node] = order.len();
                continue;
            }
            if preorder[node] != usize::MAX {
                return Err(StructureError::invalid(
                    "loop rewrite containment contains a cycle",
                ));
            }
            preorder[node] = order.len();
            order.push(node);
            pending.push((node, true));
            for child in children[node].iter().rev().copied() {
                pending.push((child, false));
            }
        }
        if let Some(index) = preorder.iter().position(|preorder| *preorder == usize::MAX) {
            return Err(StructureError::invalid(format!(
                "loop rewrite node #{index} is disconnected from its containment forest"
            )));
        }

        let mut loops_by_header = vec![Vec::new(); cfg.blocks.len()];
        for (index, loop_) in loops.iter().enumerate() {
            loops_by_header[loop_.candidate.header.index()].push(index);
        }
        for entries in &mut loops_by_header {
            entries.sort_unstable_by_key(|index| score(*index));
        }
        for entries in &mut containing_by_block {
            entries.sort_unstable_by_key(|index| score(*index));
        }
        Ok(Self {
            containing_by_block,
            preorder,
            subtree_end,
            loops_by_header,
        })
    }

    fn containing(&self, block: BlockRef) -> &[usize] {
        self.containing_by_block
            .get(block.index())
            .map_or(&[], Vec::as_slice)
    }

    fn contains_loop(&self, ancestor: usize, descendant: usize) -> bool {
        let Some(start) = self.preorder.get(ancestor).copied() else {
            return false;
        };
        let Some(end) = self.subtree_end.get(ancestor).copied() else {
            return false;
        };
        self.preorder
            .get(descendant)
            .is_some_and(|descendant| start <= *descendant && *descendant < end)
    }

    fn at_header(&self, block: BlockRef) -> &[usize] {
        self.loops_by_header
            .get(block.index())
            .map_or(&[], Vec::as_slice)
    }
}

fn legalize_conditional_continues(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    caps: ControlFlowCaps,
    input: &mut FinalPlanInput,
) -> Result<(), StructureError> {
    let loop_index = LoopRewriteIndex::build(cfg, &input.loops)?;
    if caps.continue_stmt {
        normalize_condition_continue_arms(proto, cfg, graph_facts, &loop_index, input)?;
    }
    let break_rewrites = input
        .branches
        .iter()
        .enumerate()
        .filter_map(|(index, branch)| {
            let mut domain = loop_break_arm_domain(cfg, branch, &input.loops, &loop_index)?;
            domain.included_blocks.push(branch.branch.header);
            Some((index, domain))
        })
        .collect::<Vec<_>>();
    let mut has_loop_break_arm = vec![false; input.branches.len()];
    for (index, domain) in break_rewrites {
        has_loop_break_arm[index] = true;
        if let Some(region) = &mut input.branches[index].region {
            region.replace_domain(domain);
        }
    }

    let rewrites = input
        .branches
        .iter()
        .enumerate()
        .filter_map(|(index, branch)| {
            // 同一物理出口可能先 break 内层 loop，再自然进入祖先 loop 的下一轮。
            // 此时内层词法 owner 必须优先，不能再把它翻成祖先 loop 的 continue guard。
            if has_loop_break_arm[index] || branch.branch.kind != BranchKind::Guard {
                return None;
            }
            let lexical_tail = branch.branch.merge?;
            let escape = branch.branch.then_entry;
            let conditional_loop =
                conditional_continue_loop(proto, cfg, branch, &input.loops, &loop_index);
            let body_tail_loop =
                body_tail_guard_loop(proto, cfg, branch, &input.loops, &loop_index);
            if caps.continue_stmt && conditional_loop.is_some() && body_tail_loop.is_none() {
                return None;
            }
            body_tail_loop.or(conditional_loop)?;
            let tail = lexical_tail;
            Some((index, tail, escape, branch.branch.header))
        })
        .collect::<Vec<_>>();
    for (index, tail, escape, header) in rewrites {
        rewrite_one_arm_branch(graph_facts, &mut input.branches[index], tail, escape);
        if let Some(region) = &mut input.branches[index].region {
            region.replace_domain(BranchRegionDomain {
                spans: Vec::new(),
                included_blocks: vec![header, tail],
            });
        }
    }

    if caps.continue_stmt {
        let rewrites = input
            .branches
            .iter()
            .enumerate()
            .filter_map(|(index, branch)| {
                let mut domain =
                    native_continue_arm_domain(proto, cfg, branch, &input.loops, &loop_index)?;
                domain.included_blocks.push(branch.branch.header);
                Some((index, domain))
            })
            .collect::<Vec<_>>();
        for (index, domain) in rewrites {
            if let Some(region) = &mut input.branches[index].region {
                // continue pad 可以同时承接正常 loop tail，因此不是 branch arm 的
                // containment child；该 edge 已由最终 Continue transfer 唯一表示。
                region.replace_domain(domain);
            }
        }
        return Ok(());
    }
    Ok(())
}

fn normalize_condition_continue_arms(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    loop_index: &LoopRewriteIndex,
    input: &mut FinalPlanInput,
) -> Result<(), StructureError> {
    struct Rewrite {
        branch: usize,
        loop_: usize,
        continue_entry: BlockRef,
        normal_entry: BlockRef,
        domain: BranchRegionDomain,
        transfers: BTreeSet<EdgeRef>,
    }

    let rewrites = input
        .branches
        .iter()
        .enumerate()
        .filter_map(|(branch_index, branch)| {
            let condition = branch
                .condition
                .and_then(|condition| input.conditions.get(condition.index()))?;
            // 只修复 raw local-join 被短路折叠吸进 condition DAG 的候选。边界本来
            // 已落在 condition 外的 branch 由既有 continue evidence 处理，不能重选。
            if !branch
                .branch
                .merge
                .is_some_and(|merge| condition.candidate.blocks.contains(&merge))
            {
                return None;
            }
            let ShortCircuitExit::BranchExit { truthy, falsy } = condition.candidate.exit else {
                return None;
            };
            [(truthy, falsy), (falsy, truthy)]
                .into_iter()
                .enumerate()
                .filter_map(|(orientation, (continue_entry, normal_entry))| {
                    condition_continue_rewrite_for_orientation(
                        proto,
                        cfg,
                        graph_facts,
                        input,
                        loop_index,
                        branch,
                        condition,
                        continue_entry,
                        normal_entry,
                    )
                    .map(|(loop_owner, arm, transfers)| {
                        (
                            (
                                input.loops[loop_owner].candidate.body_scope_blocks.len(),
                                input.loops[loop_owner].candidate.blocks.len(),
                                orientation,
                            ),
                            Rewrite {
                                branch: branch_index,
                                loop_: loop_owner,
                                continue_entry,
                                normal_entry,
                                domain: {
                                    let mut domain = arm;
                                    domain.included_blocks.push(branch.branch.header);
                                    domain
                                },
                                transfers,
                            },
                        )
                    })
                })
                .min_by_key(|(score, _)| *score)
                .map(|(_, rewrite)| rewrite)
        })
        .collect::<Vec<_>>();

    let mut semantic_edges = BTreeSet::new();
    for rewrite in rewrites {
        rewrite_one_arm_branch(
            graph_facts,
            &mut input.branches[rewrite.branch],
            rewrite.continue_entry,
            rewrite.normal_entry,
        );
        if let Some(region) = &mut input.branches[rewrite.branch].region {
            region.replace_domain(rewrite.domain);
        }
        input.loops[rewrite.loop_]
            .candidate
            .continue_edges
            .extend(rewrite.transfers.iter().copied());
        input.loops[rewrite.loop_]
            .semantic_continue_edges
            .extend(rewrite.transfers.iter().copied());
        semantic_edges.extend(rewrite.transfers);
    }
    input
        .residual_transfers
        .retain(|residual| !semantic_edges.contains(&residual.edge));
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn condition_continue_rewrite_for_orientation(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    input: &FinalPlanInput,
    loop_index: &LoopRewriteIndex,
    branch: &super::BranchPlanInput,
    condition: &super::ConditionPlanInput,
    continue_entry: BlockRef,
    normal_entry: BlockRef,
) -> Option<(usize, BranchRegionDomain, BTreeSet<EdgeRef>)> {
    for &owner in loop_index.containing(branch.branch.header) {
        let loop_ = &input.loops[owner];
        let candidate = &loop_.candidate;
        let contains_header = candidate.blocks.contains(&branch.branch.header)
            || candidate.body_scope_blocks.contains(&branch.branch.header);
        let contains_normal = candidate.blocks.contains(&normal_entry)
            || candidate.body_scope_blocks.contains(&normal_entry);
        if contains_header
            && contains_normal
            && candidate.backedges.len() > 1
            && !loop_iteration_escape_entry(proto, cfg, candidate, normal_entry)
            && let Some(arm) = collect_continue_arm_domain(
                proto,
                cfg,
                continue_entry,
                normal_entry,
                owner,
                &input.loops,
                loop_index,
            )
            && !arm.is_empty()
        {
            let transfers = semantic_continue_transfers(
                proto,
                cfg,
                graph_facts,
                condition,
                continue_entry,
                &arm,
                candidate,
            );
            if !transfers.is_empty() {
                return Some((owner, arm, transfers));
            }
        }
    }
    None
}

fn semantic_continue_transfers(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    condition: &super::ConditionPlanInput,
    continue_entry: BlockRef,
    arm: &BranchRegionDomain,
    loop_: &crate::structure::LoopCandidate,
) -> BTreeSet<EdgeRef> {
    let mut transfers = loop_
        .backedges
        .iter()
        .copied()
        .filter(|edge| {
            let Some(edge_data) = cfg.edges.get(edge.index()) else {
                return false;
            };
            arm.contains(graph_facts, edge_data.from)
                && (loop_.continue_edges.contains(edge)
                    || loop_iteration_escape_entry(proto, cfg, loop_, edge_data.to))
        })
        .collect::<BTreeSet<_>>();
    if arm.is_empty() && loop_iteration_escape_entry(proto, cfg, loop_, continue_entry) {
        transfers.extend(condition.arcs.iter().filter_map(|arc| {
            arc.edges.last().copied().filter(|edge| {
                cfg.edges.get(edge.index()).map(|edge| edge.to) == Some(continue_entry)
            })
        }));
    }
    transfers
}

fn loop_break_arm_domain(
    cfg: &Cfg,
    branch: &super::BranchPlanInput,
    loops: &[super::LoopPlanInput],
    loop_index: &LoopRewriteIndex,
) -> Option<BranchRegionDomain> {
    if !matches!(branch.branch.kind, BranchKind::IfThen | BranchKind::Guard)
        || branch.branch.else_entry.is_some()
    {
        return None;
    }
    let merge = branch.branch.merge?;
    for &owner in loop_index.containing(branch.branch.header) {
        let loop_ = &loops[owner];
        let candidate = &loop_.candidate;
        let eligible_header = !candidate.control_blocks.contains(&branch.branch.header)
            && candidate.condition_header != Some(branch.branch.header)
            && (candidate.blocks.contains(&branch.branch.header)
                || candidate.body_scope_blocks.contains(&branch.branch.header));
        if eligible_header
            && let Some(continuation) = loop_.continuation
            && continuation != cfg.exit_block
            && continuation != merge
            && (candidate.exits.contains(&continuation)
                || candidate.exits.contains(&branch.branch.then_entry))
            && (candidate.blocks.contains(&merge) || candidate.body_scope_blocks.contains(&merge))
            && let Some(span) = collect_linear_escape_span(
                cfg,
                branch.branch.then_entry,
                merge,
                continuation,
                candidate,
            )
        {
            return Some(BranchRegionDomain {
                spans: vec![span],
                included_blocks: Vec::new(),
            });
        }
    }
    None
}

fn collect_linear_escape_span(
    cfg: &Cfg,
    start: BlockRef,
    merge: BlockRef,
    target: BlockRef,
    owner: &crate::structure::LoopCandidate,
) -> Option<BranchRegionSpan> {
    let mut current = start;
    let mut visited = BTreeSet::new();
    while current != target {
        if current == merge
            || !visited.insert(current)
            || !owner.blocks.contains(&current) && !owner.body_scope_blocks.contains(&current)
            || current != start
                && cfg.preds[current.index()]
                    .iter()
                    .filter(|edge| cfg.reachable_blocks.contains(&cfg.edges[edge.index()].from))
                    .take(2)
                    .count()
                    > 1
        {
            return None;
        }
        let [edge] = cfg.succs.get(current.index())?.as_slice() else {
            return None;
        };
        current = cfg.edges.get(edge.index())?.to;
    }
    Some(BranchRegionSpan {
        root: start,
        excluded_subtrees: vec![target],
    })
}

fn conditional_continue_loop(
    proto: &LoweredProto,
    cfg: &Cfg,
    branch: &super::BranchPlanInput,
    loops: &[super::LoopPlanInput],
    loop_index: &LoopRewriteIndex,
) -> Option<usize> {
    (branch.branch.kind == BranchKind::Guard).then_some(())?;
    for &owner in loop_index.containing(branch.branch.header) {
        let loop_ = &loops[owner];
        if loop_.candidate.blocks.contains(&branch.branch.header)
            && loop_iteration_escape_entry(proto, cfg, &loop_.candidate, branch.branch.then_entry)
        {
            return Some(owner);
        }
    }
    None
}

fn body_tail_guard_loop(
    proto: &LoweredProto,
    cfg: &Cfg,
    branch: &super::BranchPlanInput,
    loops: &[super::LoopPlanInput],
    loop_index: &LoopRewriteIndex,
) -> Option<usize> {
    (branch.branch.kind == BranchKind::Guard).then_some(())?;
    let tail = branch.branch.merge?;
    let [tail_edge] = cfg.succs[tail.index()].as_slice() else {
        return None;
    };
    (cfg.edges[tail_edge.index()].to == branch.branch.then_entry).then_some(())?;
    for &owner in loop_index.containing(branch.branch.header) {
        let loop_ = &loops[owner];
        if (loop_.candidate.blocks.contains(&branch.branch.header)
            || loop_
                .candidate
                .body_scope_blocks
                .contains(&branch.branch.header))
            && loop_.candidate.continue_target == Some(branch.branch.then_entry)
            && block_has_non_control_prefix(proto, cfg, branch.branch.then_entry)
        {
            return Some(owner);
        }
    }
    None
}

fn native_continue_arm_domain(
    proto: &LoweredProto,
    cfg: &Cfg,
    branch: &super::BranchPlanInput,
    loops: &[super::LoopPlanInput],
    loop_index: &LoopRewriteIndex,
) -> Option<BranchRegionDomain> {
    if !matches!(branch.branch.kind, BranchKind::IfThen | BranchKind::Guard)
        || branch.branch.else_entry.is_some()
    {
        return None;
    }
    let merge = branch.branch.merge?;
    for &owner in loop_index.containing(branch.branch.header) {
        let loop_ = &loops[owner];
        if (loop_.candidate.blocks.contains(&branch.branch.header)
            || loop_
                .candidate
                .body_scope_blocks
                .contains(&branch.branch.header))
            && !loop_iteration_escape_entry(proto, cfg, &loop_.candidate, merge)
            && let Some(domain) = collect_continue_arm_domain(
                proto,
                cfg,
                branch.branch.then_entry,
                merge,
                owner,
                loops,
                loop_index,
            )
        {
            return Some(domain);
        }
    }
    None
}

fn collect_continue_arm_domain(
    proto: &LoweredProto,
    cfg: &Cfg,
    start: BlockRef,
    merge: BlockRef,
    owner_index: usize,
    loops: &[super::LoopPlanInput],
    loop_index: &LoopRewriteIndex,
) -> Option<BranchRegionDomain> {
    let owner = loops.get(owner_index)?;
    let mut current = start;
    let mut visited = BTreeSet::new();
    loop {
        if current == merge || !visited.insert(current) {
            return None;
        }
        if loop_iteration_escape_entry(proto, cfg, &owner.candidate, current) {
            return Some(if current != start {
                BranchRegionDomain::from_span(start, [current])
            } else {
                BranchRegionDomain {
                    spans: Vec::new(),
                    included_blocks: Vec::new(),
                }
            });
        }
        if !owner.candidate.blocks.contains(&current)
            && !owner.candidate.body_scope_blocks.contains(&current)
        {
            return None;
        }
        if current != start
            && cfg.preds[current.index()]
                .iter()
                .filter(|edge| cfg.reachable_blocks.contains(&cfg.edges[edge.index()].from))
                .take(2)
                .count()
                > 1
        {
            return None;
        }

        if let Some((nested, continuation)) = loop_index
            .at_header(current)
            .iter()
            .copied()
            .filter(|nested| {
                *nested != owner_index && loop_index.contains_loop(owner_index, *nested)
            })
            .filter_map(|nested| Some((nested, loops[nested].continuation?)))
            .find(|(_, continuation)| {
                loop_iteration_escape_entry(proto, cfg, &owner.candidate, *continuation)
            })
        {
            let nested = &loops[nested];
            let mut spans = Vec::new();
            if current != start {
                spans.push(BranchRegionSpan {
                    root: start,
                    excluded_subtrees: vec![current],
                });
            }
            let mut excluded_subtrees = nested.candidate.exits.iter().copied().collect::<Vec<_>>();
            excluded_subtrees.push(continuation);
            excluded_subtrees.push(cfg.exit_block);
            excluded_subtrees.sort_unstable();
            excluded_subtrees.dedup();
            spans.push(BranchRegionSpan {
                root: current,
                excluded_subtrees,
            });
            return Some(BranchRegionDomain {
                spans,
                included_blocks: Vec::new(),
            });
        }

        let [edge] = cfg.succs.get(current.index())?.as_slice() else {
            return None;
        };
        let target = cfg.edges.get(edge.index())?.to;
        if owner.candidate.continue_edges.contains(edge)
            || loop_iteration_escape_entry(proto, cfg, &owner.candidate, target)
        {
            return Some(BranchRegionDomain::from_span(start, [target]));
        }
        current = target;
    }
}

fn loop_iteration_escape_entry(
    proto: &LoweredProto,
    cfg: &Cfg,
    candidate: &crate::structure::LoopCandidate,
    entry: BlockRef,
) -> bool {
    let direct_continue = candidate.continue_target == Some(entry)
        && !(matches!(
            candidate.kind_hint,
            crate::structure::LoopKindHint::Unknown
                | crate::structure::LoopKindHint::RepeatLike
                | crate::structure::LoopKindHint::NumericForLike
                | crate::structure::LoopKindHint::WhileTrueLike
        ) && block_has_non_control_prefix(proto, cfg, entry)
            && !control_prefix_is_movable(proto, cfg, entry));
    direct_continue
        || candidate.backedges.iter().any(|edge_ref| {
            cfg.edges.get(edge_ref.index()).is_some_and(|edge| {
                edge.from == entry
                    && edge.to == candidate.header
                    && cfg.blocks[entry.index()].instrs.len == 1
                    && cfg.succs[entry.index()].as_slice() == [*edge_ref]
            })
        })
}

struct PureContinueForwardIndex {
    distance: Vec<Option<usize>>,
    last: Vec<Option<EdgeRef>>,
}

impl PureContinueForwardIndex {
    fn build(
        cfg: &Cfg,
        arena: &RegionArena,
        partition: &LoopPartitions,
        target: BlockRef,
        barriers: &BTreeSet<BlockRef>,
        labels: &BTreeSet<BlockRef>,
    ) -> Result<Self, StructureError> {
        Self::build_filtered(cfg, target, |source, incoming| {
            if !partition.body.contains(&source)
                || barriers.contains(&source)
                || labels.contains(&source)
            {
                return false;
            }
            let Some(owner) = arena.region_by_block[source.index()] else {
                return false;
            };
            !arena.navigation.has_unstructured_ancestor(owner)
                && cfg.blocks[source.index()].instrs.len == 1
                && cfg.succs[source.index()].as_slice() == [incoming]
                && cfg.edges[incoming.index()].kind == EdgeKind::Jump
        })
    }

    fn build_cfg(
        cfg: &Cfg,
        body: &BTreeSet<BlockRef>,
        target: BlockRef,
        barriers: &BTreeSet<BlockRef>,
        labels: &BTreeSet<BlockRef>,
    ) -> Result<Self, StructureError> {
        Self::build_filtered(cfg, target, |source, incoming| {
            body.contains(&source)
                && !barriers.contains(&source)
                && !labels.contains(&source)
                && cfg.blocks[source.index()].instrs.len == 1
                && cfg.succs[source.index()].as_slice() == [incoming]
                && cfg.edges[incoming.index()].kind == EdgeKind::Jump
        })
    }

    fn build_filtered(
        cfg: &Cfg,
        target: BlockRef,
        mut accepts: impl FnMut(BlockRef, EdgeRef) -> bool,
    ) -> Result<Self, StructureError> {
        let mut distance: Vec<Option<usize>> = vec![None; cfg.blocks.len()];
        let mut last = vec![None; cfg.blocks.len()];
        distance[target.index()] = Some(0);
        let mut pending = VecDeque::from([target]);
        while let Some(block) = pending.pop_front() {
            let suffix_len = distance[block.index()].ok_or_else(|| {
                StructureError::invalid("continue forward index lost a discovered block")
            })?;
            for &incoming in &cfg.preds[block.index()] {
                let source = cfg.edges[incoming.index()].from;
                if distance[source.index()].is_some() || !accepts(source, incoming) {
                    continue;
                }
                distance[source.index()] = Some(
                    suffix_len
                        .checked_add(1)
                        .ok_or_else(|| StructureError::invalid("forward route length overflow"))?,
                );
                last[source.index()] = if suffix_len == 0 {
                    Some(incoming)
                } else {
                    last[block.index()]
                };
                pending.push_back(source);
            }
        }
        Ok(Self { distance, last })
    }

    fn route(&self, cfg: &Cfg, entry: EdgeRef) -> Option<FunctionalForwardPath> {
        let start = cfg.edges.get(entry.index())?.to;
        let len = self.distance.get(start.index()).copied().flatten()?;
        if len == 0 {
            return None;
        }
        let [first] = cfg.succs.get(start.index())?.as_slice() else {
            return None;
        };
        Some(FunctionalForwardPath {
            first: *first,
            last: self.last.get(start.index()).copied().flatten()?,
            len,
        })
    }
}

fn repeat_continue_forwarding_route(
    cfg: &Cfg,
    arena: &RegionArena,
    partition: &LoopPartitions,
    candidate: &crate::structure::LoopCandidate,
    condition: BlockRef,
    barriers: &BTreeSet<BlockRef>,
    labels: &BTreeSet<BlockRef>,
) -> Option<Vec<EdgeRef>> {
    let mut loop_edges = cfg.succs[condition.index()]
        .iter()
        .copied()
        .filter(|edge| partition.owned.contains(&cfg.edges[edge.index()].to));
    let loop_edge = loop_edges.next()?;
    if loop_edges.next().is_some() {
        return None;
    }
    let mut route = vec![loop_edge];
    let mut block = cfg.edges[loop_edge.index()].to;
    let mut visited = BTreeSet::new();
    while block != candidate.header {
        if !visited.insert(block)
            || !partition.owned.contains(&block)
            || barriers.contains(&block)
            || labels.contains(&block)
        {
            return None;
        }
        let owner = arena
            .region_by_block
            .get(block.index())
            .copied()
            .flatten()?;
        if arena.navigation.has_unstructured_ancestor(owner) {
            return None;
        }
        let range = cfg.blocks.get(block.index())?.instrs;
        let [edge] = cfg.succs.get(block.index())?.as_slice() else {
            return None;
        };
        let cfg_edge = cfg.edges.get(edge.index())?;
        if range.len != 1 || cfg_edge.kind != EdgeKind::Jump {
            return None;
        }
        route.push(*edge);
        block = cfg_edge.to;
    }
    Some(route)
}

fn direct_continue_latch_route(
    cfg: &Cfg,
    arena: &RegionArena,
    partition: &LoopPartitions,
    header: BlockRef,
    target: BlockRef,
    barriers: &BTreeSet<BlockRef>,
) -> Option<Vec<EdgeRef>> {
    let mut block = target;
    let mut visited = BTreeSet::new();
    let mut route = Vec::new();
    while block != header {
        if !visited.insert(block) || !partition.body.contains(&block) || barriers.contains(&block) {
            return None;
        }
        let owner = arena
            .region_by_block
            .get(block.index())
            .copied()
            .flatten()?;
        if arena.navigation.has_unstructured_ancestor(owner) {
            return None;
        }
        let range = cfg.blocks.get(block.index())?.instrs;
        let [edge] = cfg.succs.get(block.index())?.as_slice() else {
            return None;
        };
        let cfg_edge = cfg.edges.get(edge.index())?;
        if range.len != 1 || cfg_edge.kind != EdgeKind::Jump {
            return None;
        }
        route.push(*edge);
        block = cfg_edge.to;
    }
    (!route.is_empty()).then_some(route)
}

fn continue_edge_bypasses_body(cfg: &Cfg, partition: &LoopPartitions, edge: EdgeRef) -> bool {
    continue_edge_bypasses_body_parts(cfg, &partition.body, edge)
}

fn body_blocks_reaching_target(
    cfg: &Cfg,
    body: &BTreeSet<BlockRef>,
    target: BlockRef,
) -> BTreeSet<BlockRef> {
    let mut reachable = BTreeSet::new();
    let mut pending = vec![target];
    while let Some(block) = pending.pop() {
        for edge in &cfg.preds[block.index()] {
            let source = cfg.edges[edge.index()].from;
            if body.contains(&source) && reachable.insert(source) {
                pending.push(source);
            }
        }
    }
    reachable
}

fn continue_edge_bypasses_body_parts(cfg: &Cfg, body: &BTreeSet<BlockRef>, edge: EdgeRef) -> bool {
    let Some(selected) = cfg.edges.get(edge.index()) else {
        return false;
    };
    let Some(successors) = cfg.succs.get(selected.from.index()) else {
        return false;
    };
    if successors.len() == 2
        && successors.iter().copied().any(|other| {
            other != edge
                && cfg
                    .edges
                    .get(other.index())
                    .is_some_and(|other| other.to != selected.to && body.contains(&other.to))
        })
    {
        return true;
    }
    successors.as_slice() == [edge]
        && cfg.preds[selected.from.index()]
            .iter()
            .copied()
            .any(|incoming| {
                let predecessor = cfg.edges[incoming.index()].from;
                cfg.succs[predecessor.index()].len() == 2
                    && cfg.succs[predecessor.index()]
                        .iter()
                        .copied()
                        .any(|sibling| {
                            sibling != incoming
                                && cfg.edges.get(sibling.index()).is_some_and(|sibling| {
                                    sibling.to != selected.from && body.contains(&sibling.to)
                                })
                        })
            })
}

#[derive(Debug, Clone, Copy, Default)]
pub(super) struct LayoutEdgeFact {
    pub(super) natural: bool,
    pub(super) crosses_island_layout: bool,
}

pub(super) fn layout_edge_facts(
    cfg: &Cfg,
    regions: &[RegionPlan],
    navigation: &RegionNavigation,
) -> Result<Vec<LayoutEdgeFact>, StructureError> {
    let mut sequence_positions = vec![None; regions.len()];
    let mut island_block_positions = vec![None; cfg.blocks.len()];
    let mut island_region_positions = vec![None; regions.len()];
    for (index, region) in regions.iter().enumerate() {
        match region {
            RegionPlan::Sequence { children, .. } => {
                for (position, child) in children.iter().copied().enumerate() {
                    sequence_positions[child.index()] = Some((RegionId(index), position));
                }
            }
            RegionPlan::Unstructured { layout, .. } => {
                for (position, item) in layout.iter().enumerate() {
                    match item {
                        UnstructuredLayoutItem::Block(block) => {
                            island_block_positions[block.index()] =
                                Some((RegionId(index), position));
                        }
                        UnstructuredLayoutItem::Region(region) => {
                            island_region_positions[region.index()] =
                                Some((RegionId(index), position));
                        }
                    }
                }
            }
            RegionPlan::Block { .. }
            | RegionPlan::Branch { .. }
            | RegionPlan::ValueDecision { .. }
            | RegionPlan::Loop { .. } => {}
        }
    }

    Ok(cfg
        .edges
        .iter()
        .enumerate()
        .map(|(edge_index, edge)| {
            let Some(relation) = navigation.edge_relation(EdgeRef(edge_index)) else {
                return LayoutEdgeFact::default();
            };
            let Some(source) = relation.source_owner else {
                return LayoutEdgeFact::default();
            };
            let Some(target) = relation.target_owner else {
                return LayoutEdgeFact::default();
            };
            let Some(owner) = relation.lca else {
                return LayoutEdgeFact::default();
            };
            match &regions[owner.index()] {
                RegionPlan::Sequence { .. } => {
                    let source_owner = source;
                    let Some(source) = relation.source_child else {
                        return LayoutEdgeFact::default();
                    };
                    let Some(target) = relation.target_child else {
                        return LayoutEdgeFact::default();
                    };
                    let natural = sequence_positions[source.index()]
                        .zip(sequence_positions[target.index()])
                        .is_some_and(|((source_parent, source), (target_parent, target))| {
                            source_parent == owner && target_parent == owner && target == source + 1
                        })
                        && navigation.region_can_complete_from(source, source_owner, edge.from);
                    LayoutEdgeFact {
                        natural,
                        crosses_island_layout: matches!(
                            regions.get(source.index()),
                            Some(RegionPlan::Unstructured { .. })
                        ),
                    }
                }
                RegionPlan::Unstructured { .. } => {
                    let source_owner = source;
                    let source_region = if source_owner == owner {
                        None
                    } else {
                        relation.source_child
                    };
                    let source = if source_owner == owner {
                        island_block_positions[edge.from.index()]
                            .filter(|(island, _)| *island == owner)
                            .map(|(_, position)| position)
                    } else {
                        source_region.and_then(|region| {
                            island_region_positions[region.index()]
                                .filter(|(island, _)| *island == owner)
                                .map(|(_, position)| position)
                        })
                    };
                    let target = if target == owner {
                        island_block_positions[edge.to.index()]
                            .filter(|(island, _)| *island == owner)
                            .map(|(_, position)| position)
                    } else {
                        relation.target_child.and_then(|region| {
                            island_region_positions[region.index()]
                                .filter(|(island, _)| *island == owner)
                                .map(|(_, position)| position)
                        })
                    };
                    let crosses_island_layout = source
                        .zip(target)
                        .is_some_and(|(source, target)| source != target);
                    let natural = source
                        .zip(target)
                        .is_some_and(|(source, target)| target == source + 1)
                        && source_region.is_none_or(|region| {
                            navigation.region_can_complete_from(region, source_owner, edge.from)
                        });
                    LayoutEdgeFact {
                        natural,
                        crosses_island_layout,
                    }
                }
                RegionPlan::Block { .. }
                | RegionPlan::Branch { .. }
                | RegionPlan::ValueDecision { .. }
                | RegionPlan::Loop { .. } => LayoutEdgeFact::default(),
            }
        })
        .collect())
}

fn freeze_labels(
    cfg: &Cfg,
    arena: &RegionArena,
    edge_plans: &mut [EdgePlan],
    tbc_flow: &crate::structure::scope::TbcFlowFacts,
) -> Result<(Vec<LabelPlan>, Vec<Option<LabelPlanId>>), StructureError> {
    let label_region_by_block = label_regions_by_entry(
        cfg,
        &arena.regions,
        &arena.navigation,
        &arena.single_passes,
        &arena.single_pass_by_region,
    )?;
    let mut targets = BTreeMap::<BlockRef, LabelPlacement>::new();
    for edge_plan in edge_plans.iter() {
        let EdgeTransfer::Goto(label, _) = edge_plan.transfer else {
            continue;
        };
        // classify 阶段临时以 block index 承载尚未冻结的 label identity。
        let block = BlockRef(label.index());
        record_label_target(
            &mut targets,
            block,
            label_placement_for_edge(cfg, &label_region_by_block, edge_plan.edge, block)?,
        )?;
    }
    let multi_entry_prefix = arena.navigation.multi_entry_island_prefix(&arena.regions);
    for (index, edge) in cfg.edges.iter().enumerate() {
        if arena
            .navigation
            .edge_enters_prefixed_region(EdgeRef(index), &multi_entry_prefix)
        {
            record_label_target(
                &mut targets,
                edge.to,
                label_placement_for_edge(cfg, &label_region_by_block, EdgeRef(index), edge.to)?,
            )?;
        }
    }

    let mut labels = Vec::with_capacity(targets.len());
    let mut label_by_block = vec![None; cfg.blocks.len()];
    for block in cfg.block_order.iter().copied() {
        let Some(placement) = targets.remove(&block) else {
            continue;
        };
        let id = LabelPlanId(labels.len());
        label_by_block[block.index()] = Some(id);
        labels.push(LabelPlan {
            block,
            tbc_barriers: tbc_flow
                .active_at_entry(block)
                .ok_or_else(|| StructureError::invalid("label block has no TBC entry facts"))?
                .iter()
                .copied()
                .collect(),
            placement,
        });
    }
    if !targets.is_empty() {
        return Err(StructureError::invalid(
            "planned label target is absent from stable block order",
        ));
    }

    for edge_plan in edge_plans {
        let EdgeTransfer::Goto(pending, reason) = edge_plan.transfer else {
            continue;
        };
        let target = BlockRef(pending.index());
        let label = label_by_block
            .get(target.index())
            .copied()
            .flatten()
            .ok_or_else(|| StructureError::invalid("goto target has no frozen label"))?;
        edge_plan.transfer = EdgeTransfer::Goto(label, reason);
    }

    Ok((labels, label_by_block))
}

fn record_label_target(
    targets: &mut BTreeMap<BlockRef, LabelPlacement>,
    block: BlockRef,
    placement: LabelPlacement,
) -> Result<(), StructureError> {
    if let Some(existing) = targets.insert(block, placement)
        && existing != placement
    {
        return Err(StructureError::invalid(format!(
            "label target {block} requires conflicting placements {existing:?} and {placement:?}"
        )));
    }
    Ok(())
}

fn label_placement_for_edge(
    cfg: &Cfg,
    label_region_by_block: &[Option<RegionId>],
    edge: EdgeRef,
    target: BlockRef,
) -> Result<LabelPlacement, StructureError> {
    if cfg.edges.get(edge.index()).map(|edge| edge.to) != Some(target) {
        return Err(StructureError::invalid(format!(
            "label edge {edge} does not enter target {target}"
        )));
    }
    Ok(label_region_by_block
        .get(target.index())
        .copied()
        .flatten()
        .map_or(LabelPlacement::BeforeBlock, LabelPlacement::BeforeRegion))
}

/// 同一 CFG target 只能对应一个源码 label，所以 placement 也必须按 target 冻结。
/// 若多个嵌套 region 共享入口，选择最外层会生成源码控制壳的 region；从其内部或
/// 外部进入该 block 都会先执行同一份 region 语义，且 label 不会被藏进 `if`、loop
/// 或 single-pass `repeat` 的更深词法块。
fn label_regions_by_entry(
    cfg: &Cfg,
    regions: &[RegionPlan],
    navigation: &RegionNavigation,
    single_passes: &[super::SinglePassPlan],
    single_pass_by_region: &[Option<super::SinglePassPlanId>],
) -> Result<Vec<Option<RegionId>>, StructureError> {
    let mut by_block = vec![None; cfg.blocks.len()];
    for (index, node) in regions.iter().enumerate() {
        let region = RegionId(index);
        let entry = match node {
            RegionPlan::Branch { entry, .. }
            | RegionPlan::ValueDecision { entry, .. }
            | RegionPlan::Loop { entry, .. } => *entry,
            RegionPlan::Sequence { .. } => {
                let Some(id) = single_pass_by_region.get(index).copied().flatten() else {
                    continue;
                };
                single_passes
                    .get(id.index())
                    .ok_or_else(|| {
                        StructureError::invalid(
                            "single-pass label placement references a missing payload",
                        )
                    })?
                    .entry
            }
            // island layout 直接内联到父层，不会生成独立的源码词法壳；把它当
            // `BeforeRegion` 会把入口 label 错移到 layout 首项之前。
            RegionPlan::Block { .. } | RegionPlan::Unstructured { .. } => continue,
        };
        let slot = by_block.get_mut(entry.index()).ok_or_else(|| {
            StructureError::invalid("structured label entry is outside the CFG arena")
        })?;
        match *slot {
            None => *slot = Some(region),
            Some(outer) if navigation.contains(outer, region) => {}
            Some(inner) if navigation.contains(region, inner) => *slot = Some(region),
            Some(other) => {
                return Err(StructureError::invalid(format!(
                    "block {entry} is the entry of incomparable structured regions #{} and #{}",
                    other.index(),
                    region.index()
                )));
            }
        }
    }
    Ok(by_block)
}

fn build_requirements(
    cfg: &Cfg,
    caps: ControlFlowCaps,
    arena: &RegionArena,
    edge_plans: &[EdgePlan],
) -> Result<PlanRequirements, StructureError> {
    let mut entries = Vec::new();
    let mut by_edge = vec![Vec::new(); cfg.edges.len()];
    let mut required_features = BTreeSet::new();
    let mut unavailable_features = BTreeSet::new();

    for edge_plan in edge_plans.iter() {
        let requirement = match edge_plan.transfer {
            EdgeTransfer::Goto(label, reason) => {
                required_features.insert(ControlFlowFeature::GotoLabel);
                if !caps.goto_label {
                    unavailable_features.insert(ControlFlowFeature::GotoLabel);
                }
                Some(PlanRequirement::Goto {
                    edge: edge_plan.edge,
                    label,
                    reason,
                })
            }
            EdgeTransfer::Continue(loop_region) => {
                required_features.insert(ControlFlowFeature::ContinueStatement);
                if !caps.continue_stmt {
                    unavailable_features.insert(ControlFlowFeature::ContinueStatement);
                }
                Some(PlanRequirement::Continue {
                    edge: edge_plan.edge,
                    loop_region,
                })
            }
            EdgeTransfer::Unreachable
            | EdgeTransfer::Fallthrough
            | EdgeTransfer::BranchArm(_)
            | EdgeTransfer::LoopBack(_)
            | EdgeTransfer::Break(_)
            | EdgeTransfer::Return
            | EdgeTransfer::TailCall => None,
        };
        if let Some(requirement) = requirement {
            let id = PlanRequirementId(entries.len());
            entries.push(requirement);
            by_edge[edge_plan.edge.index()].push(id);
        }
    }
    for (index, spec) in arena.specs.iter().enumerate() {
        if !matches!(
            spec.kind,
            ContainerKind::Island(_) | ContainerKind::Residual(_)
        ) {
            continue;
        }
        let region = arena.slots[index].region();
        let entry_count = match &arena.regions[region.index()] {
            RegionPlan::Unstructured { entries, .. } => entries.len(),
            _ => return Err(StructureError::invalid("island slot is not unstructured")),
        };
        if entry_count > 1 {
            required_features.insert(ControlFlowFeature::GotoLabel);
            if !caps.goto_label {
                unavailable_features.insert(ControlFlowFeature::GotoLabel);
            }
            entries.push(PlanRequirement::MultiEntryIsland {
                region,
                entry_count,
            });
        }
    }

    Ok(PlanRequirements {
        entries,
        by_edge,
        unresolved_by_block: vec![false; cfg.blocks.len()],
        required_features,
        unavailable_features,
        caps,
    })
}

fn canonicalize_loops(
    cfg: &Cfg,
    mut loops: Vec<super::LoopPlanInput>,
) -> (Vec<super::LoopPlanInput>, Vec<super::UnstructuredPlanData>) {
    for loop_ in &mut loops {
        normalize_break_only_while_body(cfg, loop_);
    }
    let mut by_header = BTreeMap::<BlockRef, Vec<super::LoopPlanInput>>::new();
    for loop_ in loops {
        by_header
            .entry(loop_.candidate.header)
            .or_default()
            .push(loop_);
    }

    let mut selected_loops = Vec::new();
    let mut residuals = Vec::new();
    for candidates in by_header.into_values() {
        let distinct_blocks = candidates
            .iter()
            .map(|candidate| &candidate.candidate.blocks)
            .collect::<BTreeSet<_>>();
        let mut block_sets = distinct_blocks.iter().copied().collect::<Vec<_>>();
        block_sets.sort_by_key(|blocks| blocks.len());
        // 同 header 的候选若构成包含链，按大小排序后只需检查相邻集合；传递性保证
        // 其余任意两项也嵌套，避免候选较多时做全对集合比较。
        let nested_chain = block_sets.windows(2).all(|pair| pair[0].is_subset(pair[1]));
        let candidate_groups = if block_sets.len() > 1 && nested_chain {
            let mut by_blocks = BTreeMap::<BTreeSet<BlockRef>, Vec<_>>::new();
            for candidate in candidates {
                by_blocks
                    .entry(candidate.candidate.blocks.clone())
                    .or_default()
                    .push(candidate);
            }
            by_blocks.into_values().collect::<Vec<_>>()
        } else {
            vec![candidates]
        };

        for mut candidates in candidate_groups {
            let kinds = candidates
                .iter()
                .map(|candidate| candidate.candidate.kind_hint)
                .filter(|kind| *kind != crate::structure::LoopKindHint::Unknown)
                .collect::<BTreeSet<_>>();
            let mut bindings = Vec::new();
            for binding in candidates
                .iter()
                .filter_map(|candidate| candidate.candidate.source_bindings)
            {
                if !bindings.contains(&binding) {
                    bindings.push(binding);
                }
            }
            let conditions = candidates
                .iter()
                .filter_map(|candidate| candidate.condition)
                .collect::<BTreeSet<_>>();
            if kinds.len() > 1 || bindings.len() > 1 || conditions.len() > 1 {
                let Some(first) = candidates.first() else {
                    continue;
                };
                let header = first.candidate.header;
                let mut blocks = BTreeSet::from([header]);
                let mut exits = BTreeSet::new();
                for candidate in candidates {
                    blocks.extend(candidate.candidate.blocks);
                    blocks.extend(candidate.candidate.body_scope_blocks);
                    blocks.extend(candidate.candidate.control_blocks);
                    exits.extend(candidate.candidate.exits);
                }
                residuals.push(super::UnstructuredPlanData {
                    fact: crate::structure::RegionFact {
                        blocks,
                        entry: header,
                        exits,
                    },
                    layout: None,
                });
                continue;
            }
            let selected = candidates
                .iter()
                .enumerate()
                .max_by_key(|(index, candidate)| {
                    (
                        candidate.candidate.source_bindings.is_some(),
                        candidate.candidate.kind_hint != crate::structure::LoopKindHint::Unknown,
                        candidate.candidate.blocks.len(),
                        Reverse(*index),
                    )
                })
                .map(|(index, _)| index);
            let Some(selected) = selected else {
                continue;
            };
            let mut selected = candidates.swap_remove(selected);
            for candidate in candidates {
                selected
                    .candidate
                    .blocks
                    .extend(candidate.candidate.blocks.iter().copied());
                selected
                    .candidate
                    .body_scope_blocks
                    .extend(candidate.candidate.body_scope_blocks.iter().copied());
                selected
                    .candidate
                    .control_blocks
                    .extend(candidate.candidate.control_blocks.iter().copied());
                selected
                    .candidate
                    .normalized_exit_aliases
                    .extend(candidate.candidate.normalized_exit_aliases);
                selected.candidate.exits.extend(candidate.candidate.exits);
                selected
                    .candidate
                    .continue_edges
                    .extend(candidate.candidate.continue_edges);
                selected
                    .semantic_continue_edges
                    .extend(candidate.semantic_continue_edges);
                extend_edges(
                    &mut selected.candidate.backedges,
                    candidate.candidate.backedges,
                );
                extend_value_merges(
                    &mut selected.candidate.header_value_merges,
                    candidate.candidate.header_value_merges,
                );
                for exit_merge in candidate.candidate.exit_value_merges {
                    if let Some(existing) = selected
                        .candidate
                        .exit_value_merges
                        .iter_mut()
                        .find(|existing| existing.exit == exit_merge.exit)
                    {
                        extend_value_merges(&mut existing.values, exit_merge.values);
                    } else {
                        selected.candidate.exit_value_merges.push(exit_merge);
                    }
                }
                extend_value_merges(&mut selected.carried_values, candidate.carried_values);
                if selected.condition.is_none() {
                    selected.condition = candidate.condition;
                }
                if selected.continuation != candidate.continuation {
                    selected.continuation = None;
                }
            }
            selected
                .candidate
                .backedges
                .sort_by_key(|edge| edge.index());
            selected.candidate.normalized_exit_aliases.sort();
            selected.candidate.normalized_exit_aliases.dedup();
            selected_loops.push(selected);
        }
    }
    (selected_loops, residuals)
}

fn normalize_break_only_while_body(cfg: &Cfg, loop_: &mut super::LoopPlanInput) {
    use crate::structure::LoopKindHint;

    let candidate = &loop_.candidate;
    if candidate.kind_hint != LoopKindHint::WhileLike
        || candidate.body_scope_blocks.is_subset(&candidate.blocks)
    {
        return;
    }
    let Some(continuation) = loop_.continuation else {
        return;
    };
    let mut lexical = reachable_nonempty_blocks(cfg, candidate.body_scope_blocks.clone());
    lexical.insert(candidate.header);
    lexical.remove(&continuation);
    let Some((truthy, falsy)) = cfg.branch_edges(candidate.header) else {
        return;
    };
    if ![truthy, falsy]
        .into_iter()
        .map(|edge| cfg.edges[edge.index()].to)
        .all(|target| lexical.contains(&target))
        || !candidate.blocks.is_subset(&lexical)
        || !single_entry(cfg, &lexical, candidate.header)
    {
        return;
    }
    let mut has_break = false;
    for block in &lexical {
        for edge in &cfg.succs[block.index()] {
            let target = cfg.edges[edge.index()].to;
            if lexical.contains(&target) {
                continue;
            }
            if target == continuation {
                has_break = true;
            } else if target != cfg.exit_block {
                return;
            }
        }
    }
    if !has_break {
        return;
    }

    let candidate = &mut loop_.candidate;
    candidate.kind_hint = LoopKindHint::WhileTrueLike;
    candidate.condition_header = None;
    candidate.blocks = lexical.clone();
    candidate.body_scope_blocks = lexical;
    candidate.exits = candidate
        .blocks
        .iter()
        .flat_map(|block| cfg.succs[block.index()].iter().copied())
        .map(|edge| cfg.edges[edge.index()].to)
        .filter(|target| !candidate.blocks.contains(target))
        .collect();
    loop_.condition = None;
}

fn extend_edges(target: &mut Vec<EdgeRef>, source: Vec<EdgeRef>) {
    let mut merged = std::mem::take(target).into_iter().collect::<BTreeSet<_>>();
    merged.extend(source);
    target.extend(merged);
}

fn extend_value_merges(
    target: &mut Vec<crate::structure::LoopValueMerge>,
    source: Vec<crate::structure::LoopValueMerge>,
) {
    let mut by_value = target
        .iter()
        .enumerate()
        .map(|(index, merge)| ((merge.phi_id, merge.reg), index))
        .collect::<BTreeMap<_, _>>();
    for merge in source {
        if let Some(index) = by_value.get(&(merge.phi_id, merge.reg)).copied() {
            let existing = &mut target[index];
            extend_value_incomings(
                &mut existing.inside_arm.incomings,
                merge.inside_arm.incomings,
            );
            extend_value_incomings(
                &mut existing.outside_arm.incomings,
                merge.outside_arm.incomings,
            );
        } else {
            by_value.insert((merge.phi_id, merge.reg), target.len());
            target.push(merge);
        }
    }
}

fn extend_value_incomings(
    target: &mut Vec<crate::structure::LoopValueIncoming>,
    source: Vec<crate::structure::LoopValueIncoming>,
) {
    let mut known = target
        .iter()
        .map(|incoming| (incoming.pred, incoming.value))
        .collect::<BTreeSet<_>>();
    for incoming in source {
        if known.insert((incoming.pred, incoming.value)) {
            target.push(incoming);
        }
    }
}

struct SelectedPayloads {
    branches: Vec<super::BranchPlanData>,
    loops: Vec<super::LoopPlanData>,
    loop_regions: Vec<RegionId>,
    conditions: Vec<super::ConditionPlan>,
    condition_map: Vec<Option<super::ConditionPlanId>>,
    value_decisions: Vec<super::ValueDecisionPlan>,
    value_decision_regions: Vec<RegionId>,
}

struct LoopExitTailIndex {
    by_block: Vec<Option<super::LoopPlanId>>,
    by_edge: Vec<Option<super::LoopPlanId>>,
    by_cleanup_instr: Vec<Option<super::LoopPlanId>>,
}

fn index_loop_exit_tails(
    cfg: &Cfg,
    loops: &[super::LoopPlanData],
) -> Result<LoopExitTailIndex, StructureError> {
    let mut by_block = vec![None; cfg.blocks.len()];
    let mut by_edge = vec![None; cfg.edges.len()];
    let mut by_cleanup_instr = vec![None; cfg.instr_to_block.len()];
    for (index, loop_) in loops.iter().enumerate() {
        let Some(tail) = &loop_.exit_tail else {
            continue;
        };
        let id = super::LoopPlanId(index);
        let block_slot = by_block.get_mut(tail.block.index()).ok_or_else(|| {
            StructureError::invalid("loop exit tail references a missing execution block")
        })?;
        if block_slot.replace(id).is_some() {
            return Err(StructureError::invalid(
                "one block is shared by multiple loop exit tails",
            ));
        }
        let edge_slot = by_edge.get_mut(tail.normal_exit.index()).ok_or_else(|| {
            StructureError::invalid("loop exit tail references a missing normal edge")
        })?;
        if edge_slot.replace(id).is_some() {
            return Err(StructureError::invalid(
                "one edge is shared by multiple loop exit tails",
            ));
        }
        for instr in &tail.cleanup {
            let cleanup_slot = by_cleanup_instr.get_mut(instr.index()).ok_or_else(|| {
                StructureError::invalid("loop exit tail cleanup is outside the instruction arena")
            })?;
            if cleanup_slot.replace(id).is_some() {
                return Err(StructureError::invalid(
                    "one cleanup instruction is shared by multiple loop exit tails",
                ));
            }
        }
    }
    Ok(LoopExitTailIndex {
        by_block,
        by_edge,
        by_cleanup_instr,
    })
}

fn build_loop_partitions(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    caps: ControlFlowCaps,
    input: &FinalPlanInput,
) -> Result<Vec<LoopPartitions>, StructureError> {
    let forwarding_barriers = input
        .scopes
        .iter()
        .flat_map(|scope| {
            scope
                .exit
                .into_iter()
                .chain(std::iter::once(scope.entry))
                .chain(
                    scope
                        .close_points
                        .iter()
                        .filter_map(|close| cfg.instr_to_block.get(close.index()).copied()),
                )
        })
        .collect();
    let label_targets = input
        .residual_transfers
        .iter()
        .filter_map(|residual| cfg.edges.get(residual.edge.index()))
        .map(|edge| edge.to)
        .collect();
    let mut branch_merge_by_header = vec![None; cfg.blocks.len()];
    for branch in &input.branches {
        branch_merge_by_header[branch.branch.header.index()] = branch.branch.merge;
    }
    let mut reachable_by_block = vec![false; cfg.blocks.len()];
    for &block in &cfg.reachable_blocks {
        let slot = reachable_by_block.get_mut(block.index()).ok_or_else(|| {
            StructureError::invalid("reachable block is outside the CFG block arena")
        })?;
        *slot = true;
    }
    let mut unstructured_by_block = vec![false; cfg.blocks.len()];
    for island in &input.unstructured {
        let blocks = island
            .layout
            .as_ref()
            .map_or(&island.fact.blocks, |layout| &layout.blocks);
        for &block in blocks {
            let slot = unstructured_by_block
                .get_mut(block.index())
                .ok_or_else(|| {
                    StructureError::invalid("unstructured block is outside the CFG block arena")
                })?;
            *slot = true;
        }
    }
    let mut residual_incidents_by_block = vec![Vec::new(); cfg.blocks.len()];
    for residual in &input.residual_transfers {
        let edge = cfg.edges.get(residual.edge.index()).ok_or_else(|| {
            StructureError::invalid("residual transfer is outside the CFG edge arena")
        })?;
        residual_incidents_by_block[edge.from.index()].push(residual.edge);
        if edge.to != edge.from {
            residual_incidents_by_block[edge.to.index()].push(residual.edge);
        }
    }
    let context = LoopPartitionContext {
        forwarding_barriers,
        label_targets,
        branch_merge_by_header,
        reachable_by_block,
        unstructured_by_block,
        residual_incidents_by_block,
    };
    let inputs = LoopPartitionInputs {
        proto,
        cfg,
        graph_facts,
        caps,
        input,
    };
    let mut workspaces = LoopPartitionWorkspaces {
        exit_pad: LoopExitPadWorkspace::new(cfg.blocks.len()),
        while_break: WhileBreakArmWorkspace::new(cfg.blocks.len(), cfg.edges.len()),
    };
    let mut partitions = Vec::with_capacity(input.loops.len());
    for (index, loop_) in input.loops.iter().enumerate() {
        partitions.push(build_loop_partition(
            &inputs,
            &context,
            &mut workspaces,
            index,
            loop_,
        )?);
    }
    Ok(partitions)
}

fn build_loop_partition(
    inputs: &LoopPartitionInputs<'_>,
    context: &LoopPartitionContext,
    workspaces: &mut LoopPartitionWorkspaces,
    index: usize,
    loop_: &super::LoopPlanInput,
) -> Result<LoopPartitions, StructureError> {
    use crate::structure::LoopKindHint;

    let proto = inputs.proto;
    let cfg = inputs.cfg;
    let graph_facts = inputs.graph_facts;
    let caps = inputs.caps;
    let input = inputs.input;
    let candidate = &loop_.candidate;
    let preheader = matches!(
        candidate.kind_hint,
        LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
    )
    .then_some(candidate.preheader)
    .flatten();
    let condition_blocks = loop_
        .condition
        .map(|id| {
            input
                .conditions
                .get(id.index())
                .map(|condition| condition.candidate.blocks.clone())
                .ok_or_else(|| {
                    StructureError::invalid(format!(
                        "loop #{index} references missing condition #{}",
                        id.index()
                    ))
                })
        })
        .transpose()?;
    let condition_entry = loop_
        .condition
        .and_then(|id| input.conditions.get(id.index()))
        .map(|condition| condition.candidate.header)
        .or(candidate.condition_header)
        .or_else(|| {
            (candidate.kind_hint == LoopKindHint::RepeatLike)
                .then_some(candidate.continue_target)
                .flatten()
        })
        .unwrap_or(candidate.header);
    let repeat_condition_exit = loop_
        .condition
        .and_then(|id| input.conditions.get(id.index()))
        .and_then(|condition| match condition.candidate.exit {
            ShortCircuitExit::BranchExit { truthy, falsy }
                if candidate.kind_hint == LoopKindHint::RepeatLike =>
            {
                match (truthy == candidate.header, falsy == candidate.header) {
                    (true, false) => Some(falsy),
                    (false, true) => Some(truthy),
                    _ => None,
                }
            }
            _ => None,
        });
    let repeat_prefix_is_movable = control_prefix_is_movable(proto, cfg, condition_entry);

    let has_vm_for_edges = |block: BlockRef| {
        let mut has_body = false;
        let mut has_exit = false;
        for edge in &cfg.succs[block.index()] {
            match cfg.edges[edge.index()].kind {
                EdgeKind::LoopBody => has_body = true,
                EdgeKind::LoopExit => has_exit = true,
                _ => {}
            }
        }
        has_body && has_exit
    };
    let vm_for_control = match candidate.kind_hint {
        LoopKindHint::NumericForLike => candidate.continue_target.into_iter(),
        LoopKindHint::GenericForLike => Some(candidate.header).into_iter(),
        _ => None.into_iter(),
    }
    .filter(|block| Some(*block) != preheader)
    .filter(|block| cfg.reachable_blocks.contains(block))
    .filter(|block| has_vm_for_edges(*block))
    .collect::<BTreeSet<_>>();
    let preheader_is_vm_control = preheader.is_some_and(has_vm_for_edges);

    let mut owned = candidate.blocks.clone();
    owned.extend(candidate.control_blocks.iter().copied());
    owned.insert(candidate.header);
    if let Some(blocks) = &condition_blocks {
        owned.extend(blocks.iter().copied());
    }
    if let Some(preheader) = preheader {
        owned.insert(preheader);
    }
    match candidate.kind_hint {
        LoopKindHint::RepeatLike => {
            // natural core 不包含只经 return/break 离开的 body arm；loops pass 已用
            // 支配与真实 LoopExit 边界冻结 lexical body scope。所有带明确 VM/尾条件
            // 边界的 repeat 必须保留该证据。
            owned.extend(candidate.body_scope_blocks.iter().copied());
            // repeat 的词法 body 扩张可以包含条件成功后进入的共享尾块；完整条件 DAG
            // 已把唯一回边出口规范化到 header，因此另一语义出口必须留在 loop 外。
            if let Some(exit) = repeat_condition_exit {
                owned.remove(&exit);
            }
        }
        LoopKindHint::NumericForLike | LoopKindHint::GenericForLike if !caps.goto_label => {
            // 无 goto 目标不能把首轮 body prefix 或 terminal arm 留成跨 loop 跳转；
            // goto-capable 目标则保留 mixed island，避免把不可规约 for 网格强压进树。
            owned.extend(candidate.body_scope_blocks.iter().copied());
        }
        LoopKindHint::WhileLike => {
            let natural = merged_natural_loop_domain(cfg, candidate);
            owned.retain(|block| natural.contains(block) || Some(*block) == preheader);
            owned.insert(candidate.header);
            let lexical_continuation = loop_.continuation.or_else(|| {
                let mut exits = condition_blocks
                    .as_ref()
                    .into_iter()
                    .flat_map(|blocks| blocks.iter().copied())
                    .chain(candidate.condition_header)
                    .chain(std::iter::once(candidate.header))
                    .flat_map(|block| cfg.succs[block.index()].iter().copied())
                    .map(|edge| cfg.edges[edge.index()].to)
                    .filter(|target| !natural.contains(target) && *target != cfg.exit_block)
                    .collect::<BTreeSet<_>>();
                (exits.len() == 1).then(|| exits.pop_first()).flatten()
            });
            let break_arms = verified_while_break_arms(
                cfg,
                graph_facts,
                context,
                WhileBreakArmDomain {
                    candidate,
                    natural: &natural,
                    condition_blocks: condition_blocks.as_ref(),
                    continuation: lexical_continuation,
                },
                &mut workspaces.while_break,
            )?;
            owned.extend(break_arms);
        }
        LoopKindHint::Unknown => {
            let terminal_condition_arm = loop_
                .condition
                .and_then(|id| input.conditions.get(id.index()))
                .and_then(|condition| match condition.candidate.exit {
                    ShortCircuitExit::BranchExit { truthy, falsy } => {
                        match (owned.contains(&truthy), owned.contains(&falsy)) {
                            (true, false) => Some(falsy),
                            (false, true) => Some(truthy),
                            (true, true) | (false, false) => None,
                        }
                    }
                    ShortCircuitExit::ValueMerge(_) => None,
                })
                .filter(|terminal| {
                    candidate.exits.contains(terminal)
                        && candidate
                            .exits
                            .iter()
                            .any(|exit| exit != terminal && *exit != cfg.exit_block)
                })
                .and_then(|terminal| closed_linear_terminal_arm(proto, cfg, terminal, &owned));
            if let Some(terminal) = terminal_condition_arm {
                // terminal arm 是 loop 内的早退，不是词法 continuation。把这个唯一入口
                // 的线性 return 链收进 body 后，Unknown loop 可稳定冻结为 `while true`
                // 加 guard，真正的 break 目标仍是唯一的非终止出口。
                owned.extend(terminal);
            }
        }
        _ => {}
    }
    if let Some(continuation) = loop_.continuation {
        // lexical body evidence 可能包含所有 break arm 汇入的共享 merge，Lua 5.5
        // 的 Close pad 尤其常见；但已声明 continuation 按合同一定在 loop 外，
        // 继续持有它只会制造虚假的多入口 loop。
        owned.remove(&continuation);
    }
    owned = reachable_nonempty_blocks(cfg, owned);
    let complete_unknown_condition = loop_
        .condition
        .and_then(|id| input.conditions.get(id.index()))
        .is_some_and(|condition| {
            let crate::structure::ShortCircuitExit::BranchExit { truthy, falsy } =
                condition.candidate.exit
            else {
                return false;
            };
            let is_body = |target| owned.contains(&target) && Some(target) != preheader;
            is_body(truthy) != is_body(falsy)
        });

    let mut control = match candidate.kind_hint {
        LoopKindHint::WhileLike => condition_blocks.unwrap_or_else(|| {
            BTreeSet::from([candidate.condition_header.unwrap_or(candidate.header)])
        }),
        LoopKindHint::RepeatLike => {
            if let Some(blocks) = condition_blocks {
                blocks
            } else {
                let loop_domain = owned
                    .iter()
                    .copied()
                    .filter(|block| Some(*block) != preheader)
                    .collect::<BTreeSet<_>>();
                let mut latches = BTreeSet::new();
                let mut frontier = candidate
                    .backedges
                    .iter()
                    .filter_map(|edge| cfg.edges.get(edge.index()))
                    .filter(|edge| edge.to == candidate.header)
                    .map(|edge| edge.from)
                    .collect::<BTreeSet<_>>();
                let mut visited = frontier.clone();
                while !frontier.is_empty() {
                    latches.extend(frontier.iter().copied().filter(|source| {
                        cfg.succs[source.index()].iter().any(|edge| {
                            let edge = cfg.edges[edge.index()];
                            edge.kind == EdgeKind::LoopExit || !loop_domain.contains(&edge.to)
                        })
                    }));
                    if !latches.is_empty() {
                        break;
                    }
                    let mut predecessors = BTreeSet::new();
                    for block in &frontier {
                        predecessors.extend(cfg.preds[block.index()].iter().filter_map(|edge| {
                            let source = cfg.edges[edge.index()].from;
                            (loop_domain.contains(&source) && visited.insert(source))
                                .then_some(source)
                        }));
                    }
                    frontier = predecessors;
                }
                if latches.is_empty() {
                    return Err(StructureError::invalid(format!(
                        "repeat loop #{index} has no condition latch on a backedge path to {}",
                        candidate.header
                    )));
                }
                latches
            }
        }
        LoopKindHint::NumericForLike | LoopKindHint::GenericForLike => {
            if vm_for_control.is_empty() && !preheader_is_vm_control {
                return Err(StructureError::invalid(format!(
                    "{:?} loop #{index} has no VM control block with LoopBody and LoopExit edges",
                    candidate.kind_hint
                )));
            }
            vm_for_control
        }
        LoopKindHint::WhileTrueLike => BTreeSet::new(),
        // Unknown 只在已经选出 loop condition 时冻结 control；没有条件证据时仍以
        // `while true` 降低，避免把普通 body branch 猜成源码 loop 条件。
        LoopKindHint::Unknown => condition_blocks
            .filter(|_| complete_unknown_condition)
            .unwrap_or_default(),
    };
    control = reachable_nonempty_blocks(cfg, control);
    if let Some(preheader) = preheader {
        control.remove(&preheader);
    }
    let exit_pads = verified_loop_exit_pads(
        cfg,
        candidate,
        loop_.continuation,
        &owned,
        &control,
        &mut workspaces.exit_pad,
    )?;
    owned.extend(exit_pads);
    if matches!(
        candidate.kind_hint,
        LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
    ) {
        control.extend(for_latch_exit_control_pads(proto, cfg, &control, &owned));
        control.extend(
            candidate
                .normalized_exit_aliases
                .iter()
                .map(|alias| alias.block),
        );
    }
    owned.extend(control.iter().copied());
    if matches!(
        candidate.kind_hint,
        LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
    ) && let Some(preheader) = preheader
    {
        for edge in &cfg.succs[preheader.index()] {
            let edge = cfg.edges[edge.index()];
            if edge.kind == EdgeKind::LoopExit {
                owned.remove(&edge.to);
            }
        }
    }
    let body = owned
        .iter()
        .copied()
        .filter(|block| Some(*block) != preheader && !control.contains(block))
        .collect::<BTreeSet<_>>();
    let is_own_branch_continuation = |edge: EdgeRef| {
        let edge = cfg.edges[edge.index()];
        context.branch_merge_by_header[edge.from.index()] == Some(edge.to)
    };
    let mut continues = candidate.continue_edges.clone();
    continues.extend(loop_.semantic_continue_edges.iter().copied());
    // branch continuation 只描述 containment 边界；带语句的 continue 也可能恰好是
    // natural backedge，只有 partition 证明它跳过同级 body tail 时才保留显式语义。
    continues.retain(|edge| {
        let source = cfg.edges[edge.index()].from;
        let proven_body_bypass =
            caps.continue_stmt && continue_edge_bypasses_body_parts(cfg, &body, *edge);
        !matches!(
            cfg.edges[edge.index()].kind,
            EdgeKind::Fallthrough | EdgeKind::LoopBody | EdgeKind::LoopExit
        ) && (!is_own_branch_continuation(*edge)
            || loop_.semantic_continue_edges.contains(edge)
            || proven_body_bypass
            || candidate.kind_hint == LoopKindHint::RepeatLike && repeat_prefix_is_movable)
            && (candidate.backedges.binary_search(edge).is_err()
                || cfg.succs[source.index()].len() > 1
                || proven_body_bypass
                || loop_.semantic_continue_edges.contains(edge))
    });
    let continue_target_carries_body_tail = candidate.kind_hint == LoopKindHint::NumericForLike
        && candidate
            .continue_target
            .is_some_and(|target| block_has_non_control_prefix(proto, cfg, target));
    if let Some(target) = candidate.continue_target
        && !continue_target_carries_body_tail
    {
        let reaches_target = body_blocks_reaching_target(cfg, &body, target);
        let forward_index = PureContinueForwardIndex::build_cfg(
            cfg,
            &body,
            target,
            &context.forwarding_barriers,
            &context.label_targets,
        )?;
        for block in &body {
            for edge in &cfg.succs[block.index()] {
                let own_branch_continuation = is_own_branch_continuation(*edge);
                let relaxed_own_continuation = caps.continue_stmt
                    && own_branch_continuation
                    && !(candidate.kind_hint == LoopKindHint::RepeatLike
                        && candidate.continue_target.is_some_and(|target| {
                            branch_conditions_share_subject(proto, cfg, *block, target)
                        }));
                if !matches!(
                    cfg.edges[edge.index()].kind,
                    EdgeKind::Fallthrough | EdgeKind::LoopBody | EdgeKind::LoopExit
                ) && candidate.backedges.binary_search(edge).is_err()
                    && (!own_branch_continuation || relaxed_own_continuation)
                    && continue_edge_bypasses_body_parts(cfg, &body, *edge)
                    && continue_pad_sibling_reaches_target(cfg, *edge, &reaches_target)
                    && (candidate.kind_hint != LoopKindHint::RepeatLike || repeat_prefix_is_movable)
                    && (cfg.edges[edge.index()].to == target
                        || forward_index.route(cfg, *edge).is_some())
                {
                    continues.insert(*edge);
                }
            }
        }
    }
    let exit_targets = owned
        .iter()
        .flat_map(|block| cfg.succs[block.index()].iter())
        .map(|edge| cfg.edges[edge.index()].to)
        .filter(|target| !owned.contains(target))
        .collect::<BTreeSet<_>>();
    let control_exit_targets = control
        .iter()
        .flat_map(|block| cfg.succs[block.index()].iter())
        .map(|edge| cfg.edges[edge.index()].to)
        .filter(|target| !owned.contains(target))
        .collect::<BTreeSet<_>>();
    let lexical_exit_targets = exit_targets
        .iter()
        .copied()
        .filter(|target| *target != cfg.exit_block)
        .collect::<Vec<_>>();
    let continuation = loop_
        .continuation
        .filter(|target| exit_targets.contains(target))
        .or_else(|| {
            (candidate.exits.len() == 1)
                .then(|| candidate.exits.first().copied())
                .flatten()
                .filter(|target| exit_targets.contains(target))
        })
        .or_else(|| {
            (control_exit_targets.len() == 1)
                .then(|| control_exit_targets.first().copied())
                .flatten()
        })
        // 终止型 body 可能让 VM latch/normal exit 不可达；synthetic exit 只表示
        // return/tailcall，不应和唯一的词法 break 目标竞争 continuation。
        .or_else(|| {
            (lexical_exit_targets.len() == 1)
                .then(|| lexical_exit_targets.first().copied())
                .flatten()
        })
        .or_else(|| {
            (exit_targets.len() == 1)
                .then(|| exit_targets.first().copied())
                .flatten()
        });
    let mut break_routes = BTreeMap::new();
    if let Some(target) = continuation {
        for block in &control {
            for edge in &cfg.succs[block.index()] {
                let cfg_edge = cfg.edges[edge.index()];
                if cfg_edge.kind != EdgeKind::LoopExit
                    && cfg_edge.to != target
                    && !owned.contains(&cfg_edge.to)
                    && let Some(route) = exclusive_break_forwarding_route(
                        proto,
                        cfg,
                        *edge,
                        target,
                        &context.forwarding_barriers,
                        &context.label_targets,
                    )
                {
                    break_routes.insert(*edge, route);
                }
            }
        }
    }
    let normal_tail = detect_normal_loop_tail(
        proto,
        cfg,
        NormalLoopTailDomain {
            candidate,
            preheader,
            control: &control,
            body: &body,
            owned: &owned,
            continuation,
        },
    );

    Ok(LoopPartitions {
        preheader,
        control,
        body,
        owned,
        continuation,
        continues,
        break_routes,
        normal_tail,
    })
}

fn closed_linear_terminal_arm(
    proto: &LoweredProto,
    cfg: &Cfg,
    entry: BlockRef,
    owner: &BTreeSet<BlockRef>,
) -> Option<Vec<BlockRef>> {
    let mut blocks = Vec::new();
    let mut visited = vec![false; cfg.blocks.len()];
    let mut block = entry;
    loop {
        if block == cfg.exit_block || std::mem::replace(&mut visited[block.index()], true) {
            return None;
        }
        if cfg.preds[block.index()].iter().any(|edge| {
            let source = cfg.edges[edge.index()].from;
            cfg.reachable_blocks.contains(&source)
                && !owner.contains(&source)
                && !visited[source.index()]
        }) {
            return None;
        }
        blocks.push(block);
        match cfg.terminator(&proto.instrs, block)? {
            LowInstr::Return(_) | LowInstr::TailCall(_) => return Some(blocks),
            LowInstr::Jump(_) => {
                let [edge] = cfg.succs[block.index()].as_slice() else {
                    return None;
                };
                block = cfg.edges[edge.index()].to;
            }
            _ => return None,
        }
    }
}

/// natural-loop SCC 不包含“进入一个结构化子图后只会 break/return”的词法 arm。
/// 这类 arm 若留在 loop 外，入口边只能退化为 goto；这里仅接纳单入口、且所有出口
/// 都直达当前 loop continuation 或函数出口的闭合子图。
struct WhileBreakArmDomain<'a> {
    candidate: &'a crate::structure::LoopCandidate,
    natural: &'a BTreeSet<BlockRef>,
    condition_blocks: Option<&'a BTreeSet<BlockRef>>,
    continuation: Option<BlockRef>,
}

fn verified_while_break_arms(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    context: &LoopPartitionContext,
    domain: WhileBreakArmDomain<'_>,
    workspace: &mut WhileBreakArmWorkspace,
) -> Result<BTreeSet<BlockRef>, StructureError> {
    let Some(continuation) = domain.continuation else {
        return Ok(BTreeSet::new());
    };
    let candidate = domain.candidate;
    let natural = domain.natural;
    workspace.begin_loop();
    for &block in natural {
        workspace.insert(block, WHILE_BREAK_OWNED)?;
        if workspace.insert(block, WHILE_BREAK_QUEUED)? {
            workspace.pending.push_back(block);
        }
    }
    for block in std::iter::once(candidate.header)
        .chain(candidate.control_blocks.iter().copied())
        .chain(domain.condition_blocks.into_iter().flatten().copied())
    {
        workspace.insert(block, WHILE_BREAK_EXCLUDED)?;
    }

    let mut added = Vec::new();
    while let Some(source) = workspace.pending.pop_front() {
        workspace.remove(source, WHILE_BREAK_QUEUED)?;
        if !workspace.contains(source, WHILE_BREAK_OWNED)?
            || workspace.contains(source, WHILE_BREAK_EXCLUDED)?
        {
            continue;
        }
        let successors = &cfg.succs[source.index()];
        if successors.len() != 2
            || !successors.iter().all(|edge| {
                matches!(
                    cfg.edges[edge.index()].kind,
                    EdgeKind::BranchTrue | EdgeKind::BranchFalse
                )
            })
        {
            continue;
        }
        for (entry_index, &entry_edge) in successors.iter().enumerate() {
            let entry = cfg.edges[entry_edge.index()].to;
            let sibling = cfg.edges[successors[1 - entry_index].index()].to;
            if entry == continuation
                || entry == cfg.exit_block
                || workspace.contains(entry, WHILE_BREAK_OWNED)?
                || !(workspace.contains(sibling, WHILE_BREAK_OWNED)? || sibling == continuation)
            {
                continue;
            }
            if !workspace.mark_attempted(entry_edge)?
                || !closed_break_arm(
                    cfg,
                    graph_facts,
                    context,
                    workspace,
                    source,
                    entry_edge,
                    continuation,
                )?
            {
                continue;
            }
            let arm_len = workspace.arm_blocks.len();
            for arm_index in 0..arm_len {
                let block = workspace.arm_blocks[arm_index];
                if !workspace.insert(block, WHILE_BREAK_OWNED)? {
                    return Err(StructureError::invalid(
                        "verified break arms overlap after ownership was frozen",
                    ));
                }
                added.push(block);
                if workspace.insert(block, WHILE_BREAK_QUEUED)? {
                    workspace.pending.push_back(block);
                }
                for &incoming in &cfg.preds[block.index()] {
                    let predecessor = cfg.edges[incoming.index()].from;
                    if workspace.contains(predecessor, WHILE_BREAK_OWNED)?
                        && workspace.insert(predecessor, WHILE_BREAK_QUEUED)?
                    {
                        workspace.pending.push_back(predecessor);
                    }
                }
            }
        }
    }
    Ok(added.into_iter().collect())
}

fn closed_break_arm(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    context: &LoopPartitionContext,
    workspace: &mut WhileBreakArmWorkspace,
    source: BlockRef,
    entry_edge: EdgeRef,
    continuation: BlockRef,
) -> Result<bool, StructureError> {
    let entry = cfg
        .edges
        .get(entry_edge.index())
        .ok_or_else(|| StructureError::invalid("break arm entry edge is outside the CFG arena"))?
        .to;
    workspace.begin_arm();
    workspace.arm_pending.push(entry);
    let mut reaches_continuation = false;
    while let Some(block) = workspace.arm_pending.pop() {
        if block == continuation {
            reaches_continuation = true;
            continue;
        }
        if block == cfg.exit_block {
            continue;
        }
        if workspace.contains(block, WHILE_BREAK_OWNED)?
            || !context
                .reachable_by_block
                .get(block.index())
                .copied()
                .ok_or_else(|| {
                    StructureError::invalid("break arm block is outside the CFG arena")
                })?
            // 单入口闭合 arm 的 entry 必须支配其全部 block。这个 interval 检查使
            // 多入口共享尾在首个汇合点即失败，避免每个入口重复遍历同一长尾。
            || !graph_facts.dominates(entry, block)
            || context
                .unstructured_by_block
                .get(block.index())
                .copied()
                .ok_or_else(|| {
                    StructureError::invalid("break arm block is outside the CFG arena")
                })?
            || context
                .residual_incidents_by_block
                .get(block.index())
                .ok_or_else(|| {
                    StructureError::invalid("break arm block is outside the CFG arena")
                })?
                .iter()
                .any(|residual| *residual != entry_edge)
        {
            return Ok(false);
        }
        if !workspace.visit(block)? {
            continue;
        }
        workspace.arm_blocks.push(block);
        for edge in &cfg.succs[block.index()] {
            let target = cfg.edges[edge.index()].to;
            if workspace.contains(target, WHILE_BREAK_OWNED)? {
                return Ok(false);
            }
            if target == continuation {
                reaches_continuation = true;
            } else if target != cfg.exit_block {
                workspace.arm_pending.push(target);
            }
        }
    }
    if workspace.arm_blocks.is_empty() || !reaches_continuation {
        return Ok(false);
    }
    for &block in &workspace.arm_blocks {
        for incoming in &cfg.preds[block.index()] {
            let edge = cfg.edges.get(incoming.index()).ok_or_else(|| {
                StructureError::invalid("break arm predecessor edge is outside the CFG arena")
            })?;
            if !context
                .reachable_by_block
                .get(edge.from.index())
                .copied()
                .ok_or_else(|| {
                    StructureError::invalid("break arm predecessor is outside the CFG arena")
                })?
                || workspace.is_visited(edge.from)?
            {
                continue;
            }
            if block != entry || edge.from != source || *incoming != entry_edge {
                return Ok(false);
            }
        }
    }
    Ok(true)
}

fn continue_pad_sibling_reaches_target(
    cfg: &Cfg,
    edge: EdgeRef,
    reaches_target: &BTreeSet<BlockRef>,
) -> bool {
    let source = cfg.edges[edge.index()].from;
    if cfg.succs[source.index()].len() != 1 {
        return true;
    }
    cfg.preds[source.index()].iter().any(|incoming| {
        let predecessor = cfg.edges[incoming.index()].from;
        cfg.succs[predecessor.index()].iter().any(|sibling| {
            *sibling != *incoming && reaches_target.contains(&cfg.edges[sibling.index()].to)
        })
    })
}

struct NormalLoopTailDomain<'a> {
    candidate: &'a crate::structure::LoopCandidate,
    preheader: Option<BlockRef>,
    control: &'a BTreeSet<BlockRef>,
    body: &'a BTreeSet<BlockRef>,
    owned: &'a BTreeSet<BlockRef>,
    continuation: Option<BlockRef>,
}

fn detect_normal_loop_tail(
    proto: &LoweredProto,
    cfg: &Cfg,
    domain: NormalLoopTailDomain<'_>,
) -> Option<NormalTailPartition> {
    use crate::structure::LoopKindHint;

    let candidate = domain.candidate;
    let preheader = domain.preheader;
    let control = domain.control;
    let body = domain.body;
    let owned = domain.owned;
    if !matches!(
        candidate.kind_hint,
        LoopKindHint::WhileLike | LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
    ) {
        return None;
    }
    if candidate.kind_hint == LoopKindHint::GenericForLike
        && matches!(
            cfg.terminator(&proto.instrs, candidate.header),
            Some(LowInstr::GenericForLoop(instr))
                if crate::structure::helpers::share_transparent_jump_target(
                    proto,
                    cfg,
                    instr.exit_target,
                    instr.body_target,
                )
        )
    {
        // body 与零迭代出口最终进入同一透明 pad 时，源码语义是“首轮立即
        // break”，并不存在只应由正常出口执行的 tail。
        return None;
    }
    let continuation = domain.continuation?;
    let normal_exits = preheader
        .into_iter()
        .chain(control.iter().copied())
        .flat_map(|block| cfg.succs[block.index()].iter().copied())
        .filter(|edge| {
            let edge = cfg.edges[edge.index()];
            !owned.contains(&edge.to)
                && edge.to != cfg.exit_block
                && if matches!(
                    candidate.kind_hint,
                    LoopKindHint::NumericForLike | LoopKindHint::GenericForLike
                ) {
                    edge.kind == EdgeKind::LoopExit
                } else {
                    !matches!(edge.kind, EdgeKind::Return | EdgeKind::TailCall)
                }
        })
        .collect::<Vec<_>>();
    let entries = normal_exits
        .iter()
        .map(|edge| cfg.edges[edge.index()].to)
        .collect::<BTreeSet<_>>();
    let mut entries = entries.into_iter();
    let entry = entries.next()?;
    if entries.next().is_some() {
        return None;
    }
    if entry == continuation || owned.contains(&entry) {
        return None;
    }

    let mut early_exits = body
        .iter()
        .flat_map(|block| cfg.succs[block.index()].iter().copied())
        .filter(|edge| {
            let edge_data = cfg.edges[edge.index()];
            edge_data.to == continuation
                && edge_data.kind != EdgeKind::LoopExit
                && candidate.backedges.binary_search(edge).is_err()
        })
        .collect::<Vec<_>>();
    if early_exits.is_empty() {
        return None;
    }

    let mut blocks = BTreeSet::new();
    let mut pending = vec![entry];
    while let Some(current) = pending.pop() {
        if current == continuation || !blocks.insert(current) {
            continue;
        }
        if current == cfg.exit_block || owned.contains(&current) {
            return None;
        }
        for edge in &cfg.succs[current.index()] {
            let edge = cfg.edges[edge.index()];
            if matches!(edge.kind, EdgeKind::Return | EdgeKind::TailCall)
                || edge.to == cfg.exit_block
                || owned.contains(&edge.to)
            {
                return None;
            }
            if edge.to != continuation {
                pending.push(edge.to);
            }
        }
    }

    let normal_exit_set = normal_exits.iter().copied().collect::<BTreeSet<_>>();
    for block in &blocks {
        if cfg.preds[block.index()].iter().any(|edge| {
            let source = cfg.edges[edge.index()].from;
            cfg.reachable_blocks.contains(&source)
                && !blocks.contains(&source)
                && !normal_exit_set.contains(edge)
        }) || cfg.succs[block.index()].iter().any(|edge| {
            let target = cfg.edges[edge.index()].to;
            target != continuation && !blocks.contains(&target)
        }) {
            return None;
        }
    }
    let mut indegree = vec![0usize; cfg.blocks.len()];
    for block in &blocks {
        for edge in &cfg.succs[block.index()] {
            let target = cfg.edges[edge.index()].to;
            if blocks.contains(&target) {
                indegree[target.index()] += 1;
            }
        }
    }
    let mut ready = blocks
        .iter()
        .copied()
        .filter(|block| indegree[block.index()] == 0)
        .collect::<Vec<_>>();
    let mut visited = 0usize;
    while let Some(block) = ready.pop() {
        visited += 1;
        for edge in &cfg.succs[block.index()] {
            let target = cfg.edges[edge.index()].to;
            if !blocks.contains(&target) {
                continue;
            }
            indegree[target.index()] -= 1;
            if indegree[target.index()] == 0 {
                ready.push(target);
            }
        }
    }
    if visited != blocks.len() {
        return None;
    }

    early_exits.sort_by_key(|edge| edge.index());
    early_exits.dedup();
    let mut normal_exits = normal_exits;
    normal_exits.sort_by_key(|edge| edge.index());
    normal_exits.dedup();
    Some(NormalTailPartition {
        entry,
        blocks,
        continuation,
        early_exits,
        normal_exits,
    })
}

fn exclusive_break_forwarding_route(
    proto: &LoweredProto,
    cfg: &Cfg,
    entry: EdgeRef,
    target: BlockRef,
    barriers: &BTreeSet<BlockRef>,
    labels: &BTreeSet<BlockRef>,
) -> Option<Vec<EdgeRef>> {
    let mut incoming = entry;
    let mut block = cfg.edges.get(entry.index())?.to;
    let mut route = Vec::new();
    while block != target {
        if barriers.contains(&block)
            || labels.contains(&block)
            || cfg.preds.get(block.index())?.as_slice() != [incoming]
        {
            return None;
        }
        let range = cfg.blocks.get(block.index())?.instrs;
        let [edge] = cfg.succs.get(block.index())?.as_slice() else {
            return None;
        };
        if cfg.edges.get(edge.index())?.kind != EdgeKind::Jump {
            return None;
        }
        let end = range.last().map_or(range.end(), |last| {
            if proto.instrs[last.index()].is_control_terminator() {
                range.end() - 1
            } else {
                range.end()
            }
        });
        if !(range.start.index()..end).all(|index| matches!(proto.instrs[index], LowInstr::Move(_)))
        {
            return None;
        }
        route.push(*edge);
        incoming = *edge;
        block = cfg.edges[edge.index()].to;
    }
    (!route.is_empty()).then_some(route)
}

fn block_has_non_control_prefix(proto: &LoweredProto, cfg: &Cfg, block: BlockRef) -> bool {
    let range = cfg.blocks[block.index()].instrs;
    let end = range.last().map_or(range.end(), |last| {
        if proto.instrs[last.index()].is_control_terminator() {
            range.end() - 1
        } else {
            range.end()
        }
    });
    range.start.index() < end
}

fn merged_natural_loop_domain(
    cfg: &Cfg,
    candidate: &crate::structure::LoopCandidate,
) -> BTreeSet<BlockRef> {
    let mut domain = BTreeSet::from([candidate.header]);
    let mut pending = candidate
        .backedges
        .iter()
        .filter_map(|edge| cfg.edges.get(edge.index()))
        .filter(|edge| edge.to == candidate.header)
        .map(|edge| edge.from)
        .collect::<Vec<_>>();
    while let Some(block) = pending.pop() {
        if !domain.insert(block) || block == candidate.header {
            continue;
        }
        pending.extend(cfg.preds[block.index()].iter().filter_map(|edge| {
            let source = cfg.edges[edge.index()].from;
            cfg.reachable_blocks.contains(&source).then_some(source)
        }));
    }
    domain
}

const LOOP_EXIT_PAD_CANDIDATE: u8 = 1 << 0;
const LOOP_EXIT_PAD_REACHES_EXIT: u8 = 1 << 1;
const LOOP_EXIT_PAD_SELECTED: u8 = 1 << 2;
const LOOP_EXIT_PAD_INVALID_QUEUED: u8 = 1 << 3;

#[derive(Clone, Copy, Default)]
struct LoopExitPadBlockState {
    epoch: usize,
    flags: u8,
}

struct LoopExitPadWorkspace {
    epoch: usize,
    blocks: Vec<LoopExitPadBlockState>,
    touched_pads: Vec<BlockRef>,
    pending: VecDeque<BlockRef>,
    invalid: VecDeque<BlockRef>,
}

impl LoopExitPadWorkspace {
    fn new(block_count: usize) -> Self {
        Self {
            epoch: 0,
            blocks: vec![LoopExitPadBlockState::default(); block_count],
            touched_pads: Vec::new(),
            pending: VecDeque::new(),
            invalid: VecDeque::new(),
        }
    }

    fn begin(&mut self) -> Result<(), StructureError> {
        self.epoch = self
            .epoch
            .checked_add(1)
            .ok_or_else(|| StructureError::invalid("loop exit-pad workspace epoch overflows"))?;
        self.touched_pads.clear();
        self.pending.clear();
        self.invalid.clear();
        Ok(())
    }

    fn contains(&self, block: BlockRef, flag: u8) -> Result<bool, StructureError> {
        let state = self.blocks.get(block.index()).ok_or_else(|| {
            StructureError::invalid(format!(
                "loop exit-pad analysis references missing block {block}"
            ))
        })?;
        Ok(state.epoch == self.epoch && state.flags & flag != 0)
    }

    fn insert(&mut self, block: BlockRef, flag: u8) -> Result<bool, StructureError> {
        let state = self.blocks.get_mut(block.index()).ok_or_else(|| {
            StructureError::invalid(format!(
                "loop exit-pad analysis references missing block {block}"
            ))
        })?;
        if state.epoch != self.epoch {
            *state = LoopExitPadBlockState {
                epoch: self.epoch,
                flags: 0,
            };
        }
        let inserted = state.flags & flag == 0;
        state.flags |= flag;
        Ok(inserted)
    }

    fn remove(&mut self, block: BlockRef, flag: u8) -> Result<(), StructureError> {
        let state = self.blocks.get_mut(block.index()).ok_or_else(|| {
            StructureError::invalid(format!(
                "loop exit-pad analysis references missing block {block}"
            ))
        })?;
        if state.epoch == self.epoch {
            state.flags &= !flag;
        }
        Ok(())
    }

    fn select_pad(&mut self, block: BlockRef) -> Result<(), StructureError> {
        if self.insert(block, LOOP_EXIT_PAD_SELECTED)? {
            self.touched_pads.push(block);
        }
        Ok(())
    }

    fn selected_pads(&self) -> Result<BTreeSet<BlockRef>, StructureError> {
        let mut pads = BTreeSet::new();
        for block in self.touched_pads.iter().copied() {
            if self.contains(block, LOOP_EXIT_PAD_SELECTED)? {
                pads.insert(block);
            }
        }
        Ok(pads)
    }
}

fn verified_loop_exit_pads(
    cfg: &Cfg,
    candidate: &crate::structure::LoopCandidate,
    continuation: Option<BlockRef>,
    owned: &BTreeSet<BlockRef>,
    control: &BTreeSet<BlockRef>,
    workspace: &mut LoopExitPadWorkspace,
) -> Result<BTreeSet<BlockRef>, StructureError> {
    workspace.begin()?;
    let control_exit_targets = control
        .iter()
        .flat_map(|block| cfg.succs[block.index()].iter())
        .map(|edge| cfg.edges[edge.index()].to)
        .filter(|target| !control.contains(target) && !owned.contains(target))
        .collect::<BTreeSet<_>>();
    let candidates = candidate
        .body_scope_blocks
        .iter()
        .copied()
        .chain(candidate.exits.iter().copied())
        .filter(|block| {
            !owned.contains(block)
                && Some(*block) != continuation
                && !control_exit_targets.contains(block)
                && Some(*block) != candidate.preheader
                && cfg.reachable_blocks.contains(block)
        })
        .collect::<BTreeSet<_>>();
    for block in &candidates {
        workspace.insert(*block, LOOP_EXIT_PAD_CANDIDATE)?;
    }
    for block in candidate.exits.iter().copied().chain(continuation) {
        if workspace.insert(block, LOOP_EXIT_PAD_REACHES_EXIT)? {
            workspace.pending.push_back(block);
        }
    }
    if candidate.exits.len() > 1 {
        let successors = candidate
            .exits
            .iter()
            .filter_map(|block| cfg.unique_reachable_successor(*block))
            .collect::<BTreeSet<_>>();
        if successors.len() == 1 {
            for block in successors {
                if workspace.insert(block, LOOP_EXIT_PAD_REACHES_EXIT)? {
                    workspace.pending.push_back(block);
                }
            }
        }
    }

    for block in candidates.iter().copied() {
        let [edge] = cfg.succs[block.index()].as_slice() else {
            continue;
        };
        let reachable_predecessors = cfg.preds[block.index()]
            .iter()
            .filter(|edge| cfg.reachable_blocks.contains(&cfg.edges[edge.index()].from))
            .count();
        if reachable_predecessors == 1
            && matches!(
                cfg.edges[edge.index()].kind,
                EdgeKind::Return | EdgeKind::TailCall
            )
        {
            workspace.select_pad(block)?;
            if workspace.insert(block, LOOP_EXIT_PAD_REACHES_EXIT)? {
                workspace.pending.push_back(block);
            }
        }
    }

    while let Some(target) = workspace.pending.pop_front() {
        for incoming in &cfg.preds[target.index()] {
            let edge = cfg.edges[incoming.index()];
            let source = edge.from;
            if !workspace.contains(source, LOOP_EXIT_PAD_CANDIDATE)?
                || workspace.contains(source, LOOP_EXIT_PAD_SELECTED)?
                || source == target
            {
                continue;
            }
            let [only] = cfg.succs[source.index()].as_slice() else {
                continue;
            };
            if *only != *incoming || matches!(edge.kind, EdgeKind::Return | EdgeKind::TailCall) {
                continue;
            }
            workspace.select_pad(source)?;
            if workspace.insert(source, LOOP_EXIT_PAD_REACHES_EXIT)? {
                workspace.pending.push_back(source);
            }
        }
    }

    for index in 0..workspace.touched_pads.len() {
        let block = workspace.touched_pads[index];
        if !workspace.contains(block, LOOP_EXIT_PAD_SELECTED)? {
            continue;
        }
        let mut reachable_predecessors = 0usize;
        let mut has_external_predecessor = false;
        for incoming in &cfg.preds[block.index()] {
            let source = cfg.edges[incoming.index()].from;
            if !cfg.reachable_blocks.contains(&source) {
                continue;
            }
            reachable_predecessors += 1;
            has_external_predecessor |=
                !owned.contains(&source) && !workspace.contains(source, LOOP_EXIT_PAD_SELECTED)?;
        }
        if (reachable_predecessors == 0 || has_external_predecessor)
            && workspace.insert(block, LOOP_EXIT_PAD_INVALID_QUEUED)?
        {
            workspace.invalid.push_back(block);
        }
    }
    while let Some(block) = workspace.invalid.pop_front() {
        if !workspace.contains(block, LOOP_EXIT_PAD_SELECTED)? {
            continue;
        }
        workspace.remove(block, LOOP_EXIT_PAD_SELECTED)?;
        for outgoing in &cfg.succs[block.index()] {
            let target = cfg.edges[outgoing.index()].to;
            if workspace.contains(target, LOOP_EXIT_PAD_SELECTED)?
                && workspace.insert(target, LOOP_EXIT_PAD_INVALID_QUEUED)?
            {
                workspace.invalid.push_back(target);
            }
        }
    }
    workspace.selected_pads()
}

fn for_latch_exit_control_pads(
    proto: &LoweredProto,
    cfg: &Cfg,
    control: &BTreeSet<BlockRef>,
    owned: &BTreeSet<BlockRef>,
) -> BTreeSet<BlockRef> {
    let mut pending = control
        .iter()
        .flat_map(|block| cfg.succs[block.index()].iter().copied())
        .filter(|edge| cfg.edges[edge.index()].kind == EdgeKind::LoopExit)
        .map(|edge| cfg.edges[edge.index()].to)
        .collect::<Vec<_>>();
    let mut pads = BTreeSet::new();
    while let Some(block) = pending.pop() {
        if !owned.contains(&block) || pads.contains(&block) {
            continue;
        }
        let range = cfg.blocks[block.index()].instrs;
        let [edge] = cfg.succs[block.index()].as_slice() else {
            continue;
        };
        if range.len != 1
            || !matches!(proto.instrs[range.start.index()], LowInstr::Jump(_))
            || cfg.edges[edge.index()].kind != EdgeKind::Jump
        {
            continue;
        }
        pads.insert(block);
        pending.push(cfg.edges[edge.index()].to);
    }
    pads
}

struct LoopPayloadFreezeInput<'a> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    edge_plans: &'a [EdgePlan],
    evidence: &'a super::LoopPlanInput,
    partition: &'a LoopPartitions,
    loop_region: RegionId,
    planned_propagated_break: Option<RegionId>,
    break_edges: &'a [EdgeRef],
    continue_edges: &'a [EdgeRef],
    tbc_flow: &'a crate::structure::scope::TbcFlowFacts,
    condition: Option<super::ConditionPlanId>,
    condition_entry: Option<BlockRef>,
    condition_terminals: Option<[EdgeRef; 2]>,
}

fn freeze_loop_payload(
    input: LoopPayloadFreezeInput<'_>,
) -> Result<super::LoopPlanData, StructureError> {
    let LoopPayloadFreezeInput {
        proto,
        cfg,
        edge_plans,
        evidence,
        partition,
        loop_region,
        planned_propagated_break,
        break_edges,
        continue_edges,
        tbc_flow,
        condition,
        condition_entry,
        condition_terminals,
    } = input;
    let candidate = &evidence.candidate;
    let mut control_edges =
        freeze_loop_control_edges(cfg, candidate, partition, condition_terminals)?;
    control_edges.continues.extend_from_slice(continue_edges);
    control_edges.continues.sort_by_key(|edge| edge.index());
    control_edges.continues.dedup();
    let exit_tail = detect_loop_exit_tail(
        proto,
        cfg,
        edge_plans,
        partition,
        loop_region,
        &control_edges,
        break_edges,
        tbc_flow,
    )?;
    let propagated_break =
        freeze_propagated_break(cfg, edge_plans, partition, planned_propagated_break);
    let condition_prefix_placement = (!partition.control.is_empty()
        && matches!(
            candidate.kind_hint,
            crate::structure::LoopKindHint::WhileLike
                | crate::structure::LoopKindHint::RepeatLike
                | crate::structure::LoopKindHint::Unknown
        ))
    .then_some(
        if candidate.kind_hint == crate::structure::LoopKindHint::RepeatLike
            && condition_entry
                .or(candidate.condition_header)
                .or(candidate.continue_target)
                .unwrap_or(candidate.header)
                != candidate.header
            && control_edges.continues.is_empty()
        {
            super::LoopConditionPrefixPlacement::AfterBody
        } else {
            super::LoopConditionPrefixPlacement::BeforeBody
        },
    );
    let continue_target = if matches!(
        candidate.kind_hint,
        crate::structure::LoopKindHint::NumericForLike
            | crate::structure::LoopKindHint::GenericForLike
    ) {
        candidate
            .continue_target
            .filter(|target| partition.control.contains(target))
    } else {
        candidate.continue_target
    };

    Ok(super::LoopPlanData {
        kind: candidate.kind_hint,
        header: candidate.header,
        preheader_block: partition.preheader,
        condition_header: candidate.condition_header,
        condition,
        condition_prefix_placement,
        continuation: partition.continuation,
        continue_target,
        source_bindings: candidate.source_bindings,
        control_edges,
        break_edges: break_edges.to_vec(),
        normalized_exit_aliases: candidate.normalized_exit_aliases.clone(),
        normal_tail: partition
            .normal_tail
            .as_ref()
            .map(|tail| super::LoopNormalTailPlan {
                entry: tail.entry,
                continuation: tail.continuation,
                early_exits: tail.early_exits.clone(),
                normal_exits: tail.normal_exits.clone(),
            }),
        exit_tail,
        propagated_break,
        header_values: candidate.header_value_merges.clone(),
        exit_values: candidate.exit_value_merges.clone(),
        carried_values: evidence.carried_values.clone(),
        protocol: None,
        value_actions: None,
    })
}

fn freeze_propagated_break(
    cfg: &Cfg,
    edge_plans: &[EdgePlan],
    partition: &LoopPartitions,
    planned_target: Option<RegionId>,
) -> Option<RegionId> {
    let target = planned_target?;
    let mut exits = Vec::new();
    for block in &partition.owned {
        for edge in &cfg.succs[block.index()] {
            let cfg_edge = cfg.edges.get(edge.index())?;
            if partition.owned.contains(&cfg_edge.to)
                || matches!(cfg_edge.kind, EdgeKind::Return | EdgeKind::TailCall)
                || shared_pure_terminal_kind(cfg, cfg_edge.to).is_some()
            {
                continue;
            }
            let edge_plan = edge_plans.get(edge.index())?;
            exits.push((cfg_edge, edge_plan));
        }
    }
    (!exits.is_empty()
        && exits.into_iter().all(|(edge, plan)| {
            matches!(plan.transfer, EdgeTransfer::Break(owner) if owner == target)
                || matches!(
                    plan.transfer,
                    EdgeTransfer::BranchArm(super::BranchArm::LoopExit)
                ) && Some(edge.to) == partition.continuation
        }))
    .then_some(target)
}

#[allow(clippy::too_many_arguments)]
fn detect_loop_exit_tail(
    proto: &LoweredProto,
    cfg: &Cfg,
    edge_plans: &[EdgePlan],
    partition: &LoopPartitions,
    loop_region: RegionId,
    control_edges: &super::LoopControlEdges,
    break_edges: &[EdgeRef],
    tbc_flow: &crate::structure::scope::TbcFlowFacts,
) -> Result<Option<super::LoopExitTailPlan>, StructureError> {
    if partition.normal_tail.is_some() {
        return Ok(None);
    }
    let [normal_exit] = control_edges.exit.as_slice() else {
        return Ok(None);
    };
    let normal_exit = *normal_exit;
    let Some(edge_plan) = edge_plans.get(normal_exit.index()) else {
        return Err(StructureError::invalid(
            "loop normal exit references a missing edge plan",
        ));
    };
    if edge_plan.owner != loop_region
        || edge_plan.transfer != EdgeTransfer::Break(loop_region)
        || edge_plan.forward_route.is_some()
    {
        return Ok(None);
    }
    let cfg_edge = cfg
        .edges
        .get(normal_exit.index())
        .ok_or_else(|| StructureError::invalid("loop normal exit references a missing CFG edge"))?;
    let Some(continuation) = partition.continuation else {
        return Ok(None);
    };
    if cfg_edge.to != continuation || continuation == cfg.exit_block {
        return Ok(None);
    }
    let mut predecessors = cfg.preds[continuation.index()]
        .iter()
        .copied()
        .filter(|edge| cfg.reachable_blocks.contains(&cfg.edges[edge.index()].from))
        .collect::<Vec<_>>();
    predecessors.sort_by_key(|edge| edge.index());
    if predecessors.as_slice() != [normal_exit] {
        return Ok(None);
    }

    let active = tbc_flow
        .active_at_entry(continuation)
        .ok_or_else(|| StructureError::invalid("loop exit tail block has no TBC entry facts"))?;
    let mut required = BTreeMap::<usize, BTreeSet<InstrRef>>::new();
    for origin in active {
        let Some(origin_block) = cfg.instr_to_block.get(origin.index()) else {
            return Err(StructureError::invalid(
                "loop exit tail TBC origin has no CFG block",
            ));
        };
        if !partition.owned.contains(origin_block) {
            continue;
        }
        let Some(LowInstr::Tbc(tbc)) = proto.instrs.get(origin.index()) else {
            return Err(StructureError::invalid(
                "loop exit tail active origin is not a TBC instruction",
            ));
        };
        required.entry(tbc.reg.index()).or_default().insert(*origin);
    }
    if required.is_empty() {
        return Ok(None);
    }

    let block_range = cfg.blocks[continuation.index()].instrs;
    let mut cleanup = Vec::new();
    let mut has_observable_prefix = false;
    let mut tail_end = None;
    let mut cleanup_block = continuation;
    let mut cleanup_route = Vec::new();
    let mut trailing_jump = None;
    for index in block_range.start.index()..block_range.end() {
        let instr_ref = InstrRef(index);
        match proto.instrs.get(index) {
            Some(LowInstr::Tbc(tbc)) => {
                cleanup.push(instr_ref);
                required
                    .entry(tbc.reg.index())
                    .or_default()
                    .insert(instr_ref);
            }
            Some(LowInstr::Close(close)) => {
                cleanup.push(instr_ref);
                required.retain(|reg, _| *reg < close.from.index());
                if required.is_empty() {
                    tail_end = Some(index + 1);
                    break;
                }
            }
            Some(LowInstr::Jump(_)) if index + 1 == block_range.end() => {
                trailing_jump = Some(instr_ref);
                break;
            }
            Some(instr) if instr.is_control_terminator() => return Ok(None),
            Some(_) => has_observable_prefix = true,
            None => {
                return Err(StructureError::invalid(
                    "loop exit tail range exceeds the instruction arena",
                ));
            }
        }
    }
    if tail_end.is_none() {
        let Some(jump) = trailing_jump else {
            return Ok(None);
        };
        if !cleanup.is_empty() {
            return Ok(None);
        }
        let [route_edge] = cfg.succs[continuation.index()].as_slice() else {
            return Ok(None);
        };
        let Some(route_cfg) = cfg.edges.get(route_edge.index()) else {
            return Err(StructureError::invalid(
                "loop exit tail cleanup route references a missing edge",
            ));
        };
        let Some(route_plan) = edge_plans.get(route_edge.index()) else {
            return Err(StructureError::invalid(
                "loop exit tail cleanup route has no edge plan",
            ));
        };
        if route_cfg.from != continuation
            || route_cfg.kind != EdgeKind::Jump
            || route_plan.transfer != EdgeTransfer::Fallthrough
            || route_plan.forward_route.is_some()
            || route_cfg.to == cfg.exit_block
        {
            return Ok(None);
        }
        let mut cleanup_predecessors = cfg.preds[route_cfg.to.index()]
            .iter()
            .copied()
            .filter(|edge| cfg.reachable_blocks.contains(&cfg.edges[edge.index()].from))
            .collect::<Vec<_>>();
        cleanup_predecessors.sort_by_key(|edge| edge.index());
        if cleanup_predecessors.as_slice() != [*route_edge] {
            return Ok(None);
        }

        cleanup_block = route_cfg.to;
        cleanup_route.push(*route_edge);
        let cleanup_range = cfg.blocks[cleanup_block.index()].instrs;
        for index in cleanup_range.start.index()..cleanup_range.end() {
            let instr_ref = InstrRef(index);
            let Some(LowInstr::Close(close)) = proto.instrs.get(index) else {
                return Ok(None);
            };
            cleanup.push(instr_ref);
            required.retain(|reg, _| *reg < close.from.index());
            if required.is_empty() {
                break;
            }
        }
        if required.is_empty() {
            tail_end = Some(jump.index());
        }
    }
    let Some(end) = tail_end else {
        return Ok(None);
    };
    if !has_observable_prefix || end >= block_range.end() || cleanup.is_empty() {
        return Ok(None);
    }

    let mut early_exits = break_edges
        .iter()
        .copied()
        .filter(|edge| *edge != normal_exit)
        .collect::<Vec<_>>();
    early_exits.sort_by_key(|edge| edge.index());
    early_exits.dedup();
    if early_exits.iter().any(|edge| {
        cfg.edges
            .get(edge.index())
            .is_some_and(|edge| edge.to == continuation)
    }) {
        return Ok(None);
    }

    Ok(Some(super::LoopExitTailPlan {
        normal_exit,
        block: continuation,
        range: crate::structure::InstrRange::new(
            block_range.start,
            end - block_range.start.index(),
        ),
        continuation,
        early_exits,
        cleanup_block,
        cleanup_route,
        cleanup,
    }))
}

fn freeze_loop_control_edges(
    cfg: &Cfg,
    candidate: &crate::structure::LoopCandidate,
    partition: &LoopPartitions,
    condition_terminals: Option<[EdgeRef; 2]>,
) -> Result<super::LoopControlEdges, StructureError> {
    let is_vm_for = matches!(
        candidate.kind_hint,
        crate::structure::LoopKindHint::NumericForLike
            | crate::structure::LoopKindHint::GenericForLike
    );
    let mut control_edges = super::LoopControlEdges {
        backedges: candidate.backedges.clone(),
        ..super::LoopControlEdges::default()
    };
    let repeat_condition_has_unique_backedge = candidate.kind_hint
        == crate::structure::LoopKindHint::RepeatLike
        && condition_terminals.is_some_and(|terminals| {
            terminals
                .iter()
                .filter(|edge| candidate.backedges.contains(edge))
                .count()
                == 1
        });
    if let Some(preheader) = partition.preheader {
        for edge in cfg.succs.get(preheader.index()).into_iter().flatten() {
            let cfg_edge = cfg.edges.get(edge.index()).ok_or_else(|| {
                StructureError::invalid("loop preheader references a missing edge")
            })?;
            let body_role = match (is_vm_for, cfg_edge.kind) {
                (true, EdgeKind::LoopBody) => true,
                (true, EdgeKind::LoopExit) => false,
                _ => partition.owned.contains(&cfg_edge.to) && cfg_edge.to != preheader,
            };
            let slot = if body_role {
                &mut control_edges.preheader_body
            } else {
                &mut control_edges.preheader_exit
            };
            if slot.replace(*edge).is_some() {
                return Err(StructureError::invalid(
                    "for preheader has multiple edges with the same syntax role",
                ));
            }
        }
    }

    for block in &partition.control {
        if candidate
            .normalized_exit_aliases
            .iter()
            .any(|alias| alias.block == *block)
        {
            continue;
        }
        for edge in cfg.succs.get(block.index()).into_iter().flatten() {
            let cfg_edge = cfg.edges.get(edge.index()).ok_or_else(|| {
                StructureError::invalid("loop condition references a missing edge")
            })?;
            let condition_terminal =
                condition_terminals.is_some_and(|terminals| terminals.contains(edge));
            // Numeric/generic-for 的 syntax body edge 可以是 header 自环，同时也是
            // backedge。它仍必须出现在 body role 中，不能因为目标留在 control
            // partition 就被丢弃。
            let vm_for_body_backedge = is_vm_for && candidate.backedges.contains(edge);
            let normalized_exit = candidate
                .normalized_exit_aliases
                .iter()
                .any(|alias| alias.block == cfg_edge.to);
            if partition.control.contains(&cfg_edge.to)
                && !condition_terminal
                && !vm_for_body_backedge
                && !normalized_exit
            {
                continue;
            }
            let body_role = match (is_vm_for, cfg_edge.kind) {
                (true, EdgeKind::LoopBody) => true,
                (true, EdgeKind::LoopExit) => false,
                (false, _) if repeat_condition_has_unique_backedge && condition_terminal => {
                    candidate.backedges.contains(edge)
                }
                _ => {
                    partition.owned.contains(&cfg_edge.to)
                        && Some(cfg_edge.to) != partition.preheader
                }
            };
            if body_role {
                control_edges.body.push(*edge);
            } else {
                control_edges.exit.push(*edge);
            }
        }
    }
    control_edges.body.sort_by_key(|edge| edge.index());
    control_edges.body.dedup();
    control_edges.exit.sort_by_key(|edge| edge.index());
    control_edges.exit.dedup();
    control_edges.backedges.sort_by_key(|edge| edge.index());
    control_edges.backedges.dedup();

    Ok(control_edges)
}

struct PayloadSelectionContext<'a> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    dataflow: &'a DataflowFacts,
    input: &'a FinalPlanInput,
    partitions: &'a [LoopPartitions],
    propagated_break_by_region: &'a [Option<RegionId>],
    edge_plans: &'a [EdgePlan],
    tbc_flow: &'a crate::structure::scope::TbcFlowFacts,
}

fn compact_selected_payloads(
    arena: &mut RegionArena,
    context: PayloadSelectionContext<'_>,
) -> Result<SelectedPayloads, StructureError> {
    let PayloadSelectionContext {
        proto,
        cfg,
        dataflow,
        input,
        partitions,
        propagated_break_by_region,
        edge_plans,
        tbc_flow,
    } = context;
    let selected_branches = arena
        .specs
        .iter()
        .filter_map(|spec| match spec.kind {
            ContainerKind::Branch(id) => Some(id),
            ContainerKind::SinglePass(_)
            | ContainerKind::ValueDecision(_)
            | ContainerKind::Loop(_)
            | ContainerKind::Island(_)
            | ContainerKind::Residual(_) => None,
        })
        .collect::<BTreeSet<_>>();
    let selected_loops = arena
        .specs
        .iter()
        .filter_map(|spec| match spec.kind {
            ContainerKind::Loop(id) => Some(id),
            ContainerKind::SinglePass(_)
            | ContainerKind::Branch(_)
            | ContainerKind::ValueDecision(_)
            | ContainerKind::Island(_)
            | ContainerKind::Residual(_) => None,
        })
        .collect::<BTreeSet<_>>();
    let selected_value_decisions = arena
        .specs
        .iter()
        .filter_map(|spec| match spec.kind {
            ContainerKind::ValueDecision(id) => Some(id),
            ContainerKind::SinglePass(_)
            | ContainerKind::Branch(_)
            | ContainerKind::Loop(_)
            | ContainerKind::Island(_)
            | ContainerKind::Residual(_) => None,
        })
        .collect::<BTreeSet<_>>();
    let selected_conditions = selected_branches
        .iter()
        .filter_map(|id| input.branches[id.index()].condition)
        .chain(selected_loops.iter().filter_map(|id| {
            input.loops[id.index()].condition.filter(|condition| {
                input.conditions[condition.index()]
                    .candidate
                    .blocks
                    .iter()
                    .all(|block| partitions[id.index()].control.contains(block))
            })
        }))
        .collect::<BTreeSet<_>>();

    let mut condition_map = vec![None; input.conditions.len()];
    let mut conditions = Vec::with_capacity(selected_conditions.len());
    for old in selected_conditions {
        let new = super::ConditionPlanId(conditions.len());
        condition_map[old.index()] = Some(new);
        conditions.push(freeze_condition(
            proto,
            cfg,
            dataflow,
            &input.conditions[old.index()],
            Some(edge_plans),
        )?);
    }

    let mut branch_map = vec![None; input.branches.len()];
    let mut branches = Vec::with_capacity(selected_branches.len());
    let mut single_pass_exit_by_header = vec![None; cfg.blocks.len()];
    for fence in &arena.single_passes {
        single_pass_exit_by_header[fence.entry.index()] = Some(fence.continuation);
    }
    for old in selected_branches {
        let new = super::BranchPlanId(branches.len());
        branch_map[old.index()] = Some(new);
        let evidence = &input.branches[old.index()];
        let condition = evidence
            .condition
            .ok_or_else(|| StructureError::invalid("selected branch is missing its condition"))?;
        let condition = condition_map[condition.index()].ok_or_else(|| {
            StructureError::invalid("selected branch condition was not compacted")
        })?;
        branches.push(freeze_branch_payload(
            cfg,
            edge_plans,
            evidence,
            condition,
            conditions.get(condition.index()),
            single_pass_exit_by_header[evidence.branch.header.index()],
        )?);
    }

    let mut value_decision_map = vec![None; input.value_decisions.len()];
    let mut value_decisions = Vec::with_capacity(selected_value_decisions.len());
    let mut value_decision_regions = Vec::with_capacity(selected_value_decisions.len());
    for old in selected_value_decisions {
        let new = super::ValueDecisionPlanId(value_decisions.len());
        value_decision_map[old.index()] = Some(new);
        value_decisions.push(freeze_value_decision(
            proto,
            cfg,
            dataflow,
            &input.value_decisions[old.index()],
        )?);
        value_decision_regions.push(arena.value_decision_region_by_plan[old.index()]);
    }
    assign_absorbed_value_phis(cfg, dataflow, &mut value_decisions)?;

    let mut loop_map = vec![None; input.loops.len()];
    let mut loops = Vec::with_capacity(selected_loops.len());
    let mut loop_regions = Vec::with_capacity(selected_loops.len());
    let mut break_edges_by_region = vec![Vec::new(); arena.regions.len()];
    let mut continue_edges_by_region = vec![Vec::new(); arena.regions.len()];
    for edge_plan in edge_plans {
        match edge_plan.transfer {
            EdgeTransfer::Break(region) => {
                break_edges_by_region[region.index()].push(edge_plan.edge);
            }
            EdgeTransfer::Continue(region) => {
                continue_edges_by_region[region.index()].push(edge_plan.edge);
            }
            _ => {}
        }
    }
    for old in selected_loops {
        let new = super::LoopPlanId(loops.len());
        loop_map[old.index()] = Some(new);
        let evidence = &input.loops[old.index()];
        let condition = evidence
            .condition
            .filter(|condition| {
                input.conditions[condition.index()]
                    .candidate
                    .blocks
                    .iter()
                    .all(|block| partitions[old.index()].control.contains(block))
            })
            .map(|id| {
                condition_map[id.index()].ok_or_else(|| {
                    StructureError::invalid("selected loop condition was not compacted")
                })
            })
            .transpose()?;
        let partition = partitions
            .get(old.index())
            .ok_or_else(|| StructureError::invalid("selected loop has no frozen partitions"))?;
        let loop_region = arena.loop_region_by_plan[old.index()];
        loops.push(freeze_loop_payload(LoopPayloadFreezeInput {
            proto,
            cfg,
            edge_plans,
            evidence,
            partition,
            loop_region,
            planned_propagated_break: propagated_break_by_region
                .get(loop_region.index())
                .copied()
                .flatten(),
            break_edges: &break_edges_by_region[loop_region.index()],
            continue_edges: &continue_edges_by_region[loop_region.index()],
            tbc_flow,
            condition,
            condition_entry: condition
                .and_then(|id| conditions.get(id.index()))
                .and_then(super::ConditionPlan::header),
            condition_terminals: condition
                .and_then(|id| conditions.get(id.index()))
                .map(|condition| [condition.truthy, condition.falsy]),
        })?);
        loop_regions.push(loop_region);
    }

    for region in &mut arena.regions {
        match region {
            RegionPlan::Branch { plan, .. } => {
                *plan = branch_map[plan.index()].ok_or_else(|| {
                    StructureError::invalid("branch region references unselected payload")
                })?;
            }
            RegionPlan::Loop { plan, .. } => {
                *plan = loop_map[plan.index()].ok_or_else(|| {
                    StructureError::invalid("loop region references unselected payload")
                })?;
            }
            RegionPlan::ValueDecision { plan, .. } => {
                *plan = value_decision_map[plan.index()].ok_or_else(|| {
                    StructureError::invalid("value decision region references unselected payload")
                })?;
            }
            RegionPlan::Block { .. }
            | RegionPlan::Sequence { .. }
            | RegionPlan::Unstructured { .. } => {}
        }
    }

    Ok(SelectedPayloads {
        branches,
        loops,
        loop_regions,
        conditions,
        condition_map,
        value_decisions,
        value_decision_regions,
    })
}

fn freeze_condition(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    evidence: &super::ConditionPlanInput,
    edge_plans: Option<&[EdgePlan]>,
) -> Result<super::ConditionPlan, StructureError> {
    let condition = &evidence.candidate;
    let ShortCircuitExit::BranchExit { truthy, falsy } = condition.exit else {
        return Err(StructureError::invalid(
            "selected control condition does not have branch exits",
        ));
    };
    let mut arc_slots = vec![[None, None]; condition.nodes.len()];
    for arc in &evidence.arcs {
        let slots = arc_slots.get_mut(arc.source.index()).ok_or_else(|| {
            StructureError::invalid("condition route references a missing source node")
        })?;
        // slots 的稳定顺序是 [semantic truthy, semantic falsy]；bool 到 usize 的原生
        // 映射恰好相反（false=0, true=1），不能直接拿来索引。
        let slot = &mut slots[usize::from(!arc.truthy)];
        if slot.replace(arc).is_some() {
            return Err(StructureError::invalid(
                "condition node has duplicate semantic branch evidence",
            ));
        }
    }
    let mut truthy_edges = Vec::new();
    let mut falsy_edges = Vec::new();
    let nodes = condition
        .nodes
        .iter()
        .enumerate()
        .map(|(index, node)| {
            let predicate = cfg.blocks[node.header.index()]
                .instrs
                .last()
                .ok_or_else(|| {
                    StructureError::invalid("condition node has an empty predicate block")
                })?;
            let [truthy_arc, falsy_arc] = arc_slots.get(index).copied().ok_or_else(|| {
                StructureError::invalid("condition node is missing its arc slots")
            })?;
            let truthy_arc = truthy_arc.ok_or_else(|| {
                StructureError::invalid("condition node is missing its truthy arc")
            })?;
            let falsy_arc = falsy_arc.ok_or_else(|| {
                StructureError::invalid("condition node is missing its falsy arc")
            })?;
            let truthy_arc = freeze_condition_arc(
                cfg,
                condition,
                truthy_arc,
                truthy,
                falsy,
                &mut truthy_edges,
                &mut falsy_edges,
                edge_plans,
            )?;
            let falsy_arc = freeze_condition_arc(
                cfg,
                condition,
                falsy_arc,
                truthy,
                falsy,
                &mut truthy_edges,
                &mut falsy_edges,
                edge_plans,
            )?;
            let predicate_negated = truthy_arc.polarity == super::ConditionArcPolarity::BranchFalse;
            let mut arcs = [None, None];
            for arc in [truthy_arc, falsy_arc] {
                let slot = &mut arcs[arc.polarity.index()];
                if slot.replace(arc).is_some() {
                    return Err(StructureError::invalid(
                        "condition node has duplicate physical branch polarity",
                    ));
                }
            }
            let [Some(branch_true_arc), Some(branch_false_arc)] = arcs else {
                return Err(StructureError::invalid(
                    "condition node is missing one physical branch route",
                ));
            };
            Ok(super::ConditionNodePlan {
                id: super::ConditionNodeId(index),
                block: node.header,
                predicate,
                predicate_negated,
                arcs: [branch_true_arc, branch_false_arc],
                materialized_value: None,
            })
        })
        .collect::<Result<Vec<_>, StructureError>>()?;
    let mut nodes = nodes;
    for index in 0..nodes.len() {
        nodes[index].materialized_value = freeze_condition_value(
            proto,
            cfg,
            dataflow,
            &nodes,
            super::ConditionNodeId(condition.entry.index()),
            super::ConditionNodeId(index),
        );
    }
    let mut blocks = BTreeSet::new();
    let mut frozen_blocks = Vec::new();
    for node in &nodes {
        if blocks.insert(node.block) {
            frozen_blocks.push(node.block);
        }
        for arc in &node.arcs {
            let transfer_position = arc
                .route
                .iter()
                .position(|edge| *edge == arc.transfer)
                .ok_or_else(|| {
                    StructureError::invalid("condition transfer is outside its physical route")
                })?;
            // transfer 之后的 connector 已由 forward route 物理覆盖，不属于会被
            // condition 表达式吸收的控制分区。
            for block in arc.connector_blocks.iter().copied().take(transfer_position) {
                if blocks.insert(block) {
                    frozen_blocks.push(block);
                }
            }
        }
    }
    let truthy = truthy_edges
        .into_iter()
        .min_by_key(|edge| edge.index())
        .ok_or_else(|| StructureError::invalid("selected condition has no truthy terminal edge"))?;
    let falsy = falsy_edges
        .into_iter()
        .min_by_key(|edge| edge.index())
        .ok_or_else(|| StructureError::invalid("selected condition has no falsy terminal edge"))?;
    Ok(super::ConditionPlan {
        entry: super::ConditionNodeId(condition.entry.index()),
        nodes,
        blocks: frozen_blocks,
        truthy,
        falsy,
    })
}

fn freeze_condition_value(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    nodes: &[super::ConditionNodePlan],
    entry: super::ConditionNodeId,
    node_id: super::ConditionNodeId,
) -> Option<super::ConditionValuePlan> {
    let node = nodes.get(node_id.index())?;
    let LowInstr::Branch(branch) = proto.instrs.get(node.predicate.index())? else {
        return None;
    };
    // Truthiness 会把任意 Lua 值压成 bool；这里只吸收本身已经返回 bool 的比较，
    // 避免把 `not not value` 错还原成原值。
    if !matches!(branch.cond.subject, BranchSubject::Compare { .. }) {
        return None;
    }
    let [raw_truthy, raw_falsy] = [true, false].map(|truthy| {
        let polarity = match truthy ^ node.predicate_negated {
            true => super::ConditionArcPolarity::BranchTrue,
            false => super::ConditionArcPolarity::BranchFalse,
        };
        node.arc(polarity)
    });
    let (
        super::ConditionTarget::Node(truthy_consumer),
        super::ConditionTarget::Node(falsy_consumer),
    ) = (raw_truthy.target, raw_falsy.target)
    else {
        return None;
    };
    if truthy_consumer != falsy_consumer || truthy_consumer == node_id {
        return None;
    }
    let consumer = nodes.get(truthy_consumer.index())?;
    let incoming_edges = [
        raw_truthy.route.last().copied()?,
        raw_falsy.route.last().copied()?,
    ];
    let mut matched = None;
    for phi in dataflow.phi_candidates_in_block(consumer.block) {
        if phi.incoming.len() != 2
            || dataflow.phi_use_count(phi.id) != 1
            || !dataflow.phi_used_only_in_block(phi.id, consumer.block)
            || !dataflow.phi_consumer_ids(phi.id).is_empty()
        {
            continue;
        }
        let values = incoming_edges.map(|edge| {
            let incoming = phi
                .incoming
                .iter()
                .find(|incoming| incoming.edge == Some(edge))?;
            let SsaValue::Def(def) = incoming.value else {
                return None;
            };
            let instr = dataflow.def_instr(def);
            let LowInstr::LoadBool(load) = proto.instrs.get(instr.index())? else {
                return None;
            };
            let block = dataflow.def_block(def);
            node.arcs
                .iter()
                .find(|arc| arc.route.last().copied() == Some(edge))?
                .connector_blocks
                .contains(&block)
                .then_some(load.value)
        });
        let [Some(raw_truthy_value), Some(raw_falsy_value)] = values else {
            continue;
        };
        if raw_truthy_value == raw_falsy_value {
            continue;
        }
        let uses = dataflow.phi_uses.get(phi.id.index())?;
        let [use_site] = uses.as_slice() else {
            continue;
        };
        if cfg.instr_to_block.get(use_site.instr.index()).copied() != Some(consumer.block) {
            continue;
        }
        let Some(forwarded_callee) = super::condition_forwarded_callee(
            proto,
            cfg,
            dataflow,
            node,
            phi.id,
            use_site.instr,
            node_id == entry,
        ) else {
            continue;
        };
        let plan = super::ConditionValuePlan {
            phi: phi.id,
            consumer: truthy_consumer,
            use_instr: use_site.instr,
            negated: !raw_truthy_value,
            forwarded_callee,
        };
        if matched.replace(plan).is_some() {
            return None;
        }
    }
    matched
}

fn index_condition_values(
    phi_count: usize,
    conditions: &[super::ConditionPlan],
) -> Result<Vec<Option<(super::ConditionPlanId, super::ConditionNodeId)>>, StructureError> {
    let mut by_phi = vec![None; phi_count];
    for (condition_index, condition) in conditions.iter().enumerate() {
        let condition_id = super::ConditionPlanId(condition_index);
        for node in &condition.nodes {
            let Some(value) = node.materialized_value else {
                continue;
            };
            let slot = by_phi.get_mut(value.phi.index()).ok_or_else(|| {
                StructureError::invalid("condition value references a missing phi")
            })?;
            if slot.replace((condition_id, node.id)).is_some() {
                return Err(StructureError::invalid(
                    "condition value phi has multiple frozen owners",
                ));
            }
        }
    }
    Ok(by_phi)
}

fn index_absorbed_condition_blocks(
    block_count: usize,
    conditions: &[super::ConditionPlan],
) -> Result<Vec<Option<super::ConditionPlanId>>, StructureError> {
    let mut by_block = vec![None; block_count];
    for (condition_index, condition) in conditions.iter().enumerate() {
        let condition_id = super::ConditionPlanId(condition_index);
        let entry = condition.header().ok_or_else(|| {
            StructureError::invalid("condition plan has no entry block while building its index")
        })?;
        for block in condition.blocks().filter(|block| *block != entry) {
            let slot = by_block.get_mut(block.index()).ok_or_else(|| {
                StructureError::invalid("condition plan references a block outside the arena")
            })?;
            if slot.replace(condition_id).is_some() {
                return Err(StructureError::invalid(
                    "one block is absorbed by multiple condition plans",
                ));
            }
        }
    }
    Ok(by_block)
}

fn freeze_value_decision(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    evidence: &super::ValueDecisionPlanInput,
) -> Result<super::ValueDecisionPlan, StructureError> {
    use crate::structure::ShortCircuitNodeRef;

    let candidate = &evidence.candidate;
    let ShortCircuitExit::ValueMerge(merge) = candidate.exit else {
        return Err(StructureError::invalid(
            "selected value decision does not have a merge exit",
        ));
    };
    let result_phi = candidate
        .result_phi_id
        .ok_or_else(|| StructureError::invalid("value decision is missing its result phi"))?;
    let result_reg = candidate
        .result_reg
        .ok_or_else(|| StructureError::invalid("value decision is missing its result register"))?;
    let phi = dataflow
        .phi_candidate(result_phi)
        .ok_or_else(|| StructureError::invalid("value decision references a missing result phi"))?;
    if phi.block != merge || phi.reg != result_reg {
        return Err(StructureError::invalid(
            "value decision result identity contradicts its merge phi",
        ));
    }
    if candidate.entry.index() >= candidate.nodes.len() {
        return Err(StructureError::invalid(
            "value decision entry references a missing node",
        ));
    }

    let mut leaf_by_block = BTreeMap::new();
    let mut leaf_evidence = Vec::with_capacity(candidate.value_incomings.len());
    for incoming in &candidate.value_incomings {
        if !candidate.blocks.contains(&incoming.pred)
            || dataflow.block_exit_value(incoming.pred, result_reg) != incoming.value
        {
            return Err(StructureError::invalid(
                "value decision leaf contradicts frozen SSA facts",
            ));
        }
        if incoming.latest_local_def.is_some_and(|def| {
            dataflow.def_block(def) != incoming.pred
                || dataflow.def_reg(def) != result_reg
                || SsaValue::Def(def) != incoming.value
        }) {
            return Err(StructureError::invalid(
                "value decision leaf local definition is stale",
            ));
        }
        let id = super::ValueDecisionLeafId(leaf_evidence.len());
        if leaf_by_block.insert(incoming.pred, id).is_some() {
            return Err(StructureError::invalid(
                "value decision has duplicate leaf identities",
            ));
        }
        leaf_evidence.push(incoming);
    }
    let mut leaf_bindings = vec![None; leaf_evidence.len()];
    let mut route_edges = BTreeSet::new();
    let mut nodes = Vec::with_capacity(candidate.nodes.len());
    for (index, node) in candidate.nodes.iter().enumerate() {
        if node.id != ShortCircuitNodeRef(index) || !candidate.blocks.contains(&node.header) {
            return Err(StructureError::invalid(
                "value decision node identity is not dense",
            ));
        }
        let predicate_ref = cfg
            .blocks
            .get(node.header.index())
            .and_then(|block| block.instrs.last())
            .ok_or_else(|| StructureError::invalid("value decision node is empty"))?;
        let Some(LowInstr::Branch(predicate)) = proto.instrs.get(predicate_ref.index()) else {
            return Err(StructureError::invalid(
                "value decision node has no branch predicate",
            ));
        };
        let truthy = freeze_value_decision_arc(
            proto,
            cfg,
            dataflow,
            candidate,
            phi,
            node,
            predicate_ref,
            predicate,
            true,
            &node.truthy,
            &leaf_by_block,
            &leaf_evidence,
            &mut leaf_bindings,
        )?;
        let falsy = freeze_value_decision_arc(
            proto,
            cfg,
            dataflow,
            candidate,
            phi,
            node,
            predicate_ref,
            predicate,
            false,
            &node.falsy,
            &leaf_by_block,
            &leaf_evidence,
            &mut leaf_bindings,
        )?;
        route_edges.extend(truthy.route.iter().copied());
        route_edges.extend(falsy.route.iter().copied());
        nodes.push(super::ValueDecisionNodePlan {
            id: super::ValueDecisionNodeId(index),
            block: node.header,
            predicate: predicate_ref,
            predicate_negated: predicate.cond.negated,
            truthy,
            falsy,
        });
    }

    let mut leaves = Vec::with_capacity(leaf_evidence.len());
    let mut terminal_edges = BTreeSet::new();
    for (index, (evidence, binding)) in leaf_evidence.into_iter().zip(leaf_bindings).enumerate() {
        let (terminal_edge, physical_pred, physical_value) = binding.ok_or_else(|| {
            StructureError::invalid("value decision has an unreachable frozen leaf")
        })?;
        terminal_edges.insert(terminal_edge);
        leaves.push(super::ValueDecisionLeafPlan {
            id: super::ValueDecisionLeafId(index),
            block: evidence.pred,
            value: evidence.value,
            latest_local_def: evidence.latest_local_def,
            terminal_edge,
            physical_pred,
            physical_value,
        });
    }

    let phi_edges = phi
        .incoming
        .iter()
        .filter(|incoming| incoming.value != SsaValue::Phi(phi.id))
        .map(|incoming| {
            incoming.edge.ok_or_else(|| {
                StructureError::invalid("value decision result phi has a synthetic incoming")
            })
        })
        .collect::<Result<BTreeSet<_>, StructureError>>()?;
    if terminal_edges != phi_edges {
        return Err(StructureError::invalid(
            "value decision leaves do not cover every physical result incoming",
        ));
    }
    let expected_edges = candidate
        .blocks
        .iter()
        .flat_map(|block| cfg.succs[block.index()].iter().copied())
        .filter(|edge| cfg.reachable_blocks.contains(&cfg.edges[edge.index()].to))
        .collect::<BTreeSet<_>>();
    if route_edges != expected_edges {
        return Err(StructureError::invalid(
            "value decision routes do not cover its closed CFG subgraph",
        ));
    }
    let shared_exit_action = leaves
        .first()
        .map(|leaf| leaf.terminal_edge)
        .ok_or_else(|| StructureError::invalid("value decision has no result leaf"))?;
    Ok(super::ValueDecisionPlan {
        entry: super::ValueDecisionNodeId(candidate.entry.index()),
        nodes,
        leaves,
        blocks: candidate.blocks.iter().copied().collect(),
        merge,
        shared_exit_action,
        result_phi,
        absorbed_phis: Vec::new(),
        result_reg,
    })
}

fn assign_absorbed_value_phis(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    decisions: &mut [super::ValueDecisionPlan],
) -> Result<(), StructureError> {
    let mut owner_by_edge = vec![None; cfg.edges.len()];
    for (index, decision) in decisions.iter().enumerate() {
        let owner = super::ValueDecisionPlanId(index);
        for block in &decision.blocks {
            for &edge in &cfg.succs[block.index()] {
                if !cfg.reachable_blocks.contains(&cfg.edges[edge.index()].to) {
                    continue;
                }
                let slot = owner_by_edge.get_mut(edge.index()).ok_or_else(|| {
                    StructureError::invalid(
                        "value decision references an edge outside the CFG arena",
                    )
                })?;
                if slot
                    .replace(owner)
                    .is_some_and(|existing| existing != owner)
                {
                    return Err(StructureError::invalid(
                        "one CFG edge is absorbed by multiple value decisions",
                    ));
                }
            }
        }
    }

    for phi in &dataflow.phi_candidates {
        let Some(first_edge) = phi.incoming.first().and_then(|incoming| incoming.edge) else {
            continue;
        };
        let Some(owner) = owner_by_edge[first_edge.index()] else {
            continue;
        };
        if phi.id == decisions[owner.index()].result_phi
            || !phi.incoming.iter().all(|incoming| {
                incoming
                    .edge
                    .is_some_and(|edge| owner_by_edge[edge.index()] == Some(owner))
            })
        {
            continue;
        }
        decisions[owner.index()].absorbed_phis.push(phi.id);
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn freeze_value_decision_arc(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    candidate: &crate::structure::ShortCircuitCandidate,
    phi: &crate::structure::PhiCandidate,
    node: &crate::structure::ShortCircuitNode,
    predicate_ref: InstrRef,
    predicate: &crate::transformer::BranchInstr,
    semantic_truthy: bool,
    raw_target: &crate::structure::ShortCircuitTarget,
    leaf_by_block: &BTreeMap<BlockRef, super::ValueDecisionLeafId>,
    leaf_evidence: &[&crate::structure::ShortCircuitValueIncoming],
    leaf_bindings: &mut [Option<(EdgeRef, BlockRef, SsaValue)>],
) -> Result<super::ValueDecisionArcPlan, StructureError> {
    use crate::structure::ShortCircuitTarget;

    let result_reg = candidate
        .result_reg
        .ok_or_else(|| StructureError::invalid("value decision has no result register"))?;
    let target = match raw_target {
        ShortCircuitTarget::Node(next) => {
            if next.index() >= candidate.nodes.len() {
                return Err(StructureError::invalid(
                    "value decision edge references a missing node",
                ));
            }
            super::ValueDecisionTarget::Node(super::ValueDecisionNodeId(next.index()))
        }
        ShortCircuitTarget::Value(block) => {
            let leaf = leaf_by_block.get(block).copied().ok_or_else(|| {
                StructureError::invalid("value decision target has no frozen value leaf")
            })?;
            let evidence = leaf_evidence.get(leaf.index()).ok_or_else(|| {
                StructureError::invalid("value decision target has no leaf evidence")
            })?;
            if super::value_leaf_is_current(
                proto,
                dataflow,
                predicate_ref,
                predicate,
                result_reg,
                evidence.value,
                evidence.latest_local_def,
            ) {
                super::ValueDecisionTarget::CurrentValue(leaf)
            } else {
                super::ValueDecisionTarget::Leaf(leaf)
            }
        }
        ShortCircuitTarget::TruthyExit | ShortCircuitTarget::FalsyExit => {
            return Err(StructureError::invalid(
                "control exit reached a value decision",
            ));
        }
    };

    let (branch_true, branch_false) = cfg
        .branch_edges(node.header)
        .ok_or_else(|| StructureError::invalid("value decision node is not a CFG branch"))?;
    let physical_truthy = if predicate.cond.negated {
        branch_false
    } else {
        branch_true
    };
    let first = if semantic_truthy {
        physical_truthy
    } else if physical_truthy == branch_true {
        branch_false
    } else {
        branch_true
    };
    let polarity = match cfg.edges[first.index()].kind {
        EdgeKind::BranchTrue => super::ConditionArcPolarity::BranchTrue,
        EdgeKind::BranchFalse => super::ConditionArcPolarity::BranchFalse,
        _ => {
            return Err(StructureError::invalid(
                "value decision route does not start with a branch edge",
            ));
        }
    };
    let endpoint = match target {
        super::ValueDecisionTarget::Node(next) => candidate.nodes[next.index()].header,
        super::ValueDecisionTarget::Leaf(_) | super::ValueDecisionTarget::CurrentValue(_) => {
            phi.block
        }
    };
    let mut route = vec![first];
    let mut visited = BTreeSet::from([node.header]);
    loop {
        let last = route
            .last()
            .copied()
            .ok_or_else(|| StructureError::invalid("value decision route is empty"))?;
        let current = cfg
            .edges
            .get(last.index())
            .ok_or_else(|| StructureError::invalid("value decision route left the edge arena"))?
            .to;
        if current == endpoint {
            break;
        }
        if !candidate.blocks.contains(&current) || !visited.insert(current) {
            return Err(StructureError::invalid(
                "value decision route leaves or cycles inside its frozen subgraph",
            ));
        }
        let mut outgoing = cfg.succs[current.index()]
            .iter()
            .copied()
            .filter(|edge| cfg.reachable_blocks.contains(&cfg.edges[edge.index()].to));
        let next = outgoing.next().ok_or_else(|| {
            StructureError::invalid("value decision route ends before its declared target")
        })?;
        if outgoing.next().is_some() {
            return Err(StructureError::invalid(
                "value decision connector has multiple reachable successors",
            ));
        }
        route.push(next);
    }

    if let super::ValueDecisionTarget::Leaf(leaf) | super::ValueDecisionTarget::CurrentValue(leaf) =
        target
    {
        let evidence = leaf_evidence.get(leaf.index()).ok_or_else(|| {
            StructureError::invalid("value decision target references a missing leaf")
        })?;
        if evidence.pred != node.header
            && !route
                .iter()
                .any(|edge| cfg.edges[edge.index()].to == evidence.pred)
        {
            return Err(StructureError::invalid(
                "value decision route does not pass through its logical value leaf",
            ));
        }
        let terminal_edge = *route
            .last()
            .ok_or_else(|| StructureError::invalid("value decision route is empty"))?;
        let physical_pred = cfg.edges[terminal_edge.index()].from;
        let incoming = phi
            .incoming
            .iter()
            .find(|incoming| incoming.edge == Some(terminal_edge))
            .ok_or_else(|| {
                StructureError::invalid(
                    "value decision terminal edge has no physical result incoming",
                )
            })?;
        if incoming.pred != Some(physical_pred)
            || !dataflow.value_contains(incoming.value, evidence.value)
        {
            return Err(StructureError::invalid(
                "value decision physical incoming does not contain its logical leaf value",
            ));
        }
        let binding = (terminal_edge, physical_pred, incoming.value);
        let slot = leaf_bindings.get_mut(leaf.index()).ok_or_else(|| {
            StructureError::invalid("value decision leaf binding is outside the arena")
        })?;
        if slot.is_some_and(|existing| existing != binding) {
            return Err(StructureError::invalid(
                "value decision leaf reaches multiple physical result incomings",
            ));
        }
        *slot = Some(binding);
    }

    Ok(super::ValueDecisionArcPlan {
        polarity,
        route,
        target,
    })
}

fn index_value_decisions(
    phi_count: usize,
    decisions: &[super::ValueDecisionPlan],
) -> Result<Vec<Option<super::ValueDecisionPlanId>>, StructureError> {
    let mut by_phi = vec![None; phi_count];
    for (index, decision) in decisions.iter().enumerate() {
        let id = super::ValueDecisionPlanId(index);
        for phi in
            std::iter::once(decision.result_phi).chain(decision.absorbed_phis.iter().copied())
        {
            let slot = by_phi.get_mut(phi.index()).ok_or_else(|| {
                StructureError::invalid("value decision references a phi outside the arena")
            })?;
            if slot.replace(id).is_some() {
                return Err(StructureError::invalid(
                    "one phi has multiple value decision owners",
                ));
            }
        }
    }
    Ok(by_phi)
}

#[allow(clippy::too_many_arguments)]
fn freeze_condition_arc(
    cfg: &Cfg,
    condition: &crate::structure::common::ShortCircuitCandidate,
    arc: &crate::structure::short_circuit::ConditionArcEvidence,
    truthy_block: BlockRef,
    falsy_block: BlockRef,
    truthy_edges: &mut Vec<EdgeRef>,
    falsy_edges: &mut Vec<EdgeRef>,
    edge_plans: Option<&[EdgePlan]>,
) -> Result<super::ConditionArcPlan, StructureError> {
    let source = condition.nodes.get(arc.source.index()).ok_or_else(|| {
        StructureError::invalid("condition route references a missing source node")
    })?;
    let first = arc
        .edges
        .first()
        .copied()
        .ok_or_else(|| StructureError::invalid("condition route is empty"))?;
    let first_edge = cfg
        .edges
        .get(first.index())
        .ok_or_else(|| StructureError::invalid("condition route references a missing CFG edge"))?;
    if first_edge.from != source.header {
        return Err(StructureError::invalid(
            "condition route does not start at its source node",
        ));
    }
    let polarity = match first_edge.kind {
        EdgeKind::BranchTrue => super::ConditionArcPolarity::BranchTrue,
        EdgeKind::BranchFalse => super::ConditionArcPolarity::BranchFalse,
        _ => {
            return Err(StructureError::invalid(
                "condition route does not start with a physical branch edge",
            ));
        }
    };
    let mut connector_blocks = Vec::with_capacity(arc.edges.len().saturating_sub(1));
    for pair in arc.edges.windows(2) {
        let current = cfg.edges.get(pair[0].index()).ok_or_else(|| {
            StructureError::invalid("condition route references a missing CFG edge")
        })?;
        let next = cfg.edges.get(pair[1].index()).ok_or_else(|| {
            StructureError::invalid("condition route references a missing CFG edge")
        })?;
        if current.to != next.from {
            return Err(StructureError::invalid(
                "condition route contains non-contiguous CFG edges",
            ));
        }
        connector_blocks.push(current.to);
    }
    if connector_blocks != arc.connector_blocks {
        return Err(StructureError::invalid(
            "condition route connector blocks contradict the CFG path",
        ));
    }
    let last =
        arc.edges.last().copied().ok_or_else(|| {
            StructureError::invalid("condition route is missing its terminal edge")
        })?;
    let transfer = condition_arc_transfer_edge(&arc.edges, edge_plans)?;
    let edge_target = cfg.edges[last.index()].to;
    let target = match &arc.target {
        crate::structure::common::ShortCircuitTarget::Node(node) => {
            let expected = condition.nodes.get(node.index()).ok_or_else(|| {
                StructureError::invalid("condition DAG references a missing node")
            })?;
            if edge_target != expected.header {
                return Err(StructureError::invalid(format!(
                    "condition DAG node edge contradicts the CFG: source=#{} target={:?} last={} cfg-to=#{} expected=#{}",
                    source.header.index(),
                    arc.target,
                    last,
                    edge_target.index(),
                    expected.header.index(),
                )));
            }
            super::ConditionTarget::Node(super::ConditionNodeId(node.index()))
        }
        crate::structure::common::ShortCircuitTarget::TruthyExit => {
            if edge_target != truthy_block {
                return Err(StructureError::invalid(format!(
                    "condition truthy edge {last} from {} reaches {} instead of frozen exit {}",
                    first_edge.from, edge_target, truthy_block,
                )));
            }
            truthy_edges.push(transfer);
            super::ConditionTarget::Truthy
        }
        crate::structure::common::ShortCircuitTarget::FalsyExit => {
            if edge_target != falsy_block {
                return Err(StructureError::invalid(format!(
                    "condition falsy edge {last} from {} reaches {} instead of frozen exit {}",
                    first_edge.from, edge_target, falsy_block,
                )));
            }
            falsy_edges.push(transfer);
            super::ConditionTarget::Falsy
        }
        crate::structure::common::ShortCircuitTarget::Value(_) => Err(StructureError::invalid(
            "value-merge leaf reached a control condition",
        ))?,
    };
    Ok(super::ConditionArcPlan {
        source: super::ConditionNodeId(arc.source.index()),
        polarity,
        route: arc.edges.clone(),
        transfer,
        connector_blocks,
        target,
    })
}

fn condition_arc_transfer_edge(
    route: &[EdgeRef],
    edge_plans: Option<&[EdgePlan]>,
) -> Result<EdgeRef, StructureError> {
    let last = route
        .last()
        .copied()
        .ok_or_else(|| StructureError::invalid("condition route is empty"))?;
    let Some(edge_plans) = edge_plans else {
        return Ok(last);
    };
    let mut transfer = None;
    for edge in route {
        let edge_plan = edge_plans.get(edge.index()).ok_or_else(|| {
            StructureError::invalid("condition route references a missing final edge plan")
        })?;
        let inert = edge_plan.action_placement == EdgeActionPlacement::BeforeTransfer
            && edge_plan.forward_route.is_none()
            && matches!(
                edge_plan.transfer,
                EdgeTransfer::Fallthrough
                    | EdgeTransfer::BranchArm(super::BranchArm::Truthy | super::BranchArm::Falsy)
            );
        if !inert && transfer.replace(*edge).is_some() {
            return Err(StructureError::invalid(
                "condition route contains multiple executable edge transfers",
            ));
        }
    }
    Ok(transfer.unwrap_or(last))
}

fn freeze_branch_payload(
    cfg: &Cfg,
    edge_plans: &[EdgePlan],
    evidence: &super::BranchPlanInput,
    condition: super::ConditionPlanId,
    condition_plan: Option<&super::ConditionPlan>,
    single_pass_exit: Option<BlockRef>,
) -> Result<super::BranchPlanData, StructureError> {
    let condition_plan = condition_plan.ok_or_else(|| {
        StructureError::invalid("selected branch is missing its frozen condition plan")
    })?;
    let (truthy, falsy) = (condition_plan.truthy, condition_plan.falsy);
    let truthy_target =
        condition_transfer_target(cfg, condition_plan, truthy).ok_or_else(|| {
            StructureError::invalid("selected branch truthy transfer has no terminal condition arc")
        })?;
    let falsy_target = condition_transfer_target(cfg, condition_plan, falsy).ok_or_else(|| {
        StructureError::invalid("selected branch falsy transfer has no terminal condition arc")
    })?;
    let then_is_truthy = resolve_branch_then_polarity(
        &evidence.branch,
        truthy_target,
        falsy_target,
        condition_plan
            .blocks()
            .any(|block| block == evidence.branch.then_entry),
        single_pass_exit,
    )
    .ok_or_else(|| {
        StructureError::invalid(format!(
            "selected branch arm does not match its condition exits: header=#{} then-entry=#{} truthy-edge={} truthy-target=#{} falsy-edge={} falsy-target=#{}",
            evidence.branch.header.index(),
            evidence.branch.then_entry.index(),
            truthy,
            truthy_target.index(),
            falsy,
            falsy_target.index(),
        ))
    })?;
    let (condition_inverted, then_edge, else_edge) = if then_is_truthy {
        (false, truthy, falsy)
    } else {
        (true, falsy, truthy)
    };
    for edge in [then_edge, else_edge] {
        if edge_plans.get(edge.index()).is_none() {
            return Err(StructureError::invalid(
                "selected branch references a missing final edge plan",
            ));
        }
    }
    Ok(super::BranchPlanData {
        header: evidence.branch.header,
        kind: evidence.branch.kind,
        condition,
        condition_inverted,
        then_edge,
        else_edge,
        continuation: evidence.branch.merge,
        value_plan: evidence
            .value_merge
            .as_ref()
            .map(|value| super::BranchValuePlan {
                merge: value.merge,
                values: value.values.clone(),
            }),
    })
}

fn condition_transfer_target(
    cfg: &Cfg,
    condition: &super::ConditionPlan,
    transfer: EdgeRef,
) -> Option<BlockRef> {
    condition
        .nodes
        .iter()
        .flat_map(|node| node.arcs.iter())
        .find(|arc| {
            arc.transfer == transfer
                && matches!(
                    arc.target,
                    super::ConditionTarget::Truthy | super::ConditionTarget::Falsy
                )
        })
        .and_then(|arc| arc.route.last())
        .and_then(|edge| cfg.edges.get(edge.index()))
        .map(|edge| edge.to)
}

fn resolve_branch_then_polarity(
    branch: &BranchCandidate,
    truthy: BlockRef,
    falsy: BlockRef,
    then_entry_is_condition_block: bool,
    single_pass_exit: Option<BlockRef>,
) -> Option<bool> {
    if branch.then_entry == truthy {
        return Some(true);
    }
    if branch.then_entry == falsy {
        return Some(false);
    }
    if !then_entry_is_condition_block {
        return None;
    }

    // 短路折叠后，旧候选的 then_entry 可能成为 condition 内部节点。单臂分支的
    // continuation 才是此时可靠的边界：另一出口必须是源码 arm，不能继续沿用折叠前
    // 针对首个物理 branch 的 invert_hint。
    if branch.else_entry.is_none() {
        for boundary in [single_pass_exit, branch.merge].into_iter().flatten() {
            match (truthy == boundary, falsy == boundary) {
                (true, false) => return Some(false),
                (false, true) => return Some(true),
                _ => {}
            }
        }
    }
    Some(!branch.invert_hint)
}

fn normalize_effectful_unknown_loop_conditions(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    input: &mut FinalPlanInput,
    partitions: &[LoopPartitions],
) -> Result<bool, StructureError> {
    let mut while_true_guards = Vec::new();
    let mut loop_header_guards = Vec::new();
    let mut rewrites = Vec::new();
    for (loop_index, loop_) in input.loops.iter().enumerate() {
        let partition = partitions
            .get(loop_index)
            .ok_or_else(|| StructureError::invalid("selected loop has no frozen partitions"))?;
        if loop_.candidate.kind_hint == crate::structure::LoopKindHint::WhileTrueLike
            && partition.control.is_empty()
            && let Some(continuation) = partition.continuation
            && let Some((branch, condition)) =
                input
                    .branches
                    .iter()
                    .enumerate()
                    .find_map(|(index, branch)| {
                        (branch.branch.header == loop_.candidate.header)
                            .then_some(branch.condition)
                            .flatten()
                            .and_then(|condition| {
                                input
                                    .conditions
                                    .get(condition.index())
                                    .map(|condition| (index, condition))
                            })
                    })
            && let ShortCircuitExit::BranchExit { truthy, falsy } = condition.candidate.exit
        {
            let body = match (truthy == continuation, falsy == continuation) {
                (true, false) if partition.body.contains(&falsy) => Some(falsy),
                (false, true) if partition.body.contains(&truthy) => Some(truthy),
                (true, true) | (false, false) | (true, false) | (false, true) => None,
            };
            if let Some(body) = body {
                // `while true; if condition then break end` 的编译结果会把整个短路 DAG
                // 绑定到 header 上的早期 local-join candidate。最终 condition 出口已经
                // 明确给出 break/body，直接冻结为包住 body tail 的单臂 guard。
                while_true_guards.push((branch, continuation, body));
                continue;
            }
        }
        if loop_.candidate.kind_hint != crate::structure::LoopKindHint::Unknown
            || !partition.control.is_empty()
        {
            continue;
        }
        let Some(condition_id) = loop_.condition else {
            continue;
        };
        let condition = input.conditions.get(condition_id.index()).ok_or_else(|| {
            StructureError::invalid(format!(
                "loop #{loop_index} references missing condition #{}",
                condition_id.index()
            ))
        })?;
        let ShortCircuitExit::BranchExit { truthy, falsy } = condition.candidate.exit else {
            continue;
        };
        if truthy == condition.candidate.header || falsy == condition.candidate.header {
            let remainder = if truthy == condition.candidate.header {
                falsy
            } else {
                truthy
            };
            if partition.body.contains(&remainder)
                && let Some(branch) = input.branches.iter().position(|branch| {
                    branch.branch.header == condition.candidate.header
                        && branch.condition == Some(condition_id)
                })
            {
                loop_header_guards.push((branch, remainder));
            }
            continue;
        }
        if !partition.body.contains(&truthy) || !partition.body.contains(&falsy) {
            continue;
        }

        let Some(prefix_branch) = input.branches.iter().position(|branch| {
            branch.branch.header == condition.candidate.header
                && branch.condition == Some(condition_id)
        }) else {
            continue;
        };
        let branch = &input.branches[prefix_branch].branch;
        if branch.else_entry.is_some() {
            continue;
        }
        // Unknown 条件的两个出口都还在 natural loop 内时，真正的 body 出口必须支配
        // 某条已冻结 backedge。这个 dominator interval 查询等价于旧的“能否到达
        // latch”探测，但不会为每个 loop 重跑图搜索；local join 仅作为直接边界证据。
        let reaches_backedge = |target| {
            loop_.candidate.backedges.iter().any(|edge| {
                cfg.edges
                    .get(edge.index())
                    .is_some_and(|edge| graph_facts.dominates(target, edge.from))
            })
        };
        let (remainder, body) = match (reaches_backedge(truthy), reaches_backedge(falsy)) {
            (true, false) => (falsy, truthy),
            (false, true) => (truthy, falsy),
            (true, true) | (false, false) => match branch.merge {
                Some(merge) if merge == truthy => (falsy, truthy),
                Some(merge) if merge == falsy => (truthy, falsy),
                Some(_) | None => continue,
            },
        };
        if !loop_.candidate.backedges.iter().any(|edge| {
            cfg.edges
                .get(edge.index())
                .is_some_and(|edge| graph_facts.dominates(body, edge.from))
        }) {
            continue;
        }
        let terminal_branches = partition
            .continuation
            .into_iter()
            .flat_map(|continuation| {
                input
                    .branches
                    .iter()
                    .enumerate()
                    .filter_map(move |(index, branch)| {
                        let header = branch.branch.header;
                        if header == condition.candidate.header
                            || !graph_facts.dominates(remainder, header)
                            || graph_facts.dominates(body, header)
                        {
                            return None;
                        }
                        let (truthy_edge, falsy_edge) = cfg.branch_edges(header)?;
                        let truthy_target = cfg.edges[truthy_edge.index()].to;
                        let falsy_target = cfg.edges[falsy_edge.index()].to;
                        match (truthy_target, falsy_target) {
                            (target, inside) | (inside, target)
                                if target == continuation && inside == body =>
                            {
                                Some((index, target, inside))
                            }
                            _ => None,
                        }
                    })
            })
            .collect::<Vec<_>>();
        rewrites.push((prefix_branch, remainder, body, terminal_branches));
    }

    let changed =
        !while_true_guards.is_empty() || !loop_header_guards.is_empty() || !rewrites.is_empty();
    for (branch, escape, body) in while_true_guards {
        rewrite_one_arm_branch(graph_facts, &mut input.branches[branch], escape, body);
    }
    for (branch, remainder) in loop_header_guards {
        rewrite_loop_header_guard(&mut input.branches[branch], remainder);
    }
    for (prefix_branch, remainder, body, terminal_branches) in rewrites {
        rewrite_one_arm_branch(
            graph_facts,
            &mut input.branches[prefix_branch],
            remainder,
            body,
        );
        for (index, exit, continuation) in terminal_branches {
            rewrite_one_arm_branch(graph_facts, &mut input.branches[index], exit, continuation);
        }
    }
    Ok(changed)
}

fn rewrite_loop_header_guard(branch: &mut super::BranchPlanInput, then_entry: BlockRef) {
    branch.branch.then_entry = then_entry;
    branch.branch.else_entry = None;
    branch.branch.merge = None;
    branch.branch.kind = BranchKind::IfThen;
    branch.branch.invert_hint = false;
    branch.value_merge = None;
    branch.region = None;
}

fn rewrite_one_arm_branch(
    graph_facts: &GraphFacts,
    branch: &mut super::BranchPlanInput,
    then_entry: BlockRef,
    merge: BlockRef,
) {
    branch.branch.then_entry = then_entry;
    branch.branch.else_entry = None;
    branch.branch.merge = Some(merge);
    branch.branch.kind = BranchKind::IfThen;
    branch.branch.invert_hint = false;
    branch.value_merge = None;
    branch.region = Some(BranchRegionFact::new(
        graph_facts,
        branch.branch.header,
        merge,
        BranchKind::IfThen,
        None,
    ));
}

fn build_regions(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    input: &FinalPlanInput,
    partitions: &[LoopPartitions],
) -> Result<RegionArena, StructureError> {
    let mut pending = Vec::new();
    let mut residuals = Vec::new();
    let mut unstructured_blocks = Vec::new();
    for (index, island) in input.unstructured.iter().enumerate() {
        let blocks = island.layout.as_ref().map_or_else(
            || island.fact.blocks.clone(),
            |layout| layout.blocks.clone(),
        );
        let blocks = reachable_nonempty_blocks(cfg, blocks);
        if !blocks.is_empty() {
            unstructured_blocks.push(blocks.clone());
            pending.push(PendingContainer::exact(
                ContainerKind::Island(index),
                blocks,
                graph_facts,
            )?);
        }
    }
    let island_prefix = if unstructured_blocks.is_empty() {
        None
    } else {
        let mut island_by_preorder = vec![false; graph_facts.dominator_tree.order.len()];
        for block in unstructured_blocks.iter().flatten() {
            let position = graph_facts
                .dominator_tree
                .preorder_index
                .get(block.index())
                .copied()
                .flatten()
                .ok_or_else(|| {
                    StructureError::invalid(format!(
                        "reachable island references block {block} outside dominator preorder"
                    ))
                })?;
            let slot = island_by_preorder.get_mut(position).ok_or_else(|| {
                StructureError::invalid("island block position exceeds dominator preorder")
            })?;
            *slot = true;
        }
        let mut prefix = Vec::with_capacity(island_by_preorder.len() + 1);
        prefix.push(0usize);
        for present in island_by_preorder {
            let count = prefix
                .last()
                .copied()
                .ok_or_else(|| StructureError::invalid("island prefix lost its initial count"))?
                .checked_add(usize::from(present))
                .ok_or_else(|| StructureError::invalid("island block count overflowed"))?;
            prefix.push(count);
        }
        Some(prefix)
    };

    for (index, branch) in input.branches.iter().enumerate() {
        let Some(region) = branch.region.as_ref() else {
            continue;
        };
        let Some(fence) = region.single_pass_fence.as_ref() else {
            continue;
        };
        let mut blocks = region
            .structured_blocks(graph_facts)
            .map_err(|block| {
                StructureError::invalid(format!(
                    "single-pass region references block {block} outside dominator preorder"
                ))
            })?
            .collect::<BTreeSet<_>>();
        blocks.insert(region.merge);
        let blocks = reachable_nonempty_blocks(cfg, blocks);
        let valid_tail = matches!(
            cfg.succs.get(region.merge.index()).map(Vec::as_slice),
            Some([edge]) if cfg.edges.get(edge.index()).is_some_and(|edge| edge.to == fence.exit)
        );
        let valid_escapes = !fence.escape_edges.is_empty()
            && fence.escape_edges.iter().all(|edge| {
                cfg.edges.get(edge.index()).is_some_and(|edge| {
                    blocks.contains(&edge.from)
                        && edge.from != region.merge
                        && edge.to == fence.exit
                })
            });
        if !valid_tail || !valid_escapes || !single_entry(cfg, &blocks, branch.branch.header) {
            continue;
        }
        pending.push(PendingContainer::exact(
            ContainerKind::SinglePass(super::BranchPlanId(index)),
            blocks,
            graph_facts,
        )?);
    }

    for (index, _) in input.loops.iter().enumerate() {
        let id = super::LoopPlanId(index);
        let blocks = partitions
            .get(index)
            .map_or_else(BTreeSet::new, |partition| {
                let mut blocks = partition.owned.clone();
                if let Some(normal_tail) = &partition.normal_tail {
                    blocks.extend(normal_tail.blocks.iter().copied());
                }
                blocks
            });
        let blocks = reachable_nonempty_blocks(cfg, blocks);
        if blocks.is_empty() {
            continue;
        }
        let partition = partitions
            .get(id.index())
            .ok_or_else(|| StructureError::invalid("selected loop has no frozen partitions"))?;
        let entry = partition
            .preheader
            .unwrap_or(input.loops[id.index()].candidate.header);
        if !single_entry(cfg, &blocks, entry) {
            push_residual_seed(&mut residuals, entry, blocks);
            continue;
        }
        pending.push(PendingContainer::exact(
            ContainerKind::Loop(id),
            blocks,
            graph_facts,
        )?);
    }

    let mut value_decision_blocks = BTreeSet::new();
    for (index, decision) in input.value_decisions.iter().enumerate() {
        let id = super::ValueDecisionPlanId(index);
        let blocks = reachable_nonempty_blocks(cfg, decision.candidate.blocks.clone());
        let decision = &input.value_decisions[id.index()].candidate;
        let ShortCircuitExit::ValueMerge(continuation) = decision.exit else {
            continue;
        };
        if blocks.is_empty()
            || blocks.contains(&continuation)
            || !single_entry(cfg, &blocks, decision.header)
            || !value_decision_is_closed(cfg, &blocks, continuation)
        {
            continue;
        }
        // 编译器会把 `a and b or c` 的控制子图压成“共享 tail + 跳过 tail”形状，
        // 与一次性 fence 的图形证据完全重合。闭合 ValueDecision 已证明所有 edge 和
        // result phi 都由表达式 DAG 消费，语义强于只描述控制跳出的 SinglePass；
        // 同一 block 集只能保留前者，不能让 fence 抢占 owner 后再把 decision 降成 goto。
        pending.retain(|candidate| {
            !matches!(candidate.kind, ContainerKind::SinglePass(_)) || candidate.blocks != blocks
        });
        value_decision_blocks.extend(blocks.iter().copied());
        pending.push(PendingContainer::exact(
            ContainerKind::ValueDecision(id),
            blocks,
            graph_facts,
        )?);
    }

    let loop_control_blocks = partitions
        .iter()
        .flat_map(|partition| partition.control.iter().copied())
        .collect::<BTreeSet<_>>();
    let mut claimed_condition_headers = BTreeSet::new();
    for (index, loop_) in input.loops.iter().enumerate() {
        if let Some(condition) = loop_
            .condition
            .and_then(|id| input.conditions.get(id.index()))
            .filter(|condition| {
                partitions.get(index).is_some_and(|partition| {
                    condition
                        .candidate
                        .blocks
                        .iter()
                        .all(|block| partition.control.contains(block))
                })
            })
        {
            claimed_condition_headers.extend(condition.candidate.blocks.iter().copied());
        }
    }
    for branch in &input.branches {
        if let Some(condition) = branch
            .condition
            .and_then(|id| input.conditions.get(id.index()))
        {
            claimed_condition_headers.extend(
                condition
                    .candidate
                    .blocks
                    .iter()
                    .copied()
                    .filter(|block| *block != branch.branch.header),
            );
        }
    }
    let mut loop_owned_by_block = vec![false; cfg.blocks.len()];
    for partition in partitions {
        for block in partition.owned.iter().copied().chain(
            partition
                .normal_tail
                .iter()
                .flat_map(|tail| tail.blocks.iter().copied()),
        ) {
            loop_owned_by_block[block.index()] = true;
        }
    }
    for (index, branch) in input.branches.iter().enumerate() {
        if loop_control_blocks.contains(&branch.branch.header)
            || claimed_condition_headers.contains(&branch.branch.header)
            || value_decision_blocks.contains(&branch.branch.header)
        {
            continue;
        }
        let id = super::BranchPlanId(index);
        if !loop_owned_by_block[branch.branch.header.index()]
            && let Some(ranges) = ordinary_branch_ranges(cfg, graph_facts, input, branch)?
        {
            let intersects_island = if let Some(prefix) = &island_prefix {
                preorder_ranges_intersect_prefix(&ranges, prefix)?
            } else {
                false
            };
            if !intersects_island {
                pending.push(PendingContainer::intervals(
                    ContainerKind::Branch(id),
                    ranges,
                    graph_facts,
                )?);
                continue;
            }
        }
        // branch-region evidence 只证明已识别的结构片段，不承诺穷尽整个 arm。
        // 最终 containment 必须从 header 的支配子树补齐，否则短路条件后的单臂
        // exit block 会掉到 branch sibling，原本有条件的 goto/break 将变成无条件。
        let normalize = |mut blocks: BTreeSet<BlockRef>| {
            blocks.insert(branch.branch.header);
            if let Some(condition) = branch
                .condition
                .and_then(|id| input.conditions.get(id.index()))
            {
                blocks.extend(condition.candidate.blocks.iter().copied());
            }
            for partition in partitions
                .iter()
                .filter(|partition| partition.owned.contains(&branch.branch.header))
            {
                let claimed = if partition.control.contains(&branch.branch.header) {
                    &partition.control
                } else if partition.preheader == Some(branch.branch.header) {
                    continue;
                } else {
                    &partition.body
                };
                blocks.retain(|block| claimed.contains(block));
            }
            // structured branch 必须由 header 单入口支配；共享 continuation 的 sibling
            // 只能由外层 region 持有，不能污染当前 branch containment。
            blocks.retain(|block| graph_facts.dominates(branch.branch.header, *block));
            blocks.retain(|block| branch_part(branch, input, graph_facts, *block).is_some());
            reachable_nonempty_blocks(cfg, blocks)
        };
        let evidence = branch
            .region
            .as_ref()
            .map(|region| {
                region
                    .structured_blocks(graph_facts)
                    .map(|blocks| blocks.collect::<BTreeSet<_>>())
                    .map_err(|block| {
                        StructureError::invalid(format!(
                            "branch region references block {block} outside dominator preorder"
                        ))
                    })
            })
            .transpose()?;
        let mut expanded = branch_default_blocks(graph_facts, branch);
        if let Some(evidence) = &evidence {
            expanded.extend(evidence);
        }
        let mut blocks = normalize(expanded);
        if !single_entry(cfg, &blocks, branch.branch.header)
            && let Some(evidence) = evidence
        {
            // 一个 default arm target 也可能是嵌套结构的共享 continuation。此时扩展
            // 会制造假多入口；退回已验证 evidence，而不是把可规约图升级成 island。
            let evidence = normalize(evidence);
            if single_entry(cfg, &evidence, branch.branch.header) {
                blocks = evidence;
            }
        }
        let branch = &input.branches[id.index()];
        if blocks.is_empty() {
            continue;
        }
        if unstructured_blocks.iter().any(|island| {
            island.is_subset(&blocks)
                && branch_part_for_blocks(branch, input, graph_facts, island).is_none()
        }) {
            // island 内部图可以跨越一个表面 branch 的两条 arm；这种 branch 不能再做
            // island 的 containment parent，否则树 ownership 与 island 的真实图边矛盾。
            continue;
        }
        if !single_entry(cfg, &blocks, branch.branch.header) {
            push_residual_seed(&mut residuals, branch.branch.header, blocks);
            continue;
        }
        pending.push(PendingContainer::exact(
            ContainerKind::Branch(id),
            blocks,
            graph_facts,
        )?);
    }

    if !unstructured_blocks.is_empty() {
        let mut islands_by_block = vec![Vec::new(); cfg.blocks.len()];
        for (island, blocks) in unstructured_blocks.iter().enumerate() {
            for block in blocks {
                islands_by_block[block.index()].push(island);
            }
        }
        let mut protected_pending = Vec::with_capacity(pending.len());
        for mut candidate in pending {
            if matches!(candidate.kind, ContainerKind::Island(_)) {
                protected_pending.push(candidate);
                continue;
            }
            let mut intersections = BTreeMap::<usize, usize>::new();
            for block in &candidate.blocks {
                for island in &islands_by_block[block.index()] {
                    *intersections.entry(*island).or_default() += 1;
                }
            }
            let crossed_islands = intersections
                .into_iter()
                .filter_map(|(island, intersection)| {
                    (intersection < unstructured_blocks[island].len()
                        && candidate.blocks.len() > intersection)
                        .then_some(island)
                })
                .collect::<Vec<_>>();
            for island in &crossed_islands {
                candidate
                    .blocks
                    .extend(unstructured_blocks[*island].iter().copied());
            }
            if !crossed_islands.is_empty() {
                push_residual_seed(
                    &mut residuals,
                    container_entry(candidate.kind, input, partitions),
                    candidate.blocks,
                );
            } else {
                protected_pending.push(candidate);
            }
        }
        pending = protected_pending;
    }

    pending.sort_by_key(|pending| {
        (
            Reverse(pending.block_count),
            Reverse(container_same_size_rank(pending.kind)),
            pending_kind_index(pending.kind),
        )
    });
    let mut specs = Vec::with_capacity(pending.len());
    let mut owners = RangeOwnerTree::new(graph_facts.dominator_tree.order.len());
    for candidate in pending {
        let kind = candidate.kind;
        match try_insert_candidate(&mut specs, &mut owners, candidate)? {
            InsertDisposition::Inserted => {}
            InsertDisposition::Rejected(_) if matches!(kind, ContainerKind::Island(_)) => {
                return Err(StructureError::invalid(format!(
                    "protected island #{} was rejected from containment",
                    pending_kind_index(kind)
                )));
            }
            InsertDisposition::Rejected(_) if matches!(kind, ContainerKind::ValueDecision(_)) => {}
            InsertDisposition::Rejected(candidate) => {
                let entry = match kind {
                    ContainerKind::Loop(id) => partitions[id.index()]
                        .preheader
                        .unwrap_or(input.loops[id.index()].candidate.header),
                    ContainerKind::SinglePass(id) | ContainerKind::Branch(id) => {
                        input.branches[id.index()].branch.header
                    }
                    ContainerKind::ValueDecision(_)
                    | ContainerKind::Island(_)
                    | ContainerKind::Residual(_) => continue,
                };
                push_residual_seed(
                    &mut residuals,
                    entry,
                    candidate.materialize_blocks(graph_facts)?,
                );
            }
        }
    }

    let mut dispositions = normalize_residual_specs(cfg, graph_facts, &mut specs, &residuals)?;
    let mut owner_by_block = build_container_topology(cfg, graph_facts, &mut specs)?;
    flatten_nested_unstructured_specs(&mut specs, &mut owner_by_block, &mut dispositions)?;
    validate_aggregate_seed_dispositions(cfg, input, &residuals, &specs, &dispositions)?;

    materialize_regions(cfg, graph_facts, input, partitions, specs, owner_by_block)
}

fn push_residual_seed(
    residuals: &mut Vec<ResidualSeed>,
    entry: BlockRef,
    blocks: BTreeSet<BlockRef>,
) {
    residuals.push(ResidualSeed {
        id: ResidualSeedId(residuals.len()),
        entry,
        blocks,
    });
}

fn materialize_regions(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    input: &FinalPlanInput,
    partitions: &[LoopPartitions],
    specs: Vec<ContainerSpec>,
    owner_by_block: Vec<Option<usize>>,
) -> Result<RegionArena, StructureError> {
    let root = RegionId(0);
    let mut regions = vec![Some(RegionPlan::Sequence {
        parent: None,
        children: Vec::new(),
    })];
    let mut slots = Vec::with_capacity(specs.len());
    for spec in &specs {
        let region = reserve(&mut regions);
        let slot = match spec.kind {
            ContainerKind::SinglePass(_) => ContainerSlots::SinglePass { region },
            ContainerKind::Branch(id) => {
                let condition = reserve_sequence(&mut regions, region);
                let then_arm = reserve_sequence(&mut regions, region);
                let else_arm = input.branches[id.index()]
                    .branch
                    .else_entry
                    .map(|_| reserve_sequence(&mut regions, region));
                ContainerSlots::Branch {
                    region,
                    condition,
                    then_arm,
                    else_arm,
                }
            }
            ContainerKind::Loop(id) => ContainerSlots::Loop {
                region,
                preheader: partitions[id.index()]
                    .preheader
                    .map(|_| reserve_sequence(&mut regions, region)),
                control: reserve_sequence(&mut regions, region),
                body: reserve_sequence(&mut regions, region),
                normal_tail: partitions[id.index()]
                    .normal_tail
                    .as_ref()
                    .map(|_| reserve_sequence(&mut regions, region)),
            },
            ContainerKind::ValueDecision(_) => ContainerSlots::ValueDecision { region },
            ContainerKind::Island(_) | ContainerKind::Residual(_) => {
                ContainerSlots::Island { region }
            }
        };
        slots.push(slot);
    }

    let mut sequence_items = vec![Vec::<(usize, RegionId)>::new(); regions.len()];
    let mut island_items = vec![Vec::<(usize, UnstructuredLayoutItem)>::new(); regions.len()];
    let mut island_regions = vec![false; regions.len()];
    for slot in &slots {
        if let ContainerSlots::Island { region } = slot {
            island_regions[region.index()] = true;
        }
    }
    let rank = block_ranks(cfg);
    let mut loop_region_by_plan = vec![root; input.loops.len()];
    let mut value_decision_region_by_plan = vec![root; input.value_decisions.len()];
    let mut single_pass_region_by_branch = vec![None; input.branches.len()];

    for (index, spec) in specs.iter().enumerate() {
        let slot = slots[index];
        let parent = attachment_for_container(
            spec.parent,
            spec,
            &specs,
            &slots,
            input,
            partitions,
            graph_facts,
        )?;
        append_region(
            parent,
            slot.region(),
            spec.first_rank,
            &island_regions,
            &mut sequence_items,
            &mut island_items,
        )?;

        let plan = match (spec.kind, slot) {
            (ContainerKind::SinglePass(id), ContainerSlots::SinglePass { region }) => {
                single_pass_region_by_branch[id.index()] = Some(region);
                RegionPlan::Sequence {
                    parent: Some(parent),
                    children: Vec::new(),
                }
            }
            (
                ContainerKind::Branch(id),
                ContainerSlots::Branch {
                    region: _,
                    condition,
                    then_arm,
                    else_arm,
                },
            ) => {
                let branch = &input.branches[id.index()].branch;
                RegionPlan::Branch {
                    parent,
                    plan: id,
                    entry: branch.header,
                    condition,
                    then_arm,
                    else_arm,
                    continuation: branch.merge,
                }
            }
            (
                ContainerKind::Loop(id),
                ContainerSlots::Loop {
                    preheader,
                    control,
                    body,
                    normal_tail,
                    ..
                },
            ) => {
                loop_region_by_plan[id.index()] = slot.region();
                let loop_ = &input.loops[id.index()];
                let partition = &partitions[id.index()];
                RegionPlan::Loop {
                    parent,
                    plan: id,
                    entry: partition.preheader.unwrap_or(loop_.candidate.header),
                    preheader,
                    control,
                    body,
                    normal_tail,
                }
            }
            (ContainerKind::ValueDecision(id), ContainerSlots::ValueDecision { .. }) => {
                let decision = &input.value_decisions[id.index()].candidate;
                let ShortCircuitExit::ValueMerge(continuation) = decision.exit else {
                    return Err(StructureError::invalid(
                        "value decision container does not have a value merge",
                    ));
                };
                value_decision_region_by_plan[id.index()] = slot.region();
                RegionPlan::ValueDecision {
                    parent,
                    plan: id,
                    entry: decision.header,
                    continuation,
                }
            }
            (ContainerKind::Island(island), ContainerSlots::Island { .. }) => {
                RegionPlan::Unstructured {
                    parent,
                    entry: input.unstructured[island].fact.entry,
                    entries: Vec::new(),
                    layout: Vec::new(),
                    exits: Vec::new(),
                }
            }
            (ContainerKind::Residual(entry), ContainerSlots::Island { .. }) => {
                RegionPlan::Unstructured {
                    parent,
                    entry,
                    entries: Vec::new(),
                    layout: Vec::new(),
                    exits: Vec::new(),
                }
            }
            _ => return Err(StructureError::invalid("container slot kind mismatch")),
        };
        regions[slot.region().index()] = Some(plan);
    }

    let mut region_by_block = vec![None; cfg.blocks.len()];
    for block in cfg
        .block_order
        .iter()
        .copied()
        .filter(|block| cfg.reachable_blocks.contains(block))
    {
        let owner = owner_by_block[block.index()];
        if owner.is_some_and(|index| {
            matches!(
                specs[index].kind,
                ContainerKind::Island(_)
                    | ContainerKind::Residual(_)
                    | ContainerKind::ValueDecision(_)
            )
        }) {
            let owner = owner.ok_or_else(|| {
                StructureError::invalid(format!("aggregate block {block} has no container owner"))
            })?;
            let region = slots[owner].region();
            region_by_block[block.index()] = Some(region);
            if matches!(
                specs[owner].kind,
                ContainerKind::Island(_) | ContainerKind::Residual(_)
            ) {
                island_items[region.index()]
                    .push((rank[block.index()], UnstructuredLayoutItem::Block(block)));
            }
            continue;
        }
        let parent =
            attachment_for_block(owner, block, &specs, &slots, input, partitions, graph_facts)?;
        let region = reserve(&mut regions);
        if sequence_items.len() < regions.len() {
            sequence_items.push(Vec::new());
            island_items.push(Vec::new());
        }
        regions[region.index()] = Some(RegionPlan::Block { parent, block });
        region_by_block[block.index()] = Some(region);
        sequence_items[parent.index()].push((rank[block.index()], region));
    }

    for (index, items) in sequence_items.iter_mut().enumerate() {
        items.sort_by_key(|(rank, region)| (*rank, region.index()));
        if let Some(RegionPlan::Sequence { children, .. }) = regions[index].as_mut() {
            *children = items.iter().map(|(_, region)| *region).collect();
        }
    }
    for (index, items) in island_items.iter_mut().enumerate() {
        items.sort_by_key(|(rank, item)| {
            let tie = match item {
                UnstructuredLayoutItem::Block(block) => block.index(),
                UnstructuredLayoutItem::Region(region) => region.index(),
            };
            (*rank, tie)
        });
        if let Some(RegionPlan::Unstructured { layout, .. }) = regions[index].as_mut() {
            *layout = items.iter().map(|(_, item)| *item).collect();
        }
    }

    let mut regions = regions
        .into_iter()
        .enumerate()
        .map(|(index, region)| {
            region.ok_or_else(|| StructureError::invalid(format!("region #{index} was not filled")))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let navigation = RegionNavigation::build(cfg, root, &regions, &region_by_block)?;
    order_sequence_children_by_flow(cfg, graph_facts, &mut regions, &navigation)?;
    let mut ports = navigation.collect_island_ports(cfg, &regions)?;
    for (index, region) in regions.iter_mut().enumerate() {
        let RegionPlan::Unstructured { entries, exits, .. } = region else {
            continue;
        };
        *entries = std::mem::take(&mut ports.entries[index]);
        *exits = std::mem::take(&mut ports.exits[index]);
    }
    let mut single_passes = Vec::new();
    let mut single_pass_by_region = vec![None; regions.len()];
    for (branch_index, region) in single_pass_region_by_branch.into_iter().enumerate() {
        let Some(region) = region else {
            continue;
        };
        let branch = input.branches.get(branch_index).ok_or_else(|| {
            StructureError::invalid("single-pass mapping references missing branch evidence")
        })?;
        let branch_region = branch.region.as_ref().ok_or_else(|| {
            StructureError::invalid("single-pass mapping references missing branch region")
        })?;
        let fence = branch_region.single_pass_fence.as_ref().ok_or_else(|| {
            StructureError::invalid("single-pass mapping references missing fence evidence")
        })?;
        let id = super::SinglePassPlanId(single_passes.len());
        single_pass_by_region[region.index()] = Some(id);
        single_passes.push(super::SinglePassPlan {
            region,
            entry: branch.branch.header,
            tail: branch_region.merge,
            continuation: fence.exit,
            escape_edges: fence.escape_edges.iter().copied().collect(),
        });
    }
    Ok(RegionArena {
        regions,
        region_by_block,
        navigation,
        loop_region_by_plan,
        value_decision_region_by_plan,
        single_passes,
        single_pass_by_region,
        specs,
        slots,
    })
}

/// 物理指令顺序不是结构化 sequence 的执行顺序：编译器可以把 loop tail 放到 header
/// 之前，再用回边连接。这里按 sibling 之间真实存在的 CFG 边做稳定拓扑排序；若 sibling
/// 图本身含环，则它属于必须保留显式 transfer 的图形，继续使用稳定物理 layout。
fn order_sequence_children_by_flow(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    regions: &mut [RegionPlan],
    navigation: &RegionNavigation,
) -> Result<(), StructureError> {
    let mut is_backedge = vec![false; cfg.edges.len()];
    for edge in &graph_facts.backedges {
        is_backedge[edge.index()] = true;
    }
    let mut successors = vec![Vec::new(); regions.len()];
    let mut indegree = vec![0usize; regions.len()];
    for (edge_index, _edge) in cfg.edges.iter().enumerate() {
        if is_backedge[edge_index] {
            continue;
        }
        let Some(relation) = navigation.edge_relation(EdgeRef(edge_index)) else {
            continue;
        };
        let Some(owner) = relation.lca else {
            continue;
        };
        if !matches!(
            regions.get(owner.index()),
            Some(RegionPlan::Sequence { .. })
        ) {
            continue;
        }
        let Some(source) = relation.source_child else {
            continue;
        };
        let Some(target) = relation.target_child else {
            continue;
        };
        if source == target {
            continue;
        }
        successors[source.index()].push(target);
        indegree[target.index()] = indegree[target.index()]
            .checked_add(1)
            .ok_or_else(|| StructureError::invalid("sequence sibling indegree overflowed"))?;
    }

    for region in regions {
        let RegionPlan::Sequence { children, .. } = region else {
            continue;
        };
        if children.len() < 2 {
            continue;
        }
        let original = children.clone();
        let mut ready = original
            .iter()
            .copied()
            .filter(|child| indegree[child.index()] == 0)
            .collect::<VecDeque<_>>();
        let mut ordered = Vec::with_capacity(original.len());
        while let Some(child) = ready.pop_front() {
            ordered.push(child);
            for successor in &successors[child.index()] {
                let degree = indegree.get_mut(successor.index()).ok_or_else(|| {
                    StructureError::invalid("sequence successor is outside the region arena")
                })?;
                *degree = degree.checked_sub(1).ok_or_else(|| {
                    StructureError::invalid("sequence sibling indegree underflowed")
                })?;
                if *degree == 0 {
                    ready.push_back(*successor);
                }
            }
        }
        if ordered.len() == original.len() {
            *children = ordered;
        }
    }
    Ok(())
}

fn container_same_size_rank(kind: ContainerKind) -> u8 {
    match kind {
        ContainerKind::ValueDecision(_) => 0,
        ContainerKind::Branch(_) => 1,
        ContainerKind::SinglePass(_) => 2,
        ContainerKind::Loop(_) => 3,
        ContainerKind::Island(_) | ContainerKind::Residual(_) => 4,
    }
}

fn build_container_topology(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    specs: &mut [ContainerSpec],
) -> Result<Vec<Option<usize>>, StructureError> {
    let mut order = (0..specs.len()).collect::<Vec<_>>();
    order.sort_by_key(|index| {
        let spec = &specs[*index];
        (
            Reverse(spec.block_count),
            Reverse(container_same_size_rank(spec.kind)),
            *index,
        )
    });

    let mut owners = RangeOwnerTree::new(graph_facts.dominator_tree.order.len());
    for index in order {
        let RangeOwnerState::Uniform(parent) = owners.uniform_owner(&specs[index].ranges)? else {
            return Err(StructureError::invalid(format!(
                "container #{index} is not laminar at block {}",
                specs[index].representative
            )));
        };
        specs[index].parent = parent;
        owners.assign(&specs[index].ranges, index)?;
    }
    let preorder_owners = owners.materialize()?;
    let mut owner_by_block = vec![None; cfg.blocks.len()];
    for (position, owner) in preorder_owners.into_iter().enumerate() {
        let block = graph_facts
            .dominator_tree
            .order
            .get(position)
            .copied()
            .ok_or_else(|| {
                StructureError::invalid("owner projection exceeds dominator preorder")
            })?;
        let slot = owner_by_block.get_mut(block.index()).ok_or_else(|| {
            StructureError::invalid("dominator preorder references a missing CFG block")
        })?;
        *slot = owner;
    }

    let parent_by_spec = specs.iter().map(|spec| spec.parent).collect::<Vec<_>>();
    let mut children = vec![Vec::new(); specs.len()];
    for (index, parent) in parent_by_spec.iter().copied().enumerate() {
        if let Some(parent) = parent {
            children
                .get_mut(parent)
                .ok_or_else(|| {
                    StructureError::invalid("container parent is outside the spec arena")
                })?
                .push(index);
        }
    }
    let mut visited = vec![false; specs.len()];
    let roots = parent_by_spec
        .iter()
        .enumerate()
        .filter_map(|(index, parent)| parent.is_none().then_some(index))
        .collect::<Vec<_>>();
    let mut pending = roots;
    let mut traversal = Vec::with_capacity(specs.len());
    while let Some(parent) = pending.pop() {
        if std::mem::replace(&mut visited[parent], true) {
            return Err(StructureError::invalid(
                "container containment contains a cycle",
            ));
        }
        traversal.push(parent);
        for &child in &children[parent] {
            pending.push(child);
        }
    }
    if let Some(index) = visited.iter().position(|visited| !visited) {
        return Err(StructureError::invalid(format!(
            "container #{index} is disconnected from the containment forest"
        )));
    }

    let rank = block_ranks(cfg);
    for (block_index, owner) in owner_by_block.iter().copied().enumerate() {
        let Some(owner) = owner else {
            continue;
        };
        specs[owner].first_rank = specs[owner].first_rank.min(rank[block_index]);
    }
    for child in traversal.into_iter().rev() {
        let first_rank = specs[child].first_rank;
        if let Some(parent) = specs[child].parent {
            specs[parent].first_rank = specs[parent].first_rank.min(first_rank);
        }
    }
    if let Some(index) = specs.iter().position(|spec| spec.first_rank == usize::MAX) {
        return Err(StructureError::invalid(format!(
            "container #{index} has no ranked CFG block"
        )));
    }
    Ok(owner_by_block)
}

fn flatten_nested_unstructured_specs(
    specs: &mut Vec<ContainerSpec>,
    owner_by_block: &mut [Option<usize>],
    dispositions: &mut AggregateSeedDispositions,
) -> Result<(), StructureError> {
    let is_unstructured =
        |kind| matches!(kind, ContainerKind::Island(_) | ContainerKind::Residual(_));
    let mut children = vec![Vec::new(); specs.len()];
    let mut roots = Vec::new();
    for (index, spec) in specs.iter().enumerate() {
        if let Some(parent) = spec.parent {
            let Some(parent_children) = children.get_mut(parent) else {
                return Err(StructureError::invalid(
                    "container parent is outside the spec arena while flattening islands",
                ));
            };
            parent_children.push(index);
        } else {
            roots.push(index);
        }
    }

    let mut removed = vec![false; specs.len()];
    let mut top_unstructured = vec![None; specs.len()];
    let mut pending = roots
        .iter()
        .rev()
        .copied()
        .map(|root| (root, None))
        .collect::<Vec<_>>();
    while let Some((index, inherited)) = pending.pop() {
        let current = if is_unstructured(specs[index].kind) {
            if let Some(outer) = inherited {
                removed[index] = true;
                Some(outer)
            } else {
                Some(index)
            }
        } else {
            inherited
        };
        top_unstructured[index] = current;
        for child in children[index].iter().rev().copied() {
            pending.push((child, current));
        }
    }
    if !removed.iter().any(|removed| *removed) {
        return Ok(());
    }

    let mut nearest_retained = vec![None; specs.len()];
    let mut pending = roots
        .iter()
        .rev()
        .copied()
        .map(|root| (root, None))
        .collect::<Vec<_>>();
    while let Some((index, inherited)) = pending.pop() {
        let current = if removed[index] {
            inherited
        } else {
            Some(index)
        };
        nearest_retained[index] = current;
        for child in children[index].iter().rev().copied() {
            pending.push((child, current));
        }
    }

    let mut new_index = vec![None; specs.len()];
    let mut retained_count = 0usize;
    for (index, removed) in removed.iter().copied().enumerate() {
        if removed {
            continue;
        }
        new_index[index] = Some(retained_count);
        retained_count = retained_count
            .checked_add(1)
            .ok_or_else(|| StructureError::invalid("flattened spec count overflowed"))?;
    }
    let flattened_target = |old: usize| -> Result<usize, StructureError> {
        if !removed.get(old).copied().ok_or_else(|| {
            StructureError::invalid("aggregate disposition references a missing spec")
        })? {
            return Ok(old);
        }
        top_unstructured[old].ok_or_else(|| {
            StructureError::invalid("nested island has no retained unstructured ancestor")
        })
    };
    let disposition_for = |old: usize| -> Result<AggregateSeedDisposition, StructureError> {
        let target = flattened_target(old)?;
        let index = new_index[target].ok_or_else(|| {
            StructureError::invalid("flattened aggregate target has no new spec index")
        })?;
        match specs[target].kind {
            ContainerKind::Island(island) => Ok(AggregateSeedDisposition::Island(island)),
            ContainerKind::Residual(_) => Ok(AggregateSeedDisposition::Residual(index)),
            _ => Err(StructureError::invalid(
                "flattened aggregate target is not unstructured",
            )),
        }
    };

    let old_islands = dispositions.islands.clone();
    for disposition in &mut dispositions.residuals {
        let old = match *disposition {
            AggregateSeedDisposition::Residual(index) => index,
            AggregateSeedDisposition::Island(island) => {
                old_islands.get(island).copied().flatten().ok_or_else(|| {
                    StructureError::invalid(
                        "residual seed references a missing island while flattening",
                    )
                })?
            }
        };
        *disposition = disposition_for(old)?;
    }
    for disposition in &mut dispositions.islands {
        let Some(old) = *disposition else {
            continue;
        };
        let target = flattened_target(old)?;
        *disposition = Some(new_index[target].ok_or_else(|| {
            StructureError::invalid("flattened island target has no new spec index")
        })?);
    }

    for owner in owner_by_block {
        let Some(old) = *owner else {
            continue;
        };
        let retained = nearest_retained[old].ok_or_else(|| {
            StructureError::invalid("nested island block has no retained container owner")
        })?;
        *owner = Some(new_index[retained].ok_or_else(|| {
            StructureError::invalid("retained block owner has no new spec index")
        })?);
    }

    let old_specs = std::mem::take(specs);
    let mut retained = Vec::with_capacity(retained_count);
    for (old, mut spec) in old_specs.into_iter().enumerate() {
        if removed[old] {
            continue;
        }
        spec.parent = spec
            .parent
            .and_then(|parent| nearest_retained[parent])
            .map(|parent| {
                new_index[parent]
                    .ok_or_else(|| StructureError::invalid("retained parent has no new spec index"))
            })
            .transpose()?;
        retained.push(spec);
    }
    *specs = retained;
    Ok(())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BranchPart {
    Condition,
    Then,
    Else,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LoopPart {
    Preheader,
    Control,
    Body,
    NormalTail,
}

fn reachable_nonempty_blocks(cfg: &Cfg, mut blocks: BTreeSet<BlockRef>) -> BTreeSet<BlockRef> {
    blocks.retain(|block| *block != cfg.exit_block && cfg.reachable_blocks.contains(block));
    blocks
}

fn single_entry(cfg: &Cfg, blocks: &BTreeSet<BlockRef>, entry: BlockRef) -> bool {
    blocks.contains(&entry)
        && blocks.iter().copied().all(|block| {
            cfg.preds[block.index()].iter().all(|edge| {
                let predecessor = cfg.edges[edge.index()].from;
                !cfg.reachable_blocks.contains(&predecessor)
                    || blocks.contains(&predecessor)
                    || block == entry
            })
        })
}

fn value_decision_is_closed(
    cfg: &Cfg,
    blocks: &BTreeSet<BlockRef>,
    continuation: BlockRef,
) -> bool {
    blocks.iter().copied().all(|block| {
        cfg.succs[block.index()].iter().all(|edge| {
            let target = cfg.edges[edge.index()].to;
            blocks.contains(&target) || target == continuation
        })
    })
}

enum InsertDisposition {
    Inserted,
    Rejected(PendingContainer),
}

fn pending_kind_index(kind: ContainerKind) -> usize {
    match kind {
        ContainerKind::SinglePass(id) | ContainerKind::Branch(id) => id.index(),
        ContainerKind::ValueDecision(id) => id.index(),
        ContainerKind::Loop(id) => id.index(),
        ContainerKind::Island(index) => index,
        ContainerKind::Residual(entry) => entry.index(),
    }
}

fn container_entry(
    kind: ContainerKind,
    input: &FinalPlanInput,
    partitions: &[LoopPartitions],
) -> BlockRef {
    match kind {
        ContainerKind::SinglePass(id) | ContainerKind::Branch(id) => {
            input.branches[id.index()].branch.header
        }
        ContainerKind::ValueDecision(id) => input.value_decisions[id.index()].candidate.header,
        ContainerKind::Loop(id) => partitions[id.index()]
            .preheader
            .unwrap_or(input.loops[id.index()].candidate.header),
        ContainerKind::Island(index) => input.unstructured[index].fact.entry,
        ContainerKind::Residual(entry) => entry,
    }
}

fn branch_default_blocks(
    graph_facts: &GraphFacts,
    branch: &super::BranchPlanInput,
) -> BTreeSet<BlockRef> {
    let Some(start) = graph_facts.dominator_tree.preorder_index[branch.branch.header.index()]
    else {
        return BTreeSet::new();
    };
    let Some(end) = graph_facts.dominator_tree.subtree_end[branch.branch.header.index()] else {
        return BTreeSet::new();
    };
    let merge = branch.branch.merge;
    let backward_continuation = merge.is_some_and(|merge| {
        merge != branch.branch.header && graph_facts.dominates(merge, branch.branch.header)
    });
    graph_facts.dominator_tree.order[start..end]
        .iter()
        .copied()
        .filter(|block| {
            merge.is_none_or(|merge| {
                *block != merge && (backward_continuation || !graph_facts.dominates(merge, *block))
            })
        })
        .collect()
}

fn ordinary_branch_ranges(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    input: &FinalPlanInput,
    branch: &super::BranchPlanInput,
) -> Result<Option<Vec<std::ops::Range<usize>>>, StructureError> {
    if branch
        .region
        .as_ref()
        .is_some_and(|region| region.single_pass_fence.is_some())
        || branch.branch.merge.is_some_and(|merge| {
            merge == branch.branch.header || graph_facts.dominates(merge, branch.branch.header)
        })
    {
        return Ok(None);
    }
    let position = |block: BlockRef| {
        graph_facts
            .dominator_tree
            .preorder_index
            .get(block.index())
            .copied()
            .flatten()
            .ok_or_else(|| {
                StructureError::invalid(format!(
                    "ordinary branch references unreachable block {block}"
                ))
            })
    };
    let subtree = |block: BlockRef| {
        Ok(position(block)?
            ..graph_facts
                .dominator_tree
                .subtree_end
                .get(block.index())
                .copied()
                .flatten()
                .ok_or_else(|| {
                    StructureError::invalid(format!(
                        "ordinary branch has no dominator subtree for {block}"
                    ))
                })?)
    };

    let header_range = subtree(branch.branch.header)?;
    let mut ranges = if let Some(merge) = branch.branch.merge {
        BranchRegionFact::new(
            graph_facts,
            branch.branch.header,
            merge,
            branch.branch.kind,
            None,
        )
        .preorder_intervals(graph_facts)
        .map_err(|block| {
            StructureError::invalid(format!(
                "ordinary branch boundary references unreachable block {block}"
            ))
        })?
    } else {
        vec![header_range.clone()]
    };
    if let Some(region) = &branch.region {
        ranges.extend(region.preorder_intervals(graph_facts).map_err(|block| {
            StructureError::invalid(format!(
                "branch evidence references unreachable block {block}"
            ))
        })?);
    }
    ranges = intersect_preorder_ranges(
        &merge_preorder_ranges(ranges),
        std::slice::from_ref(&header_range),
    );

    if branch.branch.else_entry.is_some() {
        let Some((then_entry, Some(else_entry))) = branch_arm_entries(branch, input) else {
            return Ok(None);
        };
        if graph_facts.dominates(then_entry, else_entry)
            || graph_facts.dominates(else_entry, then_entry)
        {
            return Ok(None);
        }
        let allowed = merge_preorder_ranges(vec![subtree(then_entry)?, subtree(else_entry)?]);
        ranges = intersect_preorder_ranges(&ranges, &allowed);
        ranges.push(position(branch.branch.header)?..position(branch.branch.header)? + 1);
        if let Some(condition) = branch
            .condition
            .and_then(|id| input.conditions.get(id.index()))
        {
            ranges.extend(preorder_ranges_for_block_iter(
                graph_facts,
                condition
                    .candidate
                    .blocks
                    .iter()
                    .copied()
                    .filter(|block| graph_facts.dominates(branch.branch.header, *block)),
            )?);
        }
    }

    let exit_position = graph_facts
        .dominator_tree
        .preorder_index
        .get(cfg.exit_block.index())
        .copied()
        .flatten();
    let ranges = exclude_preorder_position(merge_preorder_ranges(ranges), exit_position);
    Ok((!ranges.is_empty()).then_some(ranges))
}

fn try_insert_candidate(
    specs: &mut Vec<ContainerSpec>,
    owners: &mut RangeOwnerTree,
    candidate: PendingContainer,
) -> Result<InsertDisposition, StructureError> {
    let RangeOwnerState::Uniform(parent) = owners.uniform_owner(&candidate.ranges)? else {
        return Ok(InsertDisposition::Rejected(candidate));
    };
    let kind = candidate.kind;
    if let Some(parent_index) = parent {
        let parent_spec = &specs[parent_index];
        if parent_spec.block_count == candidate.block_count {
            let duplicate_allowed = matches!(
                (parent_spec.kind, kind),
                (ContainerKind::Loop(_), ContainerKind::Branch(_))
            );
            let value_decision_exact = matches!(kind, ContainerKind::ValueDecision(_));
            if !duplicate_allowed || value_decision_exact {
                return Ok(InsertDisposition::Rejected(candidate));
            }
        } else if matches!(kind, ContainerKind::ValueDecision(_))
            && matches!(parent_spec.kind, ContainerKind::ValueDecision(_))
        {
            return Ok(InsertDisposition::Rejected(candidate));
        }
    }
    let index = specs.len();
    owners.assign(&candidate.ranges, index)?;
    specs.push(candidate.into_spec());
    Ok(InsertDisposition::Inserted)
}

fn normalize_residual_specs(
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    specs: &mut Vec<ContainerSpec>,
    residuals: &[ResidualSeed],
) -> Result<AggregateSeedDispositions, StructureError> {
    if residuals.is_empty() {
        let mut islands = vec![
            None;
            specs
                .iter()
                .filter_map(|spec| match spec.kind {
                    ContainerKind::Island(index) => Some(index + 1),
                    _ => None,
                })
                .max()
                .unwrap_or(0)
        ];
        for (index, spec) in specs.iter().enumerate() {
            if let ContainerKind::Island(island) = spec.kind {
                let slot = islands.get_mut(island).ok_or_else(|| {
                    StructureError::invalid("island seed index overflowed its disposition arena")
                })?;
                if slot.replace(index).is_some() {
                    return Err(StructureError::invalid(format!(
                        "protected island #{island} has multiple final dispositions"
                    )));
                }
            }
        }
        return Ok(AggregateSeedDispositions {
            residuals: Vec::new(),
            islands,
        });
    }

    // Residual 聚合本来就需要精确 block incidence；只在这条异常路径展开
    // interval domain，正常 structured containment 保持区间表示。
    for spec in specs.iter_mut() {
        if spec.blocks.is_empty() {
            spec.blocks = materialize_preorder_ranges(graph_facts, &spec.ranges)?;
        }
    }

    let mut seed_dsu = DisjointSet::new(residuals.len());
    let mut seed_by_block = vec![None; cfg.blocks.len()];
    for seed in residuals {
        if seed.id.index() >= residuals.len() {
            return Err(StructureError::invalid(
                "residual seed id is outside the seed arena",
            ));
        }
        for block in &seed.blocks {
            let slot = seed_by_block.get_mut(block.index()).ok_or_else(|| {
                StructureError::invalid("residual seed references a missing block")
            })?;
            if let Some(other) = *slot {
                seed_dsu.union(seed.id.index(), other);
            } else {
                *slot = Some(seed.id.index());
            }
        }
    }

    let mut component_by_seed_root = vec![None; residuals.len()];
    let mut initial_components = Vec::<ResidualComponent>::new();
    for seed in residuals {
        let root = seed_dsu.find(seed.id.index());
        let component = if let Some(component) = component_by_seed_root[root] {
            component
        } else {
            let component = initial_components.len();
            component_by_seed_root[root] = Some(component);
            initial_components.push(ResidualComponent {
                blocks: BTreeSet::new(),
                seeds: Vec::new(),
            });
            component
        };
        initial_components[component]
            .blocks
            .extend(seed.blocks.iter().copied());
        initial_components[component].seeds.push(seed.id);
    }

    let mut initial_component_by_block = vec![None; cfg.blocks.len()];
    for (index, component) in initial_components.iter().enumerate() {
        for block in &component.blocks {
            let slot = &mut initial_component_by_block[block.index()];
            if slot.replace(index).is_some_and(|owner| owner != index) {
                return Err(StructureError::invalid(format!(
                    "overlapping residual seeds at block {block} were not merged"
                )));
            }
        }
    }

    // 现有 spec 已经是 laminar family。residual component 只有在同时拥有 spec
    // 内外 block、又没有覆盖完整 spec 时才构成交叉；吸收该 spec 只会合并已经与它
    // 相交的 component，不会再与无关 spec 产生新交叉。因此按 block incidence
    // 扫描一次即可求完整闭包，不需要 restart scan。
    let mut component_dsu = DisjointSet::new(initial_components.len());
    let mut crossed_specs = vec![false; specs.len()];
    let mut intersections = DenseIntersectionWorkspace::new(initial_components.len());
    for (spec_index, spec) in specs.iter().enumerate() {
        intersections.populate(&spec.blocks, &initial_component_by_block);
        let crossed = intersections.touched.iter().copied().any(|component| {
            intersections.counts[component] < spec.blocks.len()
                && initial_components[component].blocks.len() > intersections.counts[component]
        });
        if !crossed {
            continue;
        }
        crossed_specs[spec_index] = true;
        let mut incident = intersections.touched.iter().copied();
        let Some(first) = incident.next() else {
            return Err(StructureError::invalid(
                "crossed container has no incident residual component",
            ));
        };
        for component in incident {
            component_dsu.union(first, component);
        }
    }

    let mut component_by_root = vec![None; initial_components.len()];
    let mut components = Vec::<ResidualComponent>::new();
    for (initial, component) in initial_components.iter().enumerate() {
        let root = component_dsu.find(initial);
        let final_index = if let Some(index) = component_by_root[root] {
            index
        } else {
            let index = components.len();
            component_by_root[root] = Some(index);
            components.push(ResidualComponent {
                blocks: BTreeSet::new(),
                seeds: Vec::new(),
            });
            index
        };
        components[final_index]
            .blocks
            .extend(component.blocks.iter().copied());
        components[final_index]
            .seeds
            .extend(component.seeds.iter().copied());
    }
    for (index, spec) in specs.iter().enumerate() {
        if !crossed_specs[index] {
            continue;
        }
        let initial = spec
            .blocks
            .iter()
            .find_map(|block| initial_component_by_block[block.index()])
            .ok_or_else(|| {
                StructureError::invalid("crossed container lost its residual component")
            })?;
        let root = component_dsu.find(initial);
        let component = component_by_root[root].ok_or_else(|| {
            StructureError::invalid("crossed container references a missing residual component")
        })?;
        components[component]
            .blocks
            .extend(spec.blocks.iter().copied());
    }

    let rank = block_ranks(cfg);
    components.sort_by_key(|component| {
        component
            .blocks
            .iter()
            .map(|block| (rank[block.index()], block.index()))
            .min()
            .unwrap_or((usize::MAX, usize::MAX))
    });
    let mut component_by_block = vec![None; cfg.blocks.len()];
    let mut component_by_seed = vec![None; residuals.len()];
    for (index, component) in components.iter().enumerate() {
        for block in &component.blocks {
            let slot = &mut component_by_block[block.index()];
            if slot.replace(index).is_some_and(|owner| owner != index) {
                return Err(StructureError::invalid(format!(
                    "normalized residual components still overlap at block {block}"
                )));
            }
        }
        for seed in &component.seeds {
            let slot = component_by_seed.get_mut(seed.index()).ok_or_else(|| {
                StructureError::invalid("residual component contains a missing seed")
            })?;
            if slot.replace(index).is_some() {
                return Err(StructureError::invalid(format!(
                    "residual seed #{} belongs to multiple normalized components",
                    seed.index()
                )));
            }
        }
    }

    let mut removed = vec![false; specs.len()];
    let mut exact_island_by_component = vec![None; components.len()];
    let mut intersections = DenseIntersectionWorkspace::new(components.len());
    for (index, spec) in specs.iter().enumerate() {
        intersections.populate(&spec.blocks, &component_by_block);
        for component in intersections.touched.iter().copied() {
            let intersection = intersections.counts[component];
            if intersection < spec.blocks.len() && components[component].blocks.len() > intersection
            {
                return Err(StructureError::invalid(format!(
                    "residual component #{component} still partially crosses container #{index}"
                )));
            }
        }
        let exact_component = intersections.touched.iter().copied().find(|component| {
            intersections.counts[*component] == spec.blocks.len()
                && components[*component].blocks.len() == spec.blocks.len()
        });
        match spec.kind {
            ContainerKind::Island(island) => {
                if let Some(component) = exact_component {
                    let slot = &mut exact_island_by_component[component];
                    if slot.replace(island).is_some() {
                        return Err(StructureError::invalid(format!(
                            "residual component #{component} exactly matches multiple islands"
                        )));
                    }
                }
            }
            ContainerKind::SinglePass(_)
            | ContainerKind::Branch(_)
            | ContainerKind::ValueDecision(_)
            | ContainerKind::Loop(_)
            | ContainerKind::Residual(_) => {
                removed[index] = crossed_specs[index] || exact_component.is_some();
            }
        }
    }

    let mut retained = Vec::with_capacity(specs.len() + components.len());
    let mut islands = Vec::<Option<usize>>::new();
    for (index, spec) in specs.drain(..).enumerate() {
        if removed[index] {
            continue;
        }
        let final_index = retained.len();
        if let ContainerKind::Island(island) = spec.kind {
            if islands.len() <= island {
                islands.resize(island + 1, None);
            }
            if islands[island].replace(final_index).is_some() {
                return Err(StructureError::invalid(format!(
                    "protected island #{island} has multiple final dispositions"
                )));
            }
        }
        retained.push(spec);
    }

    let mut component_dispositions = vec![None; components.len()];
    for (component_index, component) in components.into_iter().enumerate() {
        if let Some(island) = exact_island_by_component[component_index] {
            component_dispositions[component_index] =
                Some(AggregateSeedDisposition::Island(island));
            continue;
        }
        let entry = component
            .seeds
            .iter()
            .filter_map(|seed| residuals.get(seed.index()))
            .map(|seed| seed.entry)
            .filter(|entry| component.blocks.contains(entry))
            .min_by_key(|entry| (rank[entry.index()], entry.index()))
            .ok_or_else(|| {
                StructureError::invalid(format!(
                    "residual component #{component_index} has no contained seed entry"
                ))
            })?;
        let spec_index = retained.len();
        retained.push(
            PendingContainer::exact(
                ContainerKind::Residual(entry),
                component.blocks,
                graph_facts,
            )?
            .into_spec(),
        );
        component_dispositions[component_index] =
            Some(AggregateSeedDisposition::Residual(spec_index));
    }

    let mut seed_dispositions = vec![None; residuals.len()];
    for seed in residuals {
        let component = component_by_seed[seed.id.index()].ok_or_else(|| {
            StructureError::invalid(format!(
                "residual seed #{} has no normalized component",
                seed.id.index()
            ))
        })?;
        let disposition = component_dispositions[component].ok_or_else(|| {
            StructureError::invalid(format!(
                "residual component #{component} has no final disposition"
            ))
        })?;
        if seed_dispositions[seed.id.index()]
            .replace(disposition)
            .is_some()
        {
            return Err(StructureError::invalid(format!(
                "residual seed #{} has multiple final dispositions",
                seed.id.index()
            )));
        }
    }
    *specs = retained;
    Ok(AggregateSeedDispositions {
        residuals: seed_dispositions
            .into_iter()
            .enumerate()
            .map(|(index, disposition)| {
                disposition.ok_or_else(|| {
                    StructureError::invalid(format!(
                        "residual seed #{index} has no final disposition"
                    ))
                })
            })
            .collect::<Result<Vec<_>, _>>()?,
        islands,
    })
}

fn validate_aggregate_seed_dispositions(
    cfg: &Cfg,
    input: &FinalPlanInput,
    residuals: &[ResidualSeed],
    specs: &[ContainerSpec],
    dispositions: &AggregateSeedDispositions,
) -> Result<(), StructureError> {
    if dispositions.residuals.len() != residuals.len() {
        return Err(StructureError::invalid(format!(
            "residual disposition arena has {} entries for {} seeds",
            dispositions.residuals.len(),
            residuals.len()
        )));
    }
    let mut used_residual_specs = vec![false; specs.len()];
    for seed in residuals {
        let disposition = dispositions.residuals[seed.id.index()];
        let spec_index = match disposition {
            AggregateSeedDisposition::Residual(index) => {
                if !matches!(
                    specs.get(index).map(|spec| spec.kind),
                    Some(ContainerKind::Residual(_))
                ) {
                    return Err(StructureError::invalid(format!(
                        "residual seed #{} references non-residual disposition #{index}",
                        seed.id.index()
                    )));
                }
                used_residual_specs[index] = true;
                index
            }
            AggregateSeedDisposition::Island(island) => dispositions
                .islands
                .get(island)
                .copied()
                .flatten()
                .ok_or_else(|| {
                    StructureError::invalid(format!(
                        "residual seed #{} references missing island #{island}",
                        seed.id.index()
                    ))
                })?,
        };
        let spec = &specs[spec_index];
        if !seed.blocks.is_subset(&spec.blocks) {
            return Err(StructureError::invalid(format!(
                "residual seed #{} is not contained by disposition #{spec_index}",
                seed.id.index()
            )));
        }
    }
    for (index, spec) in specs.iter().enumerate() {
        if matches!(spec.kind, ContainerKind::Residual(_)) && !used_residual_specs[index] {
            return Err(StructureError::invalid(format!(
                "residual disposition #{index} has no source seed"
            )));
        }
    }

    for (island, input_island) in input.unstructured.iter().enumerate() {
        let seed_blocks = input_island.layout.as_ref().map_or_else(
            || input_island.fact.blocks.clone(),
            |layout| layout.blocks.clone(),
        );
        let seed_blocks = reachable_nonempty_blocks(cfg, seed_blocks);
        let disposition = dispositions.islands.get(island).copied().flatten();
        if seed_blocks.is_empty() {
            if disposition.is_some() {
                return Err(StructureError::invalid(format!(
                    "unreachable island #{island} has a final disposition"
                )));
            }
            continue;
        }
        let spec_index = disposition.ok_or_else(|| {
            StructureError::invalid(format!(
                "reachable protected island #{island} has no final disposition"
            ))
        })?;
        let Some(spec) = specs.get(spec_index) else {
            return Err(StructureError::invalid(format!(
                "protected island #{island} references missing disposition #{spec_index}"
            )));
        };
        if !matches!(
            spec.kind,
            ContainerKind::Island(_) | ContainerKind::Residual(_)
        ) || !seed_blocks.is_subset(&spec.blocks)
        {
            return Err(StructureError::invalid(format!(
                "protected island #{island} is not contained by its flattened disposition"
            )));
        }
    }
    Ok(())
}

fn branch_part(
    branch: &super::BranchPlanInput,
    input: &FinalPlanInput,
    graph_facts: &GraphFacts,
    block: BlockRef,
) -> Option<BranchPart> {
    if block == branch.branch.header
        || branch
            .condition
            .and_then(|id| input.conditions.get(id.index()))
            .is_some_and(|condition| condition.candidate.blocks.contains(&block))
    {
        return Some(BranchPart::Condition);
    }
    let (then_entry, else_entry) = branch_arm_entries(branch, input)?;
    let in_then = graph_facts.dominates(then_entry, block);
    let in_else = else_entry.is_some_and(|entry| graph_facts.dominates(entry, block));
    match (in_then, in_else) {
        (true, false) => Some(BranchPart::Then),
        (false, true) => Some(BranchPart::Else),
        (false, false) if else_entry.is_none() => Some(BranchPart::Then),
        (true, true) | (false, false) => None,
    }
}

fn branch_arm_entries(
    branch: &super::BranchPlanInput,
    input: &FinalPlanInput,
) -> Option<(BlockRef, Option<BlockRef>)> {
    let Some(condition) = branch
        .condition
        .and_then(|id| input.conditions.get(id.index()))
    else {
        return Some((branch.branch.then_entry, branch.branch.else_entry));
    };
    let ShortCircuitExit::BranchExit { truthy, falsy } = condition.candidate.exit else {
        return None;
    };
    let then_is_truthy = resolve_branch_then_polarity(
        &branch.branch,
        truthy,
        falsy,
        condition
            .candidate
            .blocks
            .contains(&branch.branch.then_entry),
        None,
    )?;
    let (then_entry, other_entry) = if then_is_truthy {
        (truthy, falsy)
    } else {
        (falsy, truthy)
    };
    Some((then_entry, branch.branch.else_entry.map(|_| other_entry)))
}

fn branch_part_for_blocks(
    branch: &super::BranchPlanInput,
    input: &FinalPlanInput,
    graph_facts: &GraphFacts,
    blocks: &BTreeSet<BlockRef>,
) -> Option<BranchPart> {
    let mut parts = blocks
        .iter()
        .copied()
        .filter_map(|block| branch_part(branch, input, graph_facts, block));
    let first = parts.next()?;
    parts.all(|part| part == first).then_some(first)
}

fn loop_part(partition: &LoopPartitions, block: BlockRef) -> Result<LoopPart, StructureError> {
    if partition.preheader == Some(block) {
        Ok(LoopPart::Preheader)
    } else if partition.control.contains(&block) {
        Ok(LoopPart::Control)
    } else if partition.body.contains(&block) {
        Ok(LoopPart::Body)
    } else if partition
        .normal_tail
        .as_ref()
        .is_some_and(|tail| tail.blocks.contains(&block))
    {
        Ok(LoopPart::NormalTail)
    } else {
        Err(StructureError::invalid(format!(
            "block {block} is outside its loop partitions"
        )))
    }
}

fn loop_part_for_blocks(
    partition: &LoopPartitions,
    blocks: &BTreeSet<BlockRef>,
) -> Result<Option<LoopPart>, StructureError> {
    let mut parts = blocks
        .iter()
        .copied()
        .map(|block| loop_part(partition, block));
    let Some(first) = parts.next().transpose()? else {
        return Ok(None);
    };
    for part in parts {
        if part? != first {
            return Ok(None);
        }
    }
    Ok(Some(first))
}

fn reserve(regions: &mut Vec<Option<RegionPlan>>) -> RegionId {
    let id = RegionId(regions.len());
    regions.push(None);
    id
}

fn reserve_sequence(regions: &mut Vec<Option<RegionPlan>>, parent: RegionId) -> RegionId {
    let id = RegionId(regions.len());
    regions.push(Some(RegionPlan::Sequence {
        parent: Some(parent),
        children: Vec::new(),
    }));
    id
}

fn attachment_for_container(
    parent: Option<usize>,
    child: &ContainerSpec,
    specs: &[ContainerSpec],
    slots: &[ContainerSlots],
    input: &FinalPlanInput,
    partitions: &[LoopPartitions],
    graph_facts: &GraphFacts,
) -> Result<RegionId, StructureError> {
    let Some(parent) = parent else {
        return Ok(RegionId(0));
    };
    match (specs[parent].kind, slots[parent]) {
        (ContainerKind::SinglePass(_), ContainerSlots::SinglePass { region }) => Ok(region),
        (
            ContainerKind::Loop(id),
            ContainerSlots::Loop {
                preheader,
                control,
                body,
                normal_tail,
                ..
            },
        ) => match if child.blocks.is_empty() {
            Some(loop_part(&partitions[id.index()], child.representative)?)
        } else {
            loop_part_for_blocks(&partitions[id.index()], &child.blocks)?
        } {
            Some(LoopPart::Preheader) => preheader.ok_or_else(|| {
                StructureError::invalid("loop child requires a missing preheader region")
            }),
            Some(LoopPart::Control) => Ok(control),
            Some(LoopPart::Body) => Ok(body),
            Some(LoopPart::NormalTail) => normal_tail.ok_or_else(|| {
                StructureError::invalid("loop child requires a missing normal-tail region")
            }),
            None => Err(StructureError::invalid(format!(
                "child {:?} ranges {:?} cross loop #{} partitions: preheader={:?} control={:?} body={:?} normal_tail={:?}",
                child.kind,
                child.ranges,
                id.index(),
                partitions[id.index()].preheader,
                partitions[id.index()].control,
                partitions[id.index()].body,
                partitions[id.index()]
                    .normal_tail
                    .as_ref()
                    .map(|tail| &tail.blocks),
            ))),
        },
        (
            ContainerKind::Island(_) | ContainerKind::Residual(_),
            ContainerSlots::Island { region },
        ) => Ok(region),
        (
            ContainerKind::Branch(id),
            ContainerSlots::Branch {
                condition,
                then_arm,
                else_arm,
                ..
            },
        ) => {
            let part = if child.blocks.is_empty() {
                branch_part(
                    &input.branches[id.index()],
                    input,
                    graph_facts,
                    child.representative,
                )
            } else {
                branch_part_for_blocks(
                    &input.branches[id.index()],
                    input,
                    graph_facts,
                    &child.blocks,
                )
            };
            match part {
                Some(BranchPart::Condition) => Ok(condition),
                Some(BranchPart::Then) => Ok(then_arm),
                Some(BranchPart::Else) => else_arm.ok_or_else(|| {
                    StructureError::invalid("branch child requires a missing else arm")
                }),
                None => Err(StructureError::invalid(format!(
                    "child {:?} ranges {:?} cross branch #{} arms: then=#{} else={:?} continuation={:?}",
                    child.kind,
                    child.ranges,
                    id.index(),
                    input.branches[id.index()].branch.then_entry.index(),
                    input.branches[id.index()]
                        .branch
                        .else_entry
                        .map(BlockRef::index),
                    input.branches[id.index()].branch.merge.map(BlockRef::index),
                ))),
            }
        }
        _ => Err(StructureError::invalid("container parent slot mismatch")),
    }
}

fn attachment_for_block(
    owner: Option<usize>,
    block: BlockRef,
    specs: &[ContainerSpec],
    slots: &[ContainerSlots],
    input: &FinalPlanInput,
    partitions: &[LoopPartitions],
    graph_facts: &GraphFacts,
) -> Result<RegionId, StructureError> {
    let Some(owner) = owner else {
        return Ok(RegionId(0));
    };
    match (specs[owner].kind, slots[owner]) {
        (ContainerKind::SinglePass(_), ContainerSlots::SinglePass { region }) => Ok(region),
        (
            ContainerKind::Loop(id),
            ContainerSlots::Loop {
                preheader,
                control,
                body,
                normal_tail,
                ..
            },
        ) => match loop_part(&partitions[id.index()], block)? {
            LoopPart::Preheader => preheader.ok_or_else(|| {
                StructureError::invalid("loop block requires a missing preheader region")
            }),
            LoopPart::Control => Ok(control),
            LoopPart::Body => Ok(body),
            LoopPart::NormalTail => normal_tail.ok_or_else(|| {
                StructureError::invalid("loop block requires a missing normal-tail region")
            }),
        },
        (
            ContainerKind::Branch(id),
            ContainerSlots::Branch {
                condition,
                then_arm,
                else_arm,
                ..
            },
        ) => match branch_part(&input.branches[id.index()], input, graph_facts, block) {
            Some(BranchPart::Condition) => Ok(condition),
            Some(BranchPart::Then) => Ok(then_arm),
            Some(BranchPart::Else) => else_arm
                .ok_or_else(|| StructureError::invalid("branch block requires a missing else arm")),
            None => Err(StructureError::invalid(format!(
                "block {block} is not owned by one branch arm"
            ))),
        },
        (
            ContainerKind::Island(_) | ContainerKind::Residual(_),
            ContainerSlots::Island { region },
        ) => Ok(region),
        _ => Err(StructureError::invalid("block owner slot mismatch")),
    }
}

fn append_region(
    parent: RegionId,
    child: RegionId,
    rank: usize,
    island_regions: &[bool],
    sequences: &mut [Vec<(usize, RegionId)>],
    islands: &mut [Vec<(usize, UnstructuredLayoutItem)>],
) -> Result<(), StructureError> {
    if island_regions.get(parent.index()).copied().unwrap_or(false) {
        islands[parent.index()].push((rank, UnstructuredLayoutItem::Region(child)));
    } else {
        let sequence = sequences.get_mut(parent.index()).ok_or_else(|| {
            StructureError::invalid(format!(
                "missing sequence parent region #{}",
                parent.index()
            ))
        })?;
        sequence.push((rank, child));
    }
    Ok(())
}

fn block_ranks(cfg: &Cfg) -> Vec<usize> {
    let mut ranks = vec![usize::MAX; cfg.blocks.len()];
    for (rank, block) in cfg.block_order.iter().copied().enumerate() {
        ranks[block.index()] = rank;
    }
    ranks
}
