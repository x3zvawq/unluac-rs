//! 这个文件集中声明 StructureFacts 层的共享类型。
//!
//! 这些类型只表达“结构候选”和“必须保留的约束”，刻意不提前做最终语法决定，
//! 这样 HIR 还能基于完整证据再做一次更稳的恢复取舍。

use std::collections::{BTreeMap, BTreeSet};

use crate::structure::{BlockRef, DefId, EdgeRef, PhiId, SsaValue};
use crate::transformer::{InstrRef, Reg, RegRange};

use super::cfg::GraphFacts;

use super::plan::{
    BlockOwner, BranchCandidateId, BranchValueMergeId, CleanupDisposition, EdgeOwner,
    GotoRequirementId, LoopCandidateId, PhiIncomingDisposition, RegionId,
};

/// 一个 proto 的结构候选集合，以及它的子 proto 结果。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct StructureFacts {
    pub plan: StructurePlan,
    pub branch_candidates: Vec<BranchCandidate>,
    pub branch_region_facts: Vec<BranchRegionFact>,
    pub branch_value_merge_candidates: Vec<BranchValueMergeCandidate>,
    pub loop_candidates: Vec<LoopCandidate>,
    pub short_circuit_candidates: Vec<ShortCircuitCandidate>,
    pub goto_requirements: Vec<GotoRequirement>,
    pub region_facts: Vec<RegionFact>,
    pub scope_candidates: Vec<ScopeCandidate>,
    pub children: Vec<StructureFacts>,
}

/// Structure 已完成冲突消解后的稳定 owner 索引。
///
/// HIR 必须通过这里的 candidate identity 消费结构事实，不能再按 header 临时覆盖、
/// 取首项或在重复时把整组候选删除。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct StructurePlan {
    pub(super) branch_by_header: BTreeMap<BlockRef, BranchCandidateId>,
    pub(super) branch_value_merge_by_header: BTreeMap<BlockRef, BranchValueMergeId>,
    pub(super) branch_value_merge_by_region: BTreeMap<(BlockRef, BlockRef), BranchValueMergeId>,
    pub(super) loops_by_header: BTreeMap<BlockRef, Vec<LoopCandidateId>>,
    pub(super) unstructured_region_by_block: Vec<Option<RegionId>>,
    pub(super) unstructured_layouts: Vec<Option<UnstructuredRegionLayout>>,
    pub(super) unstructured_layout_by_block: Vec<Option<RegionId>>,
    pub(super) block_owners: Vec<BlockOwner>,
    pub(super) edge_owners: Vec<EdgeOwner>,
    pub(super) cleanup_dispositions: Vec<Option<CleanupDisposition>>,
    pub(super) generic_phi_materializations: Vec<Option<GenericPhiMaterialization>>,
    pub(super) generic_phi_materializations_by_block: Vec<Vec<GenericPhiMaterialization>>,
    pub(super) phi_incoming_dispositions: Vec<Vec<PhiIncomingDisposition>>,
    pub(super) phi_edge_copies: Vec<Vec<PhiEdgeCopy>>,
}

impl StructurePlan {
    pub(super) fn phi_is_dead(&self, phi_id: PhiId) -> bool {
        matches!(
            self.phi_incoming_dispositions[phi_id.index()].first(),
            Some(PhiIncomingDisposition::Dead)
        )
    }

    pub(super) fn phi_has_edge_copy(&self, phi_id: PhiId) -> bool {
        self.phi_incoming_dispositions[phi_id.index()]
            .iter()
            .any(|owner| matches!(owner, PhiIncomingDisposition::EdgeCopy))
    }

    pub(super) fn phi_is_edge_owned(&self, phi_id: PhiId) -> bool {
        let owners = &self.phi_incoming_dispositions[phi_id.index()];
        self.phi_has_edge_copy(phi_id)
            && owners.iter().all(|owner| {
                matches!(
                    owner,
                    PhiIncomingDisposition::EdgeCopy | PhiIncomingDisposition::Unreachable
                )
            })
    }
}

impl StructureFacts {
    pub fn branch_candidate_for_header(&self, header: BlockRef) -> Option<&BranchCandidate> {
        let id = self.plan.branch_by_header.get(&header)?;
        self.branch_candidate(*id)
    }

    pub fn branch_candidate(&self, id: BranchCandidateId) -> Option<&BranchCandidate> {
        self.branch_candidates.get(id.index())
    }

    pub fn branch_candidates_by_header(
        &self,
    ) -> impl Iterator<Item = (BlockRef, &BranchCandidate)> {
        self.plan
            .branch_by_header
            .iter()
            .filter_map(|(header, id)| {
                self.branch_candidate(*id)
                    .map(|candidate| (*header, candidate))
            })
    }

    pub fn branch_value_merge_for_header(
        &self,
        header: BlockRef,
    ) -> Option<&BranchValueMergeCandidate> {
        let id = self.plan.branch_value_merge_by_header.get(&header)?;
        self.branch_value_merge_candidates.get(id.index())
    }

    pub fn branch_value_merge_for_region(
        &self,
        header: BlockRef,
        merge: BlockRef,
    ) -> Option<&BranchValueMergeCandidate> {
        let id = self
            .plan
            .branch_value_merge_by_region
            .get(&(header, merge))?;
        self.branch_value_merge_candidates.get(id.index())
    }

    pub fn loop_candidate(&self, id: LoopCandidateId) -> Option<&LoopCandidate> {
        self.loop_candidates.get(id.index())
    }

    pub fn goto_requirement(&self, id: GotoRequirementId) -> Option<&GotoRequirement> {
        self.goto_requirements.get(id.index())
    }

    pub fn region(&self, id: RegionId) -> Option<&RegionFact> {
        self.region_facts.get(id.index())
    }

    pub fn loop_candidates_for_header(
        &self,
        header: BlockRef,
    ) -> impl DoubleEndedIterator<Item = (LoopCandidateId, &LoopCandidate)> {
        self.plan
            .loops_by_header
            .get(&header)
            .into_iter()
            .flatten()
            .copied()
            .filter_map(|id| self.loop_candidate(id).map(|candidate| (id, candidate)))
    }

    pub fn loop_headers(&self) -> impl Iterator<Item = BlockRef> + '_ {
        self.plan.loops_by_header.keys().copied()
    }

    pub fn has_loop_header(&self, header: BlockRef) -> bool {
        self.plan.loops_by_header.contains_key(&header)
    }

    pub fn block_owner(&self, block: BlockRef) -> Option<BlockOwner> {
        self.plan.block_owners.get(block.index()).copied()
    }

    pub fn edge_owner(&self, edge: EdgeRef) -> Option<EdgeOwner> {
        self.plan.edge_owners.get(edge.index()).copied()
    }

    pub fn unstructured_region(&self, block: BlockRef) -> Option<RegionId> {
        self.plan
            .unstructured_region_by_block
            .get(block.index())
            .copied()
            .flatten()
    }

    pub fn unstructured_layout(&self, region: RegionId) -> Option<&UnstructuredRegionLayout> {
        self.plan.unstructured_layouts.get(region.index())?.as_ref()
    }

    pub fn cleanup_disposition(&self, instr: InstrRef) -> CleanupDisposition {
        self.plan
            .cleanup_dispositions
            .get(instr.index())
            .copied()
            .flatten()
            .expect("cleanup instruction must have one disposition")
    }

    pub fn generic_phi_materialization(&self, phi_id: PhiId) -> Option<GenericPhiMaterialization> {
        self.plan
            .generic_phi_materializations
            .get(phi_id.index())
            .copied()
            .flatten()
    }

    pub fn generic_phi_materializations(
        &self,
    ) -> impl Iterator<Item = GenericPhiMaterialization> + '_ {
        self.plan
            .generic_phi_materializations
            .iter()
            .copied()
            .flatten()
    }

    pub fn generic_phi_materializations_in_block(
        &self,
        block: BlockRef,
    ) -> &[GenericPhiMaterialization] {
        self.plan
            .generic_phi_materializations_by_block
            .get(block.index())
            .map_or(&[], Vec::as_slice)
    }

    pub fn phi_edge_copies(&self, edge: EdgeRef) -> &[PhiEdgeCopy] {
        &self.plan.phi_edge_copies[edge.index()]
    }

    pub fn phi_is_dead(&self, phi_id: PhiId) -> bool {
        self.plan.phi_is_dead(phi_id)
    }

    pub fn phi_is_edge_owned(&self, phi_id: PhiId) -> bool {
        self.plan.phi_is_edge_owned(phi_id)
    }
}

/// 显式 CFG edge 离开 predecessor 时需要执行的一条 phi copy。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PhiEdgeCopy {
    pub phi_id: PhiId,
    pub value: SsaValue,
}

/// 不可规约 region 的实际 mixed-lowering 布局。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnstructuredRegionLayout {
    pub blocks: BTreeSet<BlockRef>,
    pub continuation: BlockRef,
}

/// 一个仍需 generic unresolved 物化的 phi。
///
/// 结构层已经尽力把 branch/loop/short-circuit 能直接解释成源码结构的 phi 接管掉了；
/// 剩下这些说明当前还没有更高层的结构 owner，HIR 只能保守落成 generic phi temp。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct GenericPhiMaterialization {
    pub block: BlockRef,
    pub phi_id: PhiId,
    pub reg: Reg,
    pub source: GenericPhiSource,
}

/// generic phi fallback 的保守来源事实。
///
/// `IdomExit` 表示所有 incoming defs 都等于该支配块出口处的寄存器值；HIR 可以用这个
/// block 降表达式。`Unresolved` 表示 Structure 无法证明单一来源，后层应显式暴露
/// unresolved，而不是猜某个 predecessor。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum GenericPhiSource {
    IdomExit(BlockRef),
    Unresolved,
}

/// 一个分支结构候选。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchCandidate {
    pub header: BlockRef,
    pub then_entry: BlockRef,
    pub else_entry: Option<BlockRef>,
    pub merge: Option<BlockRef>,
    pub kind: BranchKind,
    pub invert_hint: bool,
}

/// 分支形态提示。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum BranchKind {
    IfThen,
    IfElse,
    Guard,
}

/// 一个普通 branch 区域的共享边界事实。
///
/// 普通非回环 branch 的结构区域精确等于 `header` 的支配子树减去 `merge` 的
/// 支配子树，因此不为每个嵌套 branch 复制一份 block 集合。只有 `merge` 支配
/// `header` 的循环边界无法用这个差集表达，才保留显式集合。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchRegionFact {
    pub header: BlockRef,
    pub merge: BlockRef,
    pub kind: BranchKind,
    pub(super) explicit_structured_blocks: Option<BTreeSet<BlockRef>>,
}

impl BranchRegionFact {
    pub fn contains_structured_block(&self, graph_facts: &GraphFacts, block: BlockRef) -> bool {
        self.explicit_structured_blocks.as_ref().map_or_else(
            || {
                graph_facts.dominates(self.header, block)
                    && !graph_facts.dominates(self.merge, block)
            },
            |blocks| blocks.contains(&block),
        )
    }

    pub fn materialize_structured_blocks(&self, graph_facts: &GraphFacts) -> BTreeSet<BlockRef> {
        self.explicit_structured_blocks.clone().unwrap_or_else(|| {
            let Some(start) = graph_facts.dominator_tree.preorder_index[self.header.index()] else {
                return BTreeSet::new();
            };
            let Some(end) = graph_facts.dominator_tree.subtree_end[self.header.index()] else {
                return BTreeSet::new();
            };
            graph_facts
                .dominator_tree
                .order
                .get(start..end)
                .into_iter()
                .flatten()
                .copied()
                .filter(|block| self.contains_structured_block(graph_facts, *block))
                .collect()
        })
    }

    pub(super) fn explicit_structured_blocks(&self) -> Option<&BTreeSet<BlockRef>> {
        self.explicit_structured_blocks.as_ref()
    }
}

/// 一个不可规约区域的共享边界事实。
///
/// 它只表达 SCC 的入口和覆盖 block，不替后层决定最终 `goto/label` 语法。
/// `goto / regions` 都消费这份事实，不应再各自重复做 SCC 入口扫描。
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct IrreducibleRegion {
    pub entry: BlockRef,
    pub blocks: BTreeSet<BlockRef>,
    pub entry_edges: Vec<EdgeRef>,
}

/// 一个普通 branch 在 merge 点上产生的值合流候选。
///
/// 它和 `ShortCircuitCandidate::ValueMerge` 的区别是：这里不假设整片区域更像 `and/or`，
/// 只表达“这个结构化 branch 的两臂分别给 merge 提供了哪些值版本”。这样 HIR 可以
/// 统一决定要不要继续当成同一 lvalue、还是保守物化成 `Decision` / 临时值。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchValueMergeCandidate {
    pub header: BlockRef,
    pub merge: BlockRef,
    pub values: Vec<BranchValueMergeValue>,
}

/// 一个 merge 值在两臂上的来源分布。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchValueMergeValue {
    pub phi_id: PhiId,
    pub reg: Reg,
    pub then_arm: BranchValueMergeArm,
    pub else_arm: BranchValueMergeArm,
}

/// branch merge 某一臂已经收敛好的来源事实。
///
/// `preds` 保留结构边归属，`values` 记录这一臂在 merge 前实际可见的 canonical SSA
/// 身份。`entry_values` 是 branch header 带入的值，`update_values` 是各 arm 在本轮
/// 产生或传递更新的版本；同一个 Phi 可以同时属于两类。HIR 只消费这份分类，不再
/// 把 Phi 压回叶子 def 后重判来源。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchValueMergeArm {
    pub preds: BTreeSet<BlockRef>,
    pub values: BTreeSet<SsaValue>,
    pub entry_values: BTreeSet<SsaValue>,
    pub update_values: BTreeSet<SsaValue>,
}

/// 一个循环候选。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopCandidate {
    pub header: BlockRef,
    pub preheader: Option<BlockRef>,
    pub blocks: BTreeSet<BlockRef>,
    /// 源码 loop body 在词法上覆盖的 block。
    ///
    /// natural loop blocks 不包含提前退出 tail，也可能漏掉 repeat 分支进入的 nested
    /// loop。Structure 在这里统一保存源码 body 边界；HIR bindings 与结构降低只消费
    /// 这份事实，不回头用 CFG 扩张作用域。
    pub body_scope_blocks: BTreeSet<BlockRef>,
    /// 已被循环语法或规范化出口吸收、无需作为源码 body 单独降低的 block。
    pub control_blocks: BTreeSet<BlockRef>,
    pub backedges: Vec<EdgeRef>,
    pub exits: BTreeSet<BlockRef>,
    pub continue_target: Option<BlockRef>,
    /// 已由当前循环认领的 branch -> continue target/pad 边。
    pub continue_edges: BTreeSet<EdgeRef>,
    /// 仅在短路候选参与 loop 形态精化时记录其条件入口。
    pub condition_header: Option<BlockRef>,
    pub kind_hint: LoopKindHint,
    pub source_bindings: Option<LoopSourceBindings>,
    pub header_value_merges: Vec<LoopValueMerge>,
    pub exit_value_merges: Vec<LoopExitValueMergeCandidate>,
}

/// 循环头已经暴露给 HIR 的源码绑定证据。
///
/// 这里只记录“源码层确实会出现的绑定寄存器”，避免 HIR 再回头扫描 low-IR/CFG
/// 去猜 numeric-for / generic-for 的绑定槽位。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopSourceBindings {
    Numeric(Reg),
    Generic(RegRange),
}

/// loop merge 某一臂的稳定 incoming 事实。
///
/// 和 branch merge 不同，loop state 恢复需要保留“每个 predecessor 分别给了哪些 defs”，
/// 这样 HIR 才能直接消费 preheader/exit 的来源，不必再回头拆 `phi.incoming`。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopValueIncoming {
    pub pred: Option<BlockRef>,
    pub value: SsaValue,
}

/// 一个 loop value merge 某一臂的 incoming 集合。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LoopValueArm {
    pub incomings: Vec<LoopValueIncoming>,
}

impl LoopValueArm {
    pub fn is_empty(&self) -> bool {
        self.incomings.is_empty()
    }

    pub fn contains_pred(&self, pred: BlockRef) -> bool {
        self.incomings
            .iter()
            .any(|incoming| incoming.pred == Some(pred))
    }

    pub fn incoming_for_pred(&self, pred: BlockRef) -> Option<&LoopValueIncoming> {
        self.incomings
            .iter()
            .find(|incoming| incoming.pred == Some(pred))
    }

    pub fn entry_incoming(&self) -> Option<&LoopValueIncoming> {
        self.incomings
            .iter()
            .find(|incoming| incoming.pred.is_none())
    }

    pub fn preds(&self) -> impl Iterator<Item = BlockRef> + '_ {
        self.incomings.iter().filter_map(|incoming| incoming.pred)
    }

    pub fn values(&self) -> impl Iterator<Item = SsaValue> + '_ {
        self.incomings.iter().map(|incoming| incoming.value)
    }

    pub fn all_preds_within(&self, allowed_blocks: &BTreeSet<BlockRef>) -> bool {
        self.incomings.iter().all(|incoming| {
            incoming
                .pred
                .is_some_and(|pred| allowed_blocks.contains(&pred))
        })
    }
}

/// 一个 loop header/exit 上的值合流候选。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopValueMerge {
    pub phi_id: PhiId,
    pub reg: Reg,
    pub inside_arm: LoopValueArm,
    pub outside_arm: LoopValueArm,
}

/// 某个 loop exit block 上的值合流候选集合。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopExitValueMergeCandidate {
    pub exit: BlockRef,
    pub values: Vec<LoopValueMerge>,
}

/// 循环形态提示。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum LoopKindHint {
    WhileLike,
    WhileTrueLike,
    RepeatLike,
    NumericForLike,
    GenericForLike,
    Unknown,
}

/// 一个短路表达式候选。
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ShortCircuitCandidate {
    pub header: BlockRef,
    pub blocks: BTreeSet<BlockRef>,
    pub entry: ShortCircuitNodeRef,
    pub nodes: Vec<ShortCircuitNode>,
    pub exit: ShortCircuitExit,
    pub result_reg: Option<Reg>,
    pub result_phi_id: Option<PhiId>,
    pub entry_value: Option<SsaValue>,
    pub value_incomings: Vec<ShortCircuitValueIncoming>,
    pub reducible: bool,
}

impl ShortCircuitCandidate {
    pub(crate) fn branch_exit_leaf_preds(&self, want_truthy: bool) -> BTreeSet<BlockRef> {
        self.nodes
            .iter()
            .filter_map(|node| {
                let matches_exit = if want_truthy {
                    matches!(&node.truthy, ShortCircuitTarget::TruthyExit)
                        || matches!(&node.falsy, ShortCircuitTarget::TruthyExit)
                } else {
                    matches!(&node.truthy, ShortCircuitTarget::FalsyExit)
                        || matches!(&node.falsy, ShortCircuitTarget::FalsyExit)
                };
                matches_exit.then_some(node.header)
            })
            .collect()
    }

    pub(crate) fn value_truthiness_leaves(
        &self,
    ) -> Option<(BTreeSet<BlockRef>, BTreeSet<BlockRef>)> {
        let ShortCircuitExit::ValueMerge(_) = self.exit else {
            return None;
        };

        fn collect_truthy_value_leaves(
            short: &ShortCircuitCandidate,
            node_ref: ShortCircuitNodeRef,
            truthy_memo: &mut BTreeMap<ShortCircuitNodeRef, BTreeSet<BlockRef>>,
            falsy_memo: &mut BTreeMap<ShortCircuitNodeRef, BTreeSet<BlockRef>>,
        ) -> Option<BTreeSet<BlockRef>> {
            if let Some(leaves) = truthy_memo.get(&node_ref) {
                return Some(leaves.clone());
            }

            let node = short.nodes.get(node_ref.index())?;
            let leaves =
                collect_target_value_leaves(short, &node.truthy, true, truthy_memo, falsy_memo)?;
            Some(truthy_memo.entry(node_ref).or_insert(leaves).clone())
        }

        fn collect_falsy_value_leaves(
            short: &ShortCircuitCandidate,
            node_ref: ShortCircuitNodeRef,
            truthy_memo: &mut BTreeMap<ShortCircuitNodeRef, BTreeSet<BlockRef>>,
            falsy_memo: &mut BTreeMap<ShortCircuitNodeRef, BTreeSet<BlockRef>>,
        ) -> Option<BTreeSet<BlockRef>> {
            if let Some(leaves) = falsy_memo.get(&node_ref) {
                return Some(leaves.clone());
            }

            let node = short.nodes.get(node_ref.index())?;
            let leaves =
                collect_target_value_leaves(short, &node.falsy, false, truthy_memo, falsy_memo)?;
            Some(falsy_memo.entry(node_ref).or_insert(leaves).clone())
        }

        fn collect_target_value_leaves(
            short: &ShortCircuitCandidate,
            target: &ShortCircuitTarget,
            want_truthy: bool,
            truthy_memo: &mut BTreeMap<ShortCircuitNodeRef, BTreeSet<BlockRef>>,
            falsy_memo: &mut BTreeMap<ShortCircuitNodeRef, BTreeSet<BlockRef>>,
        ) -> Option<BTreeSet<BlockRef>> {
            match target {
                ShortCircuitTarget::Node(next_ref) => {
                    if want_truthy {
                        collect_truthy_value_leaves(short, *next_ref, truthy_memo, falsy_memo)
                    } else {
                        collect_falsy_value_leaves(short, *next_ref, truthy_memo, falsy_memo)
                    }
                }
                ShortCircuitTarget::Value(block) => Some(BTreeSet::from([*block])),
                ShortCircuitTarget::TruthyExit | ShortCircuitTarget::FalsyExit => None,
            }
        }

        let mut truthy_memo = BTreeMap::new();
        let mut falsy_memo = BTreeMap::new();
        let truthy_leaves =
            collect_truthy_value_leaves(self, self.entry, &mut truthy_memo, &mut falsy_memo)?;
        let falsy_leaves =
            collect_falsy_value_leaves(self, self.entry, &mut truthy_memo, &mut falsy_memo)?;
        Some((truthy_leaves, falsy_leaves))
    }

    pub(crate) fn node_depths(&self) -> BTreeMap<ShortCircuitNodeRef, usize> {
        let mut depths = BTreeMap::new();
        let mut worklist = vec![(self.entry, 0usize)];

        while let Some((node_ref, depth)) = worklist.pop() {
            if depths
                .get(&node_ref)
                .is_some_and(|known_depth| *known_depth <= depth)
            {
                continue;
            }
            depths.insert(node_ref, depth);

            let Some(node) = self.nodes.get(node_ref.index()) else {
                continue;
            };
            if let ShortCircuitTarget::Node(next_ref) = node.truthy {
                worklist.push((next_ref, depth + 1));
            }
            if let ShortCircuitTarget::Node(next_ref) = node.falsy {
                worklist.push((next_ref, depth + 1));
            }
        }

        depths
    }

    pub(crate) fn node_leaves(
        &self,
        node_ref: ShortCircuitNodeRef,
        memo: &mut BTreeMap<ShortCircuitNodeRef, BTreeSet<BlockRef>>,
    ) -> BTreeSet<BlockRef> {
        if let Some(leaves) = memo.get(&node_ref) {
            return leaves.clone();
        }

        let Some(node) = self.nodes.get(node_ref.index()) else {
            return BTreeSet::new();
        };

        let mut leaves = self.target_leaves(&node.truthy, memo);
        leaves.extend(self.target_leaves(&node.falsy, memo));
        memo.entry(node_ref).or_insert(leaves).clone()
    }

    fn target_leaves(
        &self,
        target: &ShortCircuitTarget,
        memo: &mut BTreeMap<ShortCircuitNodeRef, BTreeSet<BlockRef>>,
    ) -> BTreeSet<BlockRef> {
        match target {
            ShortCircuitTarget::Node(next_ref) => self.node_leaves(*next_ref, memo),
            ShortCircuitTarget::Value(block) => BTreeSet::from([*block]),
            ShortCircuitTarget::TruthyExit | ShortCircuitTarget::FalsyExit => BTreeSet::new(),
        }
    }
}

/// 值型 short-circuit merge 每个叶子最终送进 merge 的 canonical SSA 值。
///
/// 这份事实和 `result_phi_id` 一起构成了“叶子 -> merge 值身份”的前层表达，避免 HIR
/// 再顺着 `PhiCandidate.incoming` 去拆 value leaf。`latest_local_def` 进一步把
/// “这个 leaf block 自己最后一次写 result_reg 的 def”前移出来，避免 HIR 再回头扫描
/// block 指令去找叶子值来源。
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ShortCircuitValueIncoming {
    pub pred: BlockRef,
    pub value: SsaValue,
    pub latest_local_def: Option<DefId>,
}

/// 短路 DAG 中的稳定节点引用。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ShortCircuitNodeRef(pub usize);

impl ShortCircuitNodeRef {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// 一个短路决策节点。
///
/// 这里显式用 `truthy/falsy` 语义连边，而不是 raw `then/else`。原因是结构层的职责
/// 是把 CFG 重新翻译成“按 Lua 求值语义理解”的候选，方便 HIR 直接基于真值流恢复
/// `and/or`，而不用再次反查 `negated` 和 branch 边方向。
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ShortCircuitNode {
    pub id: ShortCircuitNodeRef,
    pub header: BlockRef,
    pub truthy: ShortCircuitTarget,
    pub falsy: ShortCircuitTarget,
}

/// 短路 DAG 上的目标。
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum ShortCircuitTarget {
    /// 继续进入下一个短路决策节点。
    Node(ShortCircuitNodeRef),
    /// 值型短路的一条叶子。`BlockRef` 指向把值送进 merge 的前驱 block。
    Value(BlockRef),
    /// 条件型短路的“整体为真”出口。
    TruthyExit,
    /// 条件型短路的“整体为假”出口。
    FalsyExit,
}

/// 短路控制流最终如何离开候选区域。
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum ShortCircuitExit {
    /// 这条短路 DAG 最终在某个 block 合流，并通常伴随 phi/result 语义。
    ValueMerge(BlockRef),
    /// 这条短路 DAG 最终直接分流到“整体为真/整体为假”的两个出口。
    BranchExit { truthy: BlockRef, falsy: BlockRef },
}

/// 一个必须保留跳转的要求。
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct GotoRequirement {
    pub edge: EdgeRef,
    pub reason: GotoReason,
}

/// 为什么这条边当前不能被结构候选吸收。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum GotoReason {
    IrreducibleFlow,
    MultiEntryRegion,
    UnstructuredBreakLike,
    UnstructuredContinueLike,
}

/// 某片 block 集合的区域事实。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RegionFact {
    pub blocks: BTreeSet<BlockRef>,
    pub entry: BlockRef,
    pub exits: BTreeSet<BlockRef>,
}

/// 一个潜在的词法 scope。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScopeCandidate {
    pub entry: BlockRef,
    pub exit: Option<BlockRef>,
    pub close_points: Vec<InstrRef>,
}
