//! 这个文件恢复 Luau 带 capture 的重复 `DUPCLOSURE` 所属词法 factory。
//!
//! 带 capture 的 reusable closure 不能直接降低成多个独立闭包字面量：Luau 会按 capture
//! identity 复用闭包，且 VM 对 NaN 的 identity 比较不满足自反性。因此必须在 HIR 改变
//! 形态前证明共同词法 owner。这里仅描述 closure dependency DAG；被内联 factory 的调用、
//! 参数求值及其他可观察指令仍留在父 proto 原位。
//!
//! 输入示例：父 proto 的 `@3/@7 DUPCLOSURE s2` 分别只被 `@6/@10 DUPCLOSURE s5`
//! 捕获。输出计划：在共同 owner 处声明一次 synthetic factory，消费 `@3/@7`，并把
//! `@6/@10` 改为 factory call；若 `@3` 同时是另一组的 owner，则只保留其 factory 声明。

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::hir::HirLowerError;
use crate::parser::Origin;
use crate::structure::{
    BlockRef, CanonicalMoveIndex, Cfg, CfgGraph, DataflowFacts, GraphFacts, RegionId, RegionPlan,
    SsaValue, StructurePlan,
};
use crate::transformer::{
    CaptureSource, ClosureCreation, InstrRef, LowInstr, LoweredProto, ProtoRef, Reg,
    SharedClosureRef, UpvalueRef, ValuePack,
};

mod composite;
mod groups;
mod lexical_scope;
mod templates;

use composite::*;
use groups::*;
use lexical_scope::*;
use templates::*;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub(super) struct CompositeFactoryRef(pub(super) usize);

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub(super) struct CompositeNodeRef(pub(super) usize);

impl CompositeNodeRef {
    pub(super) const fn index(self) -> usize {
        self.0
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(super) enum CompositeCapture {
    Outer(usize),
    Dependency(CompositeNodeRef),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(super) struct CompositeClosureNode {
    /// 调用方迁移 claimed child 前，它是当前父 proto 的直接 child。
    pub(super) proto: ProtoRef,
    pub(super) captures: Vec<CompositeCapture>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(super) struct CompositeFactoryPlan {
    /// synthetic factory 应声明在这个词法 owner 定义旁。
    pub(super) anchor: InstrRef,
    pub(super) lexical_owner_proto: ProtoRef,
    pub(super) root_shared: SharedClosureRef,
    pub(super) preserve_owner_value: bool,
    pub(super) outer_captures: Vec<CaptureSource>,
    /// dependency-first 拓扑序；`root` 索引这个数组。
    pub(super) nodes: Vec<CompositeClosureNode>,
    pub(super) root: CompositeNodeRef,
}

#[derive(Debug, Default)]
pub(super) struct SharedClosurePlan {
    replacements: BTreeMap<InstrRef, CompositeFactoryRef>,
    owners: BTreeMap<InstrRef, CompositeFactoryRef>,
    consumed: BTreeSet<InstrRef>,
    composites: Vec<CompositeFactoryPlan>,
    claimed_children: BTreeSet<ProtoRef>,
}

impl SharedClosurePlan {
    pub(super) fn replacement_at(&self, instr: InstrRef) -> Option<CompositeFactoryRef> {
        self.replacements.get(&instr).copied()
    }

    pub(super) fn owner_at(&self, instr: InstrRef) -> Option<CompositeFactoryRef> {
        self.owners.get(&instr).copied()
    }

    pub(super) fn is_consumed(&self, instr: InstrRef) -> bool {
        self.consumed.contains(&instr)
    }

    pub(super) fn composites(&self) -> &[CompositeFactoryPlan] {
        &self.composites
    }

    pub(super) fn child_is_claimed(&self, child: ProtoRef) -> bool {
        self.claimed_children.contains(&child)
    }
}

/// 为每个 reachable、重复且带 capture 的 reusable group 构造带证明的恢复计划。
///
/// # 错误
///
/// 当重复 group 不能绑定到唯一支配它的词法 owner 和精确的 closure-only dependency DAG
/// 时返回 [`HirLowerError::UnrepresentableRepeatedCapturedSharedClosure`]。这里不能降级输出
/// 多个独立闭包字面量，否则会改变 Luau closure identity，尤其是 NaN capture。
pub(super) fn build_shared_closure_plan(
    proto: &LoweredProto,
    cfg_graph: &CfgGraph,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    structure: &StructurePlan,
) -> Result<SharedClosurePlan, HirLowerError> {
    let groups = collect_reusable_groups(proto, &cfg_graph.cfg, dataflow);
    let targets = groups
        .values()
        .filter(|group| group.instrs.len() > 1 && group.has_captures)
        .map(|group| group.shared)
        .collect::<Vec<_>>();
    if targets.is_empty() {
        return Ok(SharedClosurePlan::default());
    }

    let owner_templates = collect_owner_templates(proto, cfg_graph, dataflow);
    let mut canonical_moves = CanonicalMoveIndex::new(proto, dataflow);
    let mut owners_by_root = BTreeMap::<_, Vec<_>>::new();
    for (index, owner) in owner_templates.iter().enumerate() {
        let root = owner.template.nodes[owner.template.root.index()].origin;
        owners_by_root
            .entry(origin_key(root))
            .or_default()
            .push(index);
    }
    let mut lexical_scopes = LexicalScopeIndex::new(structure);
    let mut roots = Vec::new();
    for shared in &targets {
        let group = &groups[shared];
        let dominance = group_dominance_envelope(group, &cfg_graph.cfg, graph_facts)
            .ok_or_else(|| group.error())?;
        let lexical_scope =
            group_lexical_scope_envelope(group, &cfg_graph.cfg, &mut lexical_scopes)
                .ok_or_else(|| group.error())?;
        let mut matched = None;
        let origin = proto
            .children
            .get(group.proto.index())
            .ok_or_else(|| group.error())?
            .origin;
        for index in owners_by_root
            .get(&origin_key(origin))
            .into_iter()
            .flatten()
        {
            let owner = &owner_templates[*index];
            let Some(component) =
                (owner_dominates_envelope(owner.instr, dominance, &cfg_graph.cfg, graph_facts)
                    && lexical_scopes
                        .instr_scope(owner.instr, &cfg_graph.cfg)
                        .is_some_and(|owner_scope| {
                            structure.region_contains(owner_scope, lexical_scope.first)
                                && structure.region_contains(owner_scope, lexical_scope.last)
                        }))
                .then(|| {
                    match_component(proto, dataflow, &groups, owner, group, &mut canonical_moves)
                })
                .flatten()
            else {
                continue;
            };
            if matched.replace((owner, component)).is_some() {
                return Err(group.error());
            }
        }
        if let Some(root) = matched {
            roots.push(root);
        }
    }

    roots.sort_by_key(|(owner, _)| owner.instr);
    let mut plan = SharedClosurePlan::default();
    let mut claimed_groups = BTreeSet::new();
    let mut claimed_owners = BTreeSet::new();
    for (owner, component) in roots {
        if component
            .node_groups
            .iter()
            .any(|shared| claimed_groups.contains(shared))
            || !claimed_owners.insert(owner.instr)
        {
            return Err(groups[&component.root_shared].error());
        }

        let owner_closure =
            closure_at(proto, owner.instr).ok_or_else(|| groups[&component.root_shared].error())?;
        let composite = build_composite(proto, owner, &component)
            .ok_or_else(|| groups[&component.root_shared].error())?;
        let factory = CompositeFactoryRef(plan.composites.len());
        plan.composites.push(CompositeFactoryPlan {
            anchor: owner.instr,
            lexical_owner_proto: owner_closure.proto,
            root_shared: component.root_shared,
            preserve_owner_value: !owner_definition_is_unused(proto, dataflow, owner.instr),
            outer_captures: composite.outer_captures,
            nodes: composite.nodes,
            root: composite.root,
        });

        if plan.replacements.contains_key(&owner.instr)
            || plan.owners.insert(owner.instr, factory).is_some()
        {
            return Err(groups[&component.root_shared].error());
        }
        for instr in &component.root_occurrences {
            if plan.owners.contains_key(instr)
                || plan.consumed.contains(instr)
                || plan.replacements.insert(*instr, factory).is_some()
            {
                return Err(groups[&component.root_shared].error());
            }
        }
        for (shared, proto) in component.node_groups.iter().zip(&component.node_protos) {
            claimed_groups.insert(*shared);
            plan.claimed_children.insert(*proto);
        }
        for instr in &component.dependency_occurrences {
            if plan.replacements.contains_key(instr) || !plan.consumed.insert(*instr) {
                return Err(groups[&component.root_shared].error());
            }
        }
    }

    if let Some(unclaimed) = targets
        .into_iter()
        .find(|shared| !claimed_groups.contains(shared))
    {
        return Err(groups[&unclaimed].error());
    }

    Ok(plan)
}
