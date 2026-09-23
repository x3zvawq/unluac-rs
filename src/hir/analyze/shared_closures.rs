//! 恢复 Luau 重复 DUPCLOSURE 所属的共同词法工厂，保留 capture 与模板身份。
//!
//! 普通恢复只搬回已证明的闭包依赖链，调用及参数求值留在父函数原位。
//! 完整事件前缀另需逐实例的帧匹配与 O2 内联合同；未证明调用消失时不能重建 activation。
//! capture-free 组没有唯一未使用 owner 时仍由共享 pool 保持身份，不猜测原物理 home。

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::hir::HirLowerError;
use crate::parser::Origin;
use crate::structure::{
    BlockRef, Cfg, CfgGraph, DataflowFacts, GraphFacts, RegionId, RegionPlan, SsaValue,
    StructurePlan,
};
use crate::transformer::{
    CaptureSource, ClosureCreation, InstrRef, LowInstr, LoweredProto, ProtoRef, Reg,
    SharedClosureRef, UpvalueRef, ValuePack,
};

mod composite;
mod effects;
mod groups;
mod lexical_scope;
mod publications;
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
    Integer(i64),
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
    pub(super) effect: Option<SharedFactoryEffect>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(super) struct SharedFactoryEffect {
    pub(super) kind: SharedFactoryEffectKind,
    pub(super) field: crate::LuaString,
    pub(super) calls: BTreeMap<InstrRef, Vec<crate::LuaString>>,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(super) enum SharedFactoryEffectKind {
    Print,
    Publish,
}

#[derive(Debug, Default, Clone)]
pub(super) struct SharedClosurePlan {
    replacements: BTreeMap<InstrRef, CompositeFactoryRef>,
    owners: BTreeMap<InstrRef, CompositeFactoryRef>,
    consumed: BTreeSet<InstrRef>,
    effect_prefixes: BTreeSet<InstrRef>,
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
    let mut targets = groups
        .values()
        .filter(|group| group.instrs.len() > 1)
        .map(|group| group.shared)
        .collect::<Vec<_>>();
    if targets.is_empty() {
        return Ok(SharedClosurePlan::default());
    }
    // 必须恢复的 captured 组件先保有依赖；可选 pool 锚定不能抢占这些现有 owner。
    targets.sort_by_key(|shared| (!groups[shared].has_captures, *shared));

    let owner_templates = collect_owner_templates(proto, cfg_graph, dataflow);
    let mut owners_by_root = BTreeMap::<_, Vec<_>>::new();
    for (index, owner) in owner_templates.iter().enumerate() {
        let root = owner.template.nodes[owner.template.root.index()].origin;
        owners_by_root
            .entry(origin_key(root))
            .or_default()
            .push(index);
    }
    let mut lexical_scopes = LexicalScopeIndex::new(structure);
    let mut shape_cache = BTreeMap::new();
    let mut roots = Vec::new();
    let mut matched_groups = BTreeSet::new();
    let mut matched_owners = BTreeSet::new();
    for shared in &targets {
        let group = &groups[shared];
        let Some((dominance, lexical_scope)) =
            group_dominance_envelope(group, &cfg_graph.cfg, graph_facts).zip(
                group_lexical_scope_envelope(group, &cfg_graph.cfg, &mut lexical_scopes),
            )
        else {
            if group.has_captures {
                return Err(group.error());
            }
            continue;
        };
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
            if !group.has_captures && !owner_definition_is_unused(proto, dataflow, owner.instr) {
                continue;
            }
            let Some(component) =
                (owner_dominates_envelope(owner.instr, dominance, &cfg_graph.cfg, graph_facts)
                    && lexical_scopes
                        .instr_scope(owner.instr, &cfg_graph.cfg)
                        .is_some_and(|owner_scope| {
                            structure.region_contains(owner_scope, lexical_scope.first)
                                && structure.region_contains(owner_scope, lexical_scope.last)
                        }))
                .then(|| match_component(proto, dataflow, &groups, owner, group, &mut shape_cache))
                .flatten()
            else {
                continue;
            };
            if matched.is_some() {
                if group.has_captures {
                    return Err(group.error());
                }
                matched = None;
                break;
            }
            matched = Some((owner, component));
        }
        if let Some(root) = matched {
            if !group.has_captures
                && (matched_owners.contains(&root.0.instr)
                    || root
                        .1
                        .node_groups
                        .iter()
                        .any(|shared| matched_groups.contains(shared)))
            {
                continue;
            }
            matched_owners.insert(root.0.instr);
            matched_groups.extend(root.1.node_groups.iter().copied());
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
            effect: None,
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
        .find(|shared| groups[shared].has_captures && !claimed_groups.contains(shared))
    {
        return Err(groups[&unclaimed].error());
    }

    Ok(plan)
}
