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

const fn origin_key(origin: Origin) -> (usize, usize, Option<u64>) {
    (origin.span.offset, origin.span.size, origin.raw_word)
}

#[derive(Debug)]
struct ReusableGroup {
    shared: SharedClosureRef,
    proto: ProtoRef,
    instrs: Vec<InstrRef>,
    has_captures: bool,
    consistent_proto: bool,
}

impl ReusableGroup {
    fn error(&self) -> HirLowerError {
        HirLowerError::UnrepresentableRepeatedCapturedSharedClosure {
            shared_index: self.shared.0,
            instr: self.instrs.first().map_or(0, |instr| instr.index()),
        }
    }
}

fn collect_reusable_groups(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
) -> BTreeMap<SharedClosureRef, ReusableGroup> {
    let mut groups = BTreeMap::new();
    for (index, instr) in proto.instrs.iter().enumerate() {
        let instr_ref = InstrRef(index);
        if !instr_is_reachable(cfg, instr_ref) {
            continue;
        }
        let LowInstr::Closure(closure) = instr else {
            continue;
        };
        let ClosureCreation::Reusable(shared) = closure.creation else {
            continue;
        };
        if dataflow.instr_def_for_reg(instr_ref, closure.dst).is_none() {
            continue;
        }
        let group = groups.entry(shared).or_insert_with(|| ReusableGroup {
            shared,
            proto: closure.proto,
            instrs: Vec::new(),
            has_captures: false,
            consistent_proto: true,
        });
        group.consistent_proto &= group.proto == closure.proto;
        group.instrs.push(instr_ref);
        group.has_captures |= !closure.captures.is_empty();
    }
    groups
}

#[derive(Debug)]
struct OwnerTemplate {
    instr: InstrRef,
    template: Arc<ClosureTemplate>,
}

fn collect_owner_templates(
    proto: &LoweredProto,
    cfg_graph: &CfgGraph,
    dataflow: &DataflowFacts,
) -> Vec<OwnerTemplate> {
    let mut templates = BTreeMap::<_, Option<Arc<ClosureTemplate>>>::new();
    let mut owners = Vec::new();
    for (index, instr) in proto.instrs.iter().enumerate() {
        let instr_ref = InstrRef(index);
        if !instr_is_reachable(&cfg_graph.cfg, instr_ref) {
            continue;
        }
        let LowInstr::Closure(closure) = instr else {
            continue;
        };
        let Some(child) = proto.children.get(closure.proto.index()) else {
            continue;
        };
        let template = templates
            .entry(origin_key(child.origin))
            .or_insert_with(|| {
                let child_cfg = cfg_graph.children.get(closure.proto.index())?;
                let child_dataflow = dataflow.children.get(closure.proto.index())?;
                extract_template(child, &child_cfg.cfg, child_dataflow).map(Arc::new)
            })
            .clone();
        if let Some(template) = template {
            owners.push(OwnerTemplate {
                instr: instr_ref,
                template,
            });
        }
    }
    owners
}

#[derive(Debug)]
struct ClosureTemplate {
    nodes: Vec<TemplateNode>,
    root: CompositeNodeRef,
    outer_upvalues: BTreeSet<UpvalueRef>,
}

#[derive(Debug)]
struct TemplateNode {
    origin: Origin,
    captures: Vec<TemplateCapture>,
}

#[derive(Debug, Clone, Copy)]
enum TemplateCapture {
    Outer(UpvalueRef),
    Dependency(CompositeNodeRef),
}

fn extract_template(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
) -> Option<ClosureTemplate> {
    let mut canonical_moves = CanonicalMoveIndex::new(proto, dataflow);
    let mut returned_root = None;
    for (index, instr) in proto.instrs.iter().enumerate() {
        let instr_ref = InstrRef(index);
        if !instr_is_reachable(cfg, instr_ref) {
            continue;
        }
        let LowInstr::Return(return_) = instr else {
            continue;
        };
        let ValuePack::Fixed(values) = return_.values else {
            return None;
        };
        if values.len != 1 {
            return None;
        }
        let value = dataflow.use_value(instr_ref, values.start);
        let root = resolve_returned_closure(proto, dataflow, value, &mut canonical_moves)?;
        match returned_root {
            None => returned_root = Some(root),
            Some(existing) if existing == root => {}
            Some(_) => return None,
        }
    }
    let returned_root = returned_root?;

    let mut builder = TemplateBuilder {
        proto,
        dataflow,
        nodes: Vec::new(),
        node_by_instr: BTreeMap::new(),
        visiting: BTreeSet::new(),
        outer_upvalues: BTreeSet::new(),
        canonical_moves: &mut canonical_moves,
    };
    let root = builder.build_node(returned_root)?;

    Some(ClosureTemplate {
        nodes: builder.nodes,
        root,
        outer_upvalues: builder.outer_upvalues,
    })
}

fn resolve_returned_closure(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    value: SsaValue,
    canonical_moves: &mut CanonicalMoveIndex<'_>,
) -> Option<InstrRef> {
    let SsaValue::Def(def) = canonical_moves.resolve(value).ok()? else {
        return None;
    };
    let instr_ref = dataflow.def_instr(def);
    matches!(proto.instrs.get(instr_ref.index()), Some(LowInstr::Closure(closure)) if closure.dst == dataflow.def_reg(def))
        .then_some(instr_ref)
}

struct TemplateBuilder<'a, 'moves> {
    proto: &'a LoweredProto,
    dataflow: &'a DataflowFacts,
    nodes: Vec<TemplateNode>,
    node_by_instr: BTreeMap<InstrRef, CompositeNodeRef>,
    visiting: BTreeSet<InstrRef>,
    outer_upvalues: BTreeSet<UpvalueRef>,
    canonical_moves: &'moves mut CanonicalMoveIndex<'a>,
}

impl TemplateBuilder<'_, '_> {
    fn build_node(&mut self, instr_ref: InstrRef) -> Option<CompositeNodeRef> {
        if let Some(node) = self.node_by_instr.get(&instr_ref) {
            return Some(*node);
        }
        if !self.visiting.insert(instr_ref) {
            return None;
        }

        let closure = closure_at(self.proto, instr_ref)?;
        let origin = self.proto.children.get(closure.proto.index())?.origin;
        let mut captures = Vec::with_capacity(closure.captures.len());
        for capture in &closure.captures {
            let template_capture = match capture.source {
                CaptureSource::Upvalue(upvalue) => {
                    self.outer_upvalues.insert(upvalue);
                    TemplateCapture::Outer(upvalue)
                }
                CaptureSource::ByReference(_) => return None,
                CaptureSource::ByValue(reg) if reg == closure.dst => return None,
                CaptureSource::ByValue(reg) => {
                    let value = self.dataflow.use_value(instr_ref, reg);
                    let dependency = self.resolve_capture_value(value)?;
                    TemplateCapture::Dependency(self.build_node(dependency)?)
                }
            };
            captures.push(template_capture);
        }

        self.visiting.remove(&instr_ref);
        let node = CompositeNodeRef(self.nodes.len());
        self.nodes.push(TemplateNode { origin, captures });
        self.node_by_instr.insert(instr_ref, node);
        Some(node)
    }

    fn resolve_capture_value(&mut self, value: SsaValue) -> Option<InstrRef> {
        let SsaValue::Def(def) = self.canonical_moves.resolve(value).ok()? else {
            return None;
        };
        let instr_ref = self.dataflow.def_instr(def);
        matches!(self.proto.instrs.get(instr_ref.index()), Some(LowInstr::Closure(closure)) if closure.dst == self.dataflow.def_reg(def))
            .then_some(instr_ref)
    }
}

#[derive(Debug)]
struct MatchedComponent {
    root_shared: SharedClosureRef,
    node_groups: Vec<SharedClosureRef>,
    node_protos: Vec<ProtoRef>,
    root_occurrences: BTreeSet<InstrRef>,
    dependency_occurrences: BTreeSet<InstrRef>,
}

fn match_component(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    groups: &BTreeMap<SharedClosureRef, ReusableGroup>,
    owner: &OwnerTemplate,
    root_group: &ReusableGroup,
    canonical_moves: &mut CanonicalMoveIndex<'_>,
) -> Option<MatchedComponent> {
    if !root_group.consistent_proto
        || proto.children.get(root_group.proto.index())?.origin
            != owner.template.nodes[owner.template.root.0].origin
    {
        return None;
    }
    let owner_closure = closure_at(proto, owner.instr)?;
    if owner
        .template
        .outer_upvalues
        .iter()
        .any(|upvalue| owner_closure.captures.get(upvalue.index()).is_none())
    {
        return None;
    }

    let node_count = owner.template.nodes.len();
    let mut matcher = ComponentMatcher {
        proto,
        dataflow,
        groups,
        owner_instr: owner.instr,
        owner_closure,
        template: &owner.template,
        node_groups: vec![None; node_count],
        group_nodes: BTreeMap::new(),
        node_occurrences: vec![BTreeSet::new(); node_count],
        expected_dependency_uses: BTreeMap::new(),
    };
    let mut instance_nodes = vec![InstrRef(0); node_count];
    let mut instance_generations = vec![0usize; node_count];
    for (root_index, root_instr) in root_group.instrs.iter().enumerate() {
        matcher.match_node(
            owner.template.root,
            *root_instr,
            &mut instance_nodes,
            &mut instance_generations,
            root_index + 1,
            canonical_moves,
        )?;
    }

    let node_groups = matcher
        .node_groups
        .into_iter()
        .collect::<Option<Vec<_>>>()?;
    if node_groups[owner.template.root.0] != root_group.shared {
        return None;
    }
    let node_protos = node_groups
        .iter()
        .map(|shared| {
            let group = groups.get(shared)?;
            group.consistent_proto.then_some(group.proto)
        })
        .collect::<Option<Vec<_>>>()?;

    for (node_index, shared) in node_groups.iter().enumerate() {
        let group = groups.get(shared)?;
        let expected = &matcher.node_occurrences[node_index];
        if group.instrs.len() != expected.len()
            || group.instrs.iter().any(|instr| !expected.contains(instr))
        {
            return None;
        }
        if node_index == owner.template.root.0 {
            continue;
        }
        for instr in expected {
            let closure = closure_at(proto, *instr)?;
            let def = dataflow.instr_def_for_reg(*instr, closure.dst)?;
            let expected_uses = matcher.expected_dependency_uses.get(instr)?;
            let actual_uses = dataflow
                .def_uses
                .get(def.index())?
                .iter()
                .map(|site| (site.instr, site.reg))
                .collect::<BTreeSet<_>>();
            if actual_uses != *expected_uses
                || dataflow
                    .def_phi_uses
                    .get(def.index())
                    .is_none_or(|uses| !uses.is_empty())
            {
                return None;
            }
        }
    }

    let root_occurrences = matcher.node_occurrences[owner.template.root.index()].clone();
    let dependency_occurrences = matcher
        .node_occurrences
        .iter()
        .enumerate()
        .filter(|(index, _)| *index != owner.template.root.index())
        .flat_map(|(_, occurrences)| occurrences.iter().copied())
        .collect();
    Some(MatchedComponent {
        root_shared: root_group.shared,
        node_groups,
        node_protos,
        root_occurrences,
        dependency_occurrences,
    })
}

struct ComponentMatcher<'a> {
    proto: &'a LoweredProto,
    dataflow: &'a DataflowFacts,
    groups: &'a BTreeMap<SharedClosureRef, ReusableGroup>,
    owner_instr: InstrRef,
    owner_closure: &'a crate::transformer::ClosureInstr,
    template: &'a ClosureTemplate,
    node_groups: Vec<Option<SharedClosureRef>>,
    group_nodes: BTreeMap<SharedClosureRef, CompositeNodeRef>,
    node_occurrences: Vec<BTreeSet<InstrRef>>,
    expected_dependency_uses: BTreeMap<InstrRef, BTreeSet<(InstrRef, Reg)>>,
}

impl ComponentMatcher<'_> {
    fn match_node(
        &mut self,
        node: CompositeNodeRef,
        instr_ref: InstrRef,
        instance_nodes: &mut [InstrRef],
        instance_generations: &mut [usize],
        generation: usize,
        canonical_moves: &mut CanonicalMoveIndex<'_>,
    ) -> Option<()> {
        if *instance_generations.get(node.index())? == generation {
            return (instance_nodes[node.index()] == instr_ref).then_some(());
        }
        instance_nodes[node.index()] = instr_ref;
        instance_generations[node.index()] = generation;

        let closure = closure_at(self.proto, instr_ref)?;
        let ClosureCreation::Reusable(shared) = closure.creation else {
            return None;
        };
        let group = self.groups.get(&shared)?;
        if !group.consistent_proto
            || self.proto.children.get(closure.proto.index())?.origin
                != self.template.nodes.get(node.0)?.origin
        {
            return None;
        }
        match self.node_groups[node.0] {
            None => self.node_groups[node.0] = Some(shared),
            Some(existing) if existing == shared => {}
            Some(_) => return None,
        }
        match self.group_nodes.get(&shared) {
            None => {
                self.group_nodes.insert(shared, node);
            }
            Some(existing) if *existing == node => {}
            Some(_) => return None,
        }
        let template_captures = &self.template.nodes[node.0].captures;
        if closure.captures.len() != template_captures.len() {
            return None;
        }
        for (capture, template_capture) in closure.captures.iter().zip(template_captures) {
            match *template_capture {
                TemplateCapture::Outer(upvalue) => {
                    let owner_source = self.owner_closure.captures.get(upvalue.index())?.source;
                    if capture_identity(
                        owner_source,
                        self.owner_instr,
                        self.dataflow,
                        canonical_moves,
                    )? != capture_identity(
                        capture.source,
                        instr_ref,
                        self.dataflow,
                        canonical_moves,
                    )? {
                        return None;
                    }
                }
                TemplateCapture::Dependency(dependency) => {
                    let CaptureSource::ByValue(reg) = capture.source else {
                        return None;
                    };
                    if reg == closure.dst {
                        return None;
                    }
                    let SsaValue::Def(def) = self.dataflow.use_value(instr_ref, reg) else {
                        return None;
                    };
                    let dependency_instr = self.dataflow.def_instr(def);
                    let dependency_closure = closure_at(self.proto, dependency_instr)?;
                    if dependency_closure.dst != self.dataflow.def_reg(def) {
                        return None;
                    }
                    self.expected_dependency_uses
                        .entry(dependency_instr)
                        .or_default()
                        .insert((instr_ref, reg));
                    self.match_node(
                        dependency,
                        dependency_instr,
                        instance_nodes,
                        instance_generations,
                        generation,
                        canonical_moves,
                    )?;
                }
            }
        }
        self.node_occurrences[node.index()].insert(instr_ref);
        Some(())
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum CaptureIdentity {
    Value(SsaValue),
    Upvalue(UpvalueRef),
}

fn capture_identity(
    source: CaptureSource,
    instr: InstrRef,
    dataflow: &DataflowFacts,
    canonical_moves: &mut CanonicalMoveIndex<'_>,
) -> Option<CaptureIdentity> {
    match source {
        CaptureSource::ByValue(reg) => Some(CaptureIdentity::Value(
            canonical_moves
                .resolve(dataflow.use_value(instr, reg))
                .ok()?,
        )),
        CaptureSource::Upvalue(upvalue) => Some(CaptureIdentity::Upvalue(upvalue)),
        CaptureSource::ByReference(_) => None,
    }
}

struct BuiltComposite {
    outer_captures: Vec<CaptureSource>,
    nodes: Vec<CompositeClosureNode>,
    root: CompositeNodeRef,
}

fn build_composite(
    proto: &LoweredProto,
    owner: &OwnerTemplate,
    component: &MatchedComponent,
) -> Option<BuiltComposite> {
    let owner_closure = closure_at(proto, owner.instr)?;
    let mut outer_indices = BTreeMap::new();
    let mut outer_captures = Vec::with_capacity(owner.template.outer_upvalues.len());
    for upvalue in &owner.template.outer_upvalues {
        let source = owner_closure.captures.get(upvalue.index())?.source;
        if matches!(source, CaptureSource::ByReference(_)) {
            return None;
        }
        let index = outer_captures.len();
        outer_indices.insert(*upvalue, index);
        outer_captures.push(source);
    }

    let nodes = owner
        .template
        .nodes
        .iter()
        .enumerate()
        .map(|(index, node)| {
            let captures = node
                .captures
                .iter()
                .map(|capture| match *capture {
                    TemplateCapture::Outer(upvalue) => outer_indices
                        .get(&upvalue)
                        .copied()
                        .map(CompositeCapture::Outer),
                    TemplateCapture::Dependency(dependency) => {
                        Some(CompositeCapture::Dependency(dependency))
                    }
                })
                .collect::<Option<Vec<_>>>()?;
            Some(CompositeClosureNode {
                proto: component.node_protos[index],
                captures,
            })
        })
        .collect::<Option<Vec<_>>>()?;

    Some(BuiltComposite {
        outer_captures,
        nodes,
        root: owner.template.root,
    })
}

fn owner_definition_is_unused(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    owner: InstrRef,
) -> bool {
    let Some(closure) = closure_at(proto, owner) else {
        return false;
    };
    let Some(def) = dataflow.instr_def_for_reg(owner, closure.dst) else {
        return false;
    };
    dataflow
        .def_uses
        .get(def.index())
        .is_some_and(Vec::is_empty)
        && dataflow
            .def_phi_uses
            .get(def.index())
            .is_some_and(Vec::is_empty)
}

#[derive(Debug, Clone, Copy)]
struct GroupDominanceEnvelope {
    block: BlockRef,
    earliest_instr: Option<usize>,
}

fn group_dominance_envelope(
    group: &ReusableGroup,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
) -> Option<GroupDominanceEnvelope> {
    let mut sites = group.instrs.iter();
    let first = *sites.next()?;
    let mut block = *cfg.instr_to_block.get(first.index())?;
    for site in sites {
        let site_block = *cfg.instr_to_block.get(site.index())?;
        block = graph_facts
            .dominator_tree
            .nearest_common_ancestor(block, site_block)?;
    }
    let earliest_instr = group
        .instrs
        .iter()
        .filter(|site| cfg.instr_to_block.get(site.index()) == Some(&block))
        .map(|site| site.index())
        .min();
    Some(GroupDominanceEnvelope {
        block,
        earliest_instr,
    })
}

fn owner_dominates_envelope(
    owner: InstrRef,
    envelope: GroupDominanceEnvelope,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
) -> bool {
    let Some(owner_block) = cfg.instr_to_block.get(owner.index()).copied() else {
        return false;
    };
    if owner_block == envelope.block {
        envelope
            .earliest_instr
            .is_none_or(|site| owner.index() < site)
    } else {
        graph_facts.dominates(owner_block, envelope.block)
    }
}

#[derive(Clone, Copy)]
struct GroupLexicalScopeEnvelope {
    first: RegionId,
    last: RegionId,
}

/// containment tree 的每棵子树在 DFS postorder 中都是连续区间；因此 owner 同时包含
/// 一组 scope 的最左、最右端点，当且仅当它包含整组 scope。
fn group_lexical_scope_envelope(
    group: &ReusableGroup,
    cfg: &Cfg,
    scopes: &mut LexicalScopeIndex<'_>,
) -> Option<GroupLexicalScopeEnvelope> {
    let mut sites = group.instrs.iter();
    let first = scopes.instr_scope(*sites.next()?, cfg)?;
    let mut min = (scopes.rank(first)?, first);
    let mut max = min;
    for site in sites {
        let site_scope = scopes.instr_scope(*site, cfg)?;
        let ranked = (scopes.rank(site_scope)?, site_scope);
        if ranked.0 < min.0 {
            min = ranked;
        }
        if ranked.0 > max.0 {
            max = ranked;
        }
    }
    Some(GroupLexicalScopeEnvelope {
        first: min.1,
        last: max.1,
    })
}

#[derive(Clone, Copy)]
enum LexicalScopeState {
    Unknown,
    Resolved(Option<RegionId>),
}

enum LexicalScopeStep {
    Parent(RegionId),
    Resolved(Option<RegionId>),
}

struct LexicalScopeIndex<'a> {
    structure: &'a StructurePlan,
    states: Vec<LexicalScopeState>,
    ranks: Vec<usize>,
}

impl<'a> LexicalScopeIndex<'a> {
    fn new(structure: &'a StructurePlan) -> Self {
        let mut ranks = vec![usize::MAX; structure.regions().len()];
        for (rank, region) in structure.region_postorder().iter().copied().enumerate() {
            ranks[region.index()] = rank;
        }
        Self {
            structure,
            states: vec![LexicalScopeState::Unknown; ranks.len()],
            ranks,
        }
    }

    fn rank(&self, region: RegionId) -> Option<usize> {
        self.ranks
            .get(region.index())
            .copied()
            .filter(|rank| *rank != usize::MAX)
    }

    fn instr_scope(&mut self, instr: InstrRef, cfg: &Cfg) -> Option<RegionId> {
        let block = *cfg.instr_to_block.get(instr.index())?;
        self.region_scope(self.structure.region_for_block(block)?)
    }

    fn region_scope(&mut self, start: RegionId) -> Option<RegionId> {
        let mut pending = Vec::new();
        let mut region = start;
        let resolved = loop {
            match *self.states.get(region.index())? {
                LexicalScopeState::Resolved(scope) => break scope,
                LexicalScopeState::Unknown => pending.push(region),
            }
            match lexical_scope_step(self.structure, region) {
                LexicalScopeStep::Parent(parent) => region = parent,
                LexicalScopeStep::Resolved(scope) => break scope,
            }
        };
        for region in pending {
            self.states[region.index()] = LexicalScopeState::Resolved(resolved);
        }
        resolved
    }
}

/// 返回 region 最终发射到的 Lua block；无法证明 VM-for control/preheader 落点时拒绝。
///
/// CFG dominance 不等于词法可见性：例如 repeat body 可以支配循环后的 block，但 body
/// 内声明的 local 在循环外不可见。Sequence 与 island 会被展平；branch arm、loop body、
/// normal tail 和 single-pass wrapper 则各自产生新的 Lua block；while/repeat control
/// prefix 最终发射在 loop body 内，因此共享 body 的 scope identity。
fn lexical_scope_step(structure: &StructurePlan, region: RegionId) -> LexicalScopeStep {
    if region == structure.root() || structure.single_pass_for_region(region).is_some() {
        return LexicalScopeStep::Resolved(Some(region));
    }
    let Some(parent) = structure.region(region).and_then(RegionPlan::parent) else {
        return LexicalScopeStep::Resolved(None);
    };
    match structure.region(parent) {
        Some(RegionPlan::Branch {
            then_arm, else_arm, ..
        }) if *then_arm == region || *else_arm == Some(region) => {
            LexicalScopeStep::Resolved(Some(region))
        }
        Some(RegionPlan::Loop {
            plan,
            preheader,
            control,
            body,
            normal_tail,
            ..
        }) => {
            if *body == region || *normal_tail == Some(region) {
                LexicalScopeStep::Resolved(Some(region))
            } else if *control == region {
                LexicalScopeStep::Resolved(
                    matches!(
                        structure.loop_protocol(*plan),
                        Some(
                            crate::structure::LoopVmProtocol::While(_)
                                | crate::structure::LoopVmProtocol::Repeat(_)
                                | crate::structure::LoopVmProtocol::WhileTrue
                        )
                    )
                    .then_some(*body),
                )
            } else if *preheader == Some(region) {
                LexicalScopeStep::Resolved(None)
            } else {
                LexicalScopeStep::Parent(parent)
            }
        }
        Some(_) => LexicalScopeStep::Parent(parent),
        None => LexicalScopeStep::Resolved(None),
    }
}

fn instr_is_reachable(cfg: &Cfg, instr: InstrRef) -> bool {
    cfg.instr_to_block
        .get(instr.index())
        .is_some_and(|block| cfg.reachable_blocks.contains(block))
}

fn closure_at(proto: &LoweredProto, instr: InstrRef) -> Option<&crate::transformer::ClosureInstr> {
    match proto.instrs.get(instr.index())? {
        LowInstr::Closure(closure) => Some(closure),
        _ => None,
    }
}
