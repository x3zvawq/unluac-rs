//! 提取 closure capture 模板并匹配 owner/replacement 组件；依赖 canonical Move 与 child 依赖，不负责最终 dominance/scope 校验；例如递归构建共享 factory 节点。

use super::*;

#[derive(Debug)]
pub(super) struct ClosureTemplate {
    pub(super) nodes: Vec<TemplateNode>,
    pub(super) root: CompositeNodeRef,
    pub(super) outer_upvalues: BTreeSet<UpvalueRef>,
}

#[derive(Debug)]
pub(super) struct TemplateNode {
    pub(super) origin: Origin,
    pub(super) captures: Vec<TemplateCapture>,
}

#[derive(Debug, Clone, Copy)]
pub(super) enum TemplateCapture {
    Outer(UpvalueRef),
    Dependency(CompositeNodeRef),
}

pub(super) fn extract_template(
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

pub(super) fn resolve_returned_closure(
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

pub(super) struct TemplateBuilder<'a, 'moves> {
    proto: &'a LoweredProto,
    dataflow: &'a DataflowFacts,
    nodes: Vec<TemplateNode>,
    node_by_instr: BTreeMap<InstrRef, CompositeNodeRef>,
    visiting: BTreeSet<InstrRef>,
    outer_upvalues: BTreeSet<UpvalueRef>,
    canonical_moves: &'moves mut CanonicalMoveIndex<'a>,
}

impl TemplateBuilder<'_, '_> {
    pub(super) fn build_node(&mut self, instr_ref: InstrRef) -> Option<CompositeNodeRef> {
        if let Some(node) = self.node_by_instr.get(&instr_ref) {
            return Some(*node);
        }
        if !self.visiting.insert(instr_ref) {
            return None;
        }

        let closure = closure_at(self.proto, instr_ref)?;
        let origin = self.proto.children.get(closure.proto.index())?.origin;
        struct BuildFrame {
            instr_ref: InstrRef,
            origin: Origin,
            next_capture: usize,
            captures: Vec<TemplateCapture>,
        }

        // 父 frame 保留到依赖完成后再接收 node ref，使 capture 顺序和 node 后序编号
        // 与递归 DFS 相同；visiting 则覆盖整个 frame 生命周期以拒绝环。
        let mut stack = vec![BuildFrame {
            instr_ref,
            origin,
            next_capture: 0,
            captures: Vec::with_capacity(closure.captures.len()),
        }];
        loop {
            let frame = stack.last_mut()?;
            let closure = closure_at(self.proto, frame.instr_ref)?;
            let Some(capture) = closure.captures.get(frame.next_capture) else {
                let frame = stack.pop()?;
                self.visiting.remove(&frame.instr_ref);
                let node = CompositeNodeRef(self.nodes.len());
                self.nodes.push(TemplateNode {
                    origin: frame.origin,
                    captures: frame.captures,
                });
                self.node_by_instr.insert(frame.instr_ref, node);
                if let Some(parent) = stack.last_mut() {
                    parent.captures.push(TemplateCapture::Dependency(node));
                    continue;
                }
                return Some(node);
            };

            let capture_source = capture.source;
            let closure_dst = closure.dst;
            let current_instr = frame.instr_ref;
            frame.next_capture += 1;
            match capture_source {
                CaptureSource::Upvalue(upvalue) => {
                    self.outer_upvalues.insert(upvalue);
                    frame.captures.push(TemplateCapture::Outer(upvalue));
                }
                CaptureSource::ByReference(_) => return None,
                CaptureSource::ByValue(reg) if reg == closure_dst => return None,
                CaptureSource::ByValue(reg) => {
                    let value = self.dataflow.use_value(current_instr, reg);
                    let dependency = self.resolve_capture_value(value)?;
                    if let Some(node) = self.node_by_instr.get(&dependency) {
                        frame.captures.push(TemplateCapture::Dependency(*node));
                        continue;
                    }
                    if !self.visiting.insert(dependency) {
                        return None;
                    }
                    let dependency_closure = closure_at(self.proto, dependency)?;
                    let dependency_origin = self
                        .proto
                        .children
                        .get(dependency_closure.proto.index())?
                        .origin;
                    stack.push(BuildFrame {
                        instr_ref: dependency,
                        origin: dependency_origin,
                        next_capture: 0,
                        captures: Vec::with_capacity(dependency_closure.captures.len()),
                    });
                }
            }
        }
    }

    pub(super) fn resolve_capture_value(&mut self, value: SsaValue) -> Option<InstrRef> {
        let SsaValue::Def(def) = self.canonical_moves.resolve(value).ok()? else {
            return None;
        };
        let instr_ref = self.dataflow.def_instr(def);
        matches!(self.proto.instrs.get(instr_ref.index()), Some(LowInstr::Closure(closure)) if closure.dst == self.dataflow.def_reg(def))
            .then_some(instr_ref)
    }
}

#[derive(Debug)]
pub(super) struct MatchedComponent {
    pub(super) root_shared: SharedClosureRef,
    pub(super) node_groups: Vec<SharedClosureRef>,
    pub(super) node_protos: Vec<ProtoRef>,
    pub(super) root_occurrences: BTreeSet<InstrRef>,
    pub(super) dependency_occurrences: BTreeSet<InstrRef>,
}

/// owner-independent component proof cached by `(TemplateClassRef, SharedClosureRef)`.
///
/// The shape pass resolves every physical dependency edge and records the canonical identity
/// of each outer capture.  A later owner candidate only compares its own capture sources with
/// these facts; it never re-walks a validated `(template node, physical instruction)` pair.
/// The occurrence sets are also the alias/liveness contract used to consume the matched shared
/// groups.
#[derive(Debug, Clone)]
pub(super) struct MatchedShape {
    pub(super) node_groups: Vec<SharedClosureRef>,
    pub(super) node_protos: Vec<ProtoRef>,
    pub(super) root_occurrences: BTreeSet<InstrRef>,
    pub(super) dependency_occurrences: BTreeSet<InstrRef>,
    pub(super) outer_identities: BTreeMap<UpvalueRef, CaptureIdentity>,
}

pub(super) fn match_component(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    groups: &BTreeMap<SharedClosureRef, ReusableGroup>,
    owner: &OwnerTemplate,
    root_group: &ReusableGroup,
    shape_cache: &mut BTreeMap<(TemplateClassRef, SharedClosureRef), Option<Arc<MatchedShape>>>,
    canonical_moves: &mut CanonicalMoveIndex<'_>,
) -> Option<MatchedComponent> {
    let owner_closure = closure_at(proto, owner.instr)?;
    let shape = shape_cache
        .entry((owner.class, root_group.shared))
        .or_insert_with(|| {
            match_component_shape(proto, dataflow, groups, owner, root_group, canonical_moves)
                .map(Arc::new)
        })
        .clone()?;

    // The shape cache deliberately does not include the owner occurrence.  Compare all outer
    // capture identities here, once per upvalue, so an owner with a different lexical value is
    // rejected without replaying the dependency DAG.
    if owner
        .template
        .outer_upvalues
        .iter()
        .any(|upvalue| owner_closure.captures.get(upvalue.index()).is_none())
    {
        return None;
    }
    for (upvalue, expected) in &shape.outer_identities {
        let source = owner_closure.captures.get(upvalue.index())?.source;
        if capture_identity(source, owner.instr, dataflow, canonical_moves) != Some(*expected) {
            return None;
        }
    }

    Some(MatchedComponent {
        root_shared: root_group.shared,
        node_groups: shape.node_groups.clone(),
        node_protos: shape.node_protos.clone(),
        root_occurrences: shape.root_occurrences.clone(),
        dependency_occurrences: shape.dependency_occurrences.clone(),
    })
}

fn match_component_shape(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    groups: &BTreeMap<SharedClosureRef, ReusableGroup>,
    owner: &OwnerTemplate,
    root_group: &ReusableGroup,
    canonical_moves: &mut CanonicalMoveIndex<'_>,
) -> Option<MatchedShape> {
    if !root_group.consistent_proto
        || proto.children.get(root_group.proto.index())?.origin
            != owner.template.nodes[owner.template.root.0].origin
    {
        return None;
    }

    let node_count = owner.template.nodes.len();
    let mut matcher = ComponentMatcher {
        proto,
        dataflow,
        groups,
        template: &owner.template,
        node_groups: vec![None; node_count],
        group_nodes: BTreeMap::new(),
        node_occurrences: vec![BTreeSet::new(); node_count],
        expected_dependency_uses: BTreeMap::new(),
        outer_identities: BTreeMap::new(),
        validated_pairs: BTreeSet::new(),
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
    Some(MatchedShape {
        root_occurrences,
        dependency_occurrences,
        node_groups,
        node_protos,
        outer_identities: matcher.outer_identities,
    })
}

pub(super) struct ComponentMatcher<'a> {
    proto: &'a LoweredProto,
    dataflow: &'a DataflowFacts,
    groups: &'a BTreeMap<SharedClosureRef, ReusableGroup>,
    template: &'a ClosureTemplate,
    node_groups: Vec<Option<SharedClosureRef>>,
    group_nodes: BTreeMap<SharedClosureRef, CompositeNodeRef>,
    node_occurrences: Vec<BTreeSet<InstrRef>>,
    expected_dependency_uses: BTreeMap<InstrRef, BTreeSet<(InstrRef, Reg)>>,
    outer_identities: BTreeMap<UpvalueRef, CaptureIdentity>,
    /// `(template node, physical instruction)` 已完成全部 capture proof 的持久索引。
    /// 它只跳过重复的子图 materialization；每次进入仍先执行 generation 与 group alias
    /// 检查，因此 diamond 中的同一 node 不会因 seen 去重而接受不同物理指令。
    validated_pairs: BTreeSet<(CompositeNodeRef, InstrRef)>,
}

impl ComponentMatcher<'_> {
    pub(super) fn match_node(
        &mut self,
        node: CompositeNodeRef,
        instr_ref: InstrRef,
        instance_nodes: &mut [InstrRef],
        instance_generations: &mut [usize],
        generation: usize,
        canonical_moves: &mut CanonicalMoveIndex<'_>,
    ) -> Option<()> {
        enum MatchFrame {
            Enter {
                node: CompositeNodeRef,
                instr_ref: InstrRef,
            },
            Captures {
                node: CompositeNodeRef,
                instr_ref: InstrRef,
                next_capture: usize,
            },
        }

        // dependency 前先压入父 capture 续点，确保 expected use 在下潜前登记，
        // node occurrence 仍只在全部 capture 验证完成后登记。
        let mut stack = vec![MatchFrame::Enter { node, instr_ref }];
        while let Some(frame) = stack.pop() {
            match frame {
                MatchFrame::Enter { node, instr_ref } => {
                    if *instance_generations.get(node.index())? == generation {
                        if instance_nodes[node.index()] != instr_ref {
                            return None;
                        }
                        continue;
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
                    if closure.captures.len() != self.template.nodes[node.0].captures.len() {
                        return None;
                    }
                    if self.validated_pairs.contains(&(node, instr_ref)) {
                        continue;
                    }
                    stack.push(MatchFrame::Captures {
                        node,
                        instr_ref,
                        next_capture: 0,
                    });
                }
                MatchFrame::Captures {
                    node,
                    instr_ref,
                    next_capture,
                } => {
                    let closure = closure_at(self.proto, instr_ref)?;
                    let Some(capture) = closure.captures.get(next_capture) else {
                        self.validated_pairs.insert((node, instr_ref));
                        self.node_occurrences[node.index()].insert(instr_ref);
                        continue;
                    };
                    let template_capture = *self
                        .template
                        .nodes
                        .get(node.index())?
                        .captures
                        .get(next_capture)?;
                    match template_capture {
                        TemplateCapture::Outer(upvalue) => {
                            let identity = capture_identity(
                                capture.source,
                                instr_ref,
                                self.dataflow,
                                canonical_moves,
                            )?;
                            match self.outer_identities.entry(upvalue) {
                                std::collections::btree_map::Entry::Vacant(entry) => {
                                    entry.insert(identity);
                                }
                                std::collections::btree_map::Entry::Occupied(entry)
                                    if *entry.get() != identity =>
                                {
                                    return None;
                                }
                                std::collections::btree_map::Entry::Occupied(_) => {}
                            }
                            stack.push(MatchFrame::Captures {
                                node,
                                instr_ref,
                                next_capture: next_capture + 1,
                            });
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
                            stack.push(MatchFrame::Captures {
                                node,
                                instr_ref,
                                next_capture: next_capture + 1,
                            });
                            stack.push(MatchFrame::Enter {
                                node: dependency,
                                instr_ref: dependency_instr,
                            });
                        }
                    }
                }
            }
        }
        Some(())
    }
}
