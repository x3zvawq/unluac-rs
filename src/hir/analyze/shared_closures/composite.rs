//! 解析 capture identity、构建 composite factory 并检查 dominance envelope；依赖匹配组件与图事实，不负责词法 scope；例如确认 owner 支配全部 replacement。

use super::*;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(super) enum CaptureIdentity {
    Value(SsaValue),
    Upvalue(UpvalueRef),
}

pub(super) fn capture_identity(
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

pub(super) struct BuiltComposite {
    pub(super) outer_captures: Vec<CaptureSource>,
    pub(super) nodes: Vec<CompositeClosureNode>,
    pub(super) root: CompositeNodeRef,
}

pub(super) fn build_composite(
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

pub(super) fn owner_definition_is_unused(
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
pub(super) struct GroupDominanceEnvelope {
    block: BlockRef,
    earliest_instr: Option<usize>,
}

pub(super) fn group_dominance_envelope(
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

pub(super) fn owner_dominates_envelope(
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
