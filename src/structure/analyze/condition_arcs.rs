//! 为直接条件候选合成弧证据并执行副作用/定义逃逸检查；依赖 CFG 与 SSA，不负责候选排序；例如截断包含未吸收副作用的条件尾。

use super::*;

pub(super) fn synthesize_direct_condition_arcs(
    proto: &LoweredProto,
    cfg: &Cfg,
    condition: &ShortCircuitCandidate,
    workspace: &mut ConditionArcWorkspace,
) -> Result<Option<Vec<ConditionArcEvidence>>, StructureError> {
    let context = DirectConditionArcContext {
        proto,
        cfg,
        condition,
    };
    let arcs = condition
        .nodes
        .iter()
        .map(|node| -> Result<Option<_>, StructureError> {
            let Some((truthy_edge, falsy_edge)) = semantic_branch_edges(proto, cfg, node.header)
            else {
                return Ok(None);
            };
            let Some(truthy) = synthesize_direct_condition_arc(
                &context,
                node.id,
                true,
                truthy_edge,
                node.truthy.clone(),
                workspace,
            )?
            else {
                return Ok(None);
            };
            let Some(falsy) = synthesize_direct_condition_arc(
                &context,
                node.id,
                false,
                falsy_edge,
                node.falsy.clone(),
                workspace,
            )?
            else {
                return Ok(None);
            };
            Ok(Some([truthy, falsy]))
        })
        .collect::<Result<Option<Vec<_>>, _>>()?
        .map(|pairs| pairs.into_iter().flatten().collect());
    Ok(arcs)
}

pub(super) struct DirectConditionArcContext<'a> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    condition: &'a ShortCircuitCandidate,
}

/// 所有候选共享访问代次，避免每条 condition arc 都按全图分配并清零 visited。
pub(super) struct ConditionArcWorkspace {
    marks: Vec<usize>,
    epoch: usize,
}

impl ConditionArcWorkspace {
    pub(super) fn new(block_count: usize) -> Self {
        Self {
            marks: vec![0; block_count],
            epoch: 0,
        }
    }

    fn next_epoch(&mut self) -> Result<usize, StructureError> {
        self.epoch = self
            .epoch
            .checked_add(1)
            .ok_or_else(|| StructureError::invalid("direct condition arc visit epoch overflow"))?;
        Ok(self.epoch)
    }

    fn mark_once(&mut self, block: super::super::BlockRef, epoch: usize) -> Option<bool> {
        let mark = self.marks.get_mut(block.index())?;
        if *mark == epoch {
            Some(false)
        } else {
            *mark = epoch;
            Some(true)
        }
    }
}

pub(super) fn synthesize_direct_condition_arc(
    context: &DirectConditionArcContext<'_>,
    source: ShortCircuitNodeRef,
    truthy: bool,
    first_edge: super::super::EdgeRef,
    target: ShortCircuitTarget,
    workspace: &mut ConditionArcWorkspace,
) -> Result<Option<ConditionArcEvidence>, StructureError> {
    let DirectConditionArcContext {
        proto,
        cfg,
        condition,
    } = *context;
    let expected = match target {
        ShortCircuitTarget::Node(node) => {
            let Some(node) = condition.nodes.get(node.index()) else {
                return Ok(None);
            };
            node.header
        }
        ShortCircuitTarget::TruthyExit => match condition.exit {
            ShortCircuitExit::BranchExit { truthy, .. } => truthy,
            ShortCircuitExit::ValueMerge(_) => return Ok(None),
        },
        ShortCircuitTarget::FalsyExit => match condition.exit {
            ShortCircuitExit::BranchExit { falsy, .. } => falsy,
            ShortCircuitExit::ValueMerge(_) => return Ok(None),
        },
        ShortCircuitTarget::Value(_) => return Ok(None),
    };
    let mut edges = vec![first_edge];
    let mut connector_blocks = Vec::new();
    let epoch = workspace.next_epoch()?;
    let Some(first_edge) = cfg.edges.get(first_edge.index()) else {
        return Ok(None);
    };
    let mut block = first_edge.to;
    while block != expected {
        if !workspace.mark_once(block, epoch).unwrap_or(false) {
            return Ok(None);
        }
        let Some(block_data) = cfg.blocks.get(block.index()) else {
            return Ok(None);
        };
        let range = block_data.instrs;
        let Some(successors) = cfg.succs.get(block.index()) else {
            return Ok(None);
        };
        let [edge] = successors.as_slice() else {
            return Ok(None);
        };
        if range.len != 1
            || !matches!(
                proto.instrs.get(range.start.index()),
                Some(LowInstr::Jump(_))
            )
            || !matches!(
                cfg.edges.get(edge.index()),
                Some(edge) if edge.kind == EdgeKind::Jump
            )
        {
            return Ok(None);
        }
        connector_blocks.push(block);
        edges.push(*edge);
        let Some(edge) = cfg.edges.get(edge.index()) else {
            return Ok(None);
        };
        block = edge.to;
    }
    Ok(Some(ConditionArcEvidence {
        source,
        truthy,
        edges,
        connector_blocks,
        target,
    }))
}

pub(super) fn semantic_branch_edges(
    proto: &LoweredProto,
    cfg: &Cfg,
    header: super::super::BlockRef,
) -> Option<(super::super::EdgeRef, super::super::EdgeRef)> {
    let (then_edge, else_edge) = cfg.branch_edges(header)?;
    match cfg.terminator(&proto.instrs, header) {
        Some(crate::transformer::LowInstr::Branch(branch)) if branch.cond.negated => {
            Some((else_edge, then_edge))
        }
        Some(crate::transformer::LowInstr::Branch(_)) => Some((then_edge, else_edge)),
        _ => None,
    }
}

pub(super) fn safe_condition_candidate(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    candidate: &ShortCircuitCandidate,
    workspace: &mut ConditionSafetyWorkspace,
) -> Option<ShortCircuitCandidate> {
    let cut_index = candidate
        .nodes
        .iter()
        .enumerate()
        .skip(1)
        .find_map(|(index, node)| {
            (block_has_escaping_defs(cfg, dataflow, candidate, node.header)
                || block_has_unabsorbed_effects(cfg, dataflow, node.header, workspace))
            .then_some(index)
        });
    match cut_index {
        Some(cut_index) => truncate_condition_at(candidate, cut_index),
        None => Some(candidate.clone()),
    }
}

pub(super) struct ConditionSafetyWorkspace {
    epoch: usize,
    needed_instr_epochs: Vec<usize>,
    def_epochs: Vec<usize>,
    phi_epochs: Vec<usize>,
    pending: Vec<super::super::SsaValue>,
}

impl ConditionSafetyWorkspace {
    pub(super) fn new(dataflow: &DataflowFacts) -> Self {
        Self {
            epoch: 0,
            needed_instr_epochs: vec![0; dataflow.instr_effects.len()],
            def_epochs: vec![0; dataflow.defs.len()],
            phi_epochs: vec![0; dataflow.phi_candidates.len()],
            pending: Vec::new(),
        }
    }

    fn begin(&mut self) {
        if self.epoch == usize::MAX {
            self.needed_instr_epochs.fill(0);
            self.def_epochs.fill(0);
            self.phi_epochs.fill(0);
            self.epoch = 1;
        } else {
            self.epoch += 1;
        }
        self.pending.clear();
    }

    fn needs_instr(&self, instr: InstrRef) -> bool {
        self.needed_instr_epochs.get(instr.index()).copied() == Some(self.epoch)
    }
}

pub(super) fn block_has_unabsorbed_effects(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    block: super::super::BlockRef,
    workspace: &mut ConditionSafetyWorkspace,
) -> bool {
    workspace.begin();
    let Some(range) = cfg.blocks.get(block.index()).map(|block| block.instrs) else {
        return true;
    };
    let Some(predicate) = range.last() else {
        return true;
    };
    let Some(uses) = dataflow.use_values.get(predicate.index()) else {
        return true;
    };
    workspace.pending.extend(uses.fixed.values());
    while let Some(value) = workspace.pending.pop() {
        match value {
            super::super::SsaValue::Entry(_) => {}
            super::super::SsaValue::Def(def) => {
                let Some(stamp) = workspace.def_epochs.get_mut(def.index()) else {
                    return true;
                };
                if *stamp == workspace.epoch {
                    continue;
                }
                *stamp = workspace.epoch;
                let Some(definition) = dataflow.defs.get(def.index()) else {
                    return true;
                };
                let Some(needed) = workspace
                    .needed_instr_epochs
                    .get_mut(definition.instr.index())
                else {
                    return true;
                };
                *needed = workspace.epoch;
                let Some(uses) = dataflow.use_values.get(definition.instr.index()) else {
                    return true;
                };
                workspace.pending.extend(uses.fixed.values());
            }
            super::super::SsaValue::Phi(phi) => {
                let Some(stamp) = workspace.phi_epochs.get_mut(phi.index()) else {
                    return true;
                };
                if *stamp == workspace.epoch {
                    continue;
                }
                *stamp = workspace.epoch;
                let Some(phi) = dataflow.phi_candidate(phi) else {
                    return true;
                };
                workspace
                    .pending
                    .extend(phi.incoming.iter().map(|incoming| incoming.value));
            }
        }
    }

    (range.start.index()..predicate.index()).any(|index| {
        dataflow.effect_summaries.get(index).is_none_or(|summary| {
            !summary.tags.is_empty() && !workspace.needs_instr(InstrRef(index))
        })
    })
}

pub(super) fn block_has_escaping_defs(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    condition: &ShortCircuitCandidate,
    block: super::super::BlockRef,
) -> bool {
    let range = cfg.blocks[block.index()].instrs;
    (range.start.index()..range.end()).any(|instr| {
        dataflow.instr_defs[instr]
            .iter()
            .copied()
            .any(|def| dataflow.def_has_use_outside(cfg, def, &condition.blocks))
    })
}

pub(super) fn truncate_condition_at(
    condition: &ShortCircuitCandidate,
    cut_index: usize,
) -> Option<ShortCircuitCandidate> {
    let ShortCircuitExit::BranchExit { falsy, .. } = condition.exit else {
        return None;
    };
    let cut_ref = ShortCircuitNodeRef(cut_index);
    let cut_header = condition.nodes[cut_index].header;
    let mut nodes = condition.nodes[..cut_index].to_vec();
    let mut replaced = false;
    for node in &mut nodes {
        for target in [&mut node.truthy, &mut node.falsy] {
            if matches!(target, ShortCircuitTarget::TruthyExit) {
                return None;
            }
            if *target == ShortCircuitTarget::Node(cut_ref) {
                *target = ShortCircuitTarget::TruthyExit;
                replaced = true;
            } else if matches!(target, ShortCircuitTarget::Node(node) if node.index() >= cut_index)
            {
                return None;
            }
        }
    }
    if !replaced {
        return None;
    }
    let blocks = nodes
        .iter()
        .map(|node| node.header)
        .collect::<BTreeSet<_>>();
    Some(ShortCircuitCandidate {
        header: condition.header,
        blocks,
        entry: condition.entry,
        nodes,
        exit: ShortCircuitExit::BranchExit {
            truthy: cut_header,
            falsy,
        },
        result_reg: None,
        result_phi_id: None,
        entry_value: None,
        value_incomings: Vec::new(),
        reducible: true,
    })
}
