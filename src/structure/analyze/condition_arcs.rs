//! 为直接条件候选合成弧证据并执行副作用/定义逃逸检查；依赖 CFG 与 SSA，不负责候选排序。

use super::*;
use crate::structure::cfg::EvaluationDependency;

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
            let Some((truthy_edge, falsy_edge)) = cfg.predicate_edges(&proto.instrs, node.header)
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

pub(super) fn safe_condition_candidate(
    proto: &LoweredProto,
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
            (!condition_node_can_be_absorbed(
                proto,
                cfg,
                dataflow,
                candidate,
                node.header,
                workspace,
            ))
            .then_some(index)
        });
    match cut_index {
        Some(cut_index) => truncate_condition_at(candidate, cut_index),
        None => Some(candidate.clone()),
    }
}

pub(super) fn condition_node_can_be_absorbed(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    candidate: &ShortCircuitCandidate,
    header: super::super::BlockRef,
    workspace: &mut ConditionSafetyWorkspace,
) -> bool {
    !workspace.value_headers.contains(&header)
        && !dataflow.block_defs_have_use_outside(cfg, header, &candidate.blocks)
        && !block_has_unabsorbed_effects(proto, cfg, dataflow, header, workspace)
}

pub(super) struct ConditionSafetyWorkspace {
    value_headers: BTreeSet<super::super::BlockRef>,
    source_initializers: Vec<bool>,
    epoch: usize,
    needed_instr_epochs: Vec<usize>,
    def_epochs: Vec<usize>,
    phi_epochs: Vec<usize>,
    pending: Vec<EvaluationDependency>,
}

impl ConditionSafetyWorkspace {
    pub(super) fn new(
        proto: &LoweredProto,
        cfg: &Cfg,
        graph: &GraphFacts,
        dataflow: &DataflowFacts,
        candidates: &[ShortCircuitCandidate],
    ) -> Self {
        let mut source_initializers = vec![false; proto.instrs.len()];
        for (_, _, value) in debug_scope_entries(proto, cfg, graph, dataflow) {
            if let super::super::SsaValue::Def(def) = value {
                source_initializers[dataflow.def_instr(def).index()] = true;
            }
        }
        Self {
            source_initializers,
            // 取值 DAG 的 phi 结果由 ValueDecision 消费；外层条件不能把它吞成
            // 只有 bool 出口的节点，否则 condition region 会嵌入另一个控制 owner。
            value_headers: candidates
                .iter()
                .filter(|candidate| matches!(candidate.exit, ShortCircuitExit::ValueMerge(_)))
                .filter(|candidate| !candidate.is_value_operand_only())
                .map(|candidate| candidate.header)
                .collect(),
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

    pub(super) fn source_initializer_blocks(&self, cfg: &Cfg) -> Vec<bool> {
        cfg.blocks
            .iter()
            .map(|block| {
                (block.instrs.start.index()..block.instrs.start.index() + block.instrs.len)
                    .any(|index| self.source_initializers[index])
            })
            .collect()
    }

    fn needs_instr(&self, instr: InstrRef) -> bool {
        self.needed_instr_epochs.get(instr.index()).copied() == Some(self.epoch)
    }
}

pub(super) fn block_has_unabsorbed_effects(
    proto: &LoweredProto,
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
    if !super::dependencies::mark_region_dependencies(
        cfg,
        dataflow,
        |candidate| candidate == block,
        super::dependencies::DependencyMarks {
            instructions: &mut workspace.needed_instr_epochs,
            defs: &mut workspace.def_epochs,
            phis: &mut workspace.phi_epochs,
            epoch: workspace.epoch,
        },
        &mut workspace.pending,
        dataflow.evaluation_inputs(predicate),
        |_| false,
    ) {
        return true;
    }
    (range.start.index()..predicate.index()).any(|index| {
        // 候选拒绝[SemanticBarrier:NamedRootWrite]：和值判定共享原 local 写入边界，
        // 不能在 value DAG 被拒绝后由 condition DAG 再吸收同一写入（regress_578）。
        // 初始化通常在 debug 活动区间开始前；即使未被谓词读取，也必须作为声明发射。
        workspace.source_initializers[index]
            || instr_writes_source_binding(proto, dataflow, InstrRef(index))
            // 候选拒绝[SemanticBarrier:EvaluationCount]：谓词依赖闭包只证明
            // producer 被使用，不证明它只被使用一次。条件内没有共享值声明，
            // 吸收多用的 CALL/GETTABLE 或计算会让 HIR 在每个读取处重新求值。
            // 字面量与透明 COPY 没有独立求值事件；其上游 producer 仍逐一定义检查。
            || (!matches!(proto.instrs[index],
                LowInstr::LoadNil(_) | LowInstr::LoadBool(_) | LowInstr::LoadConst(_)
                    | LowInstr::LoadInteger(_) | LowInstr::LoadNumber(_) | LowInstr::Move(_))
                && dataflow.instr_defs[index].iter().any(|def| {
                    dataflow.def_uses[def.index()].len() > 1
                        || dataflow.def_uses[def.index()].first().is_some_and(|site| {
                            dataflow.instr_effects[site.instr.index()].repeats_fixed_use(site.reg)
                        })
                        || !dataflow.def_phi_uses[def.index()].is_empty()
                }))
            || dataflow.effect_summaries.get(index).is_none_or(|summary| {
                summary.has_effect_tags() && !workspace.needs_instr(InstrRef(index))
            })
    })
}

pub(super) fn instr_writes_source_binding(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    instr: InstrRef,
) -> bool {
    let pcs = &proto.lowering_map.pc_map()[instr.index()];
    dataflow.instr_defs[instr.index()].iter().any(|def| {
        proto
            .debug_locals
            .source_visible_at(dataflow.def_reg(*def), pcs)
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
