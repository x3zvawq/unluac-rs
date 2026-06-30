//! 这个文件承载 HIR 初始恢复里真正的 lowering 内核。
//!
//! 外层 [analyze.rs](/Users/x3zvawq/workspace/unluac-rs/src/hir/analyze/mod.rs) 只负责组织模块和
//! 暴露主入口，这里集中放 proto 递归构造、线性 block 降低、edge phi copy 和 phi
//! 物化。单条 low-IR 指令到 HIR 语句的映射由 `instrs.rs` 负责，避免主流程再次
//! 膨胀成所有 lowering 细节的集合。

use std::collections::{BTreeMap, BTreeSet};

use super::super::promotion::ProtoPromotionFacts;
use super::bindings::build_bindings;
use super::exprs::{expr_for_reg_at_block_exit, lower_branch_cond};
use super::helpers::{
    assign_stmt, branch_stmt, build_label_map_for_summary, decode_raw_string, empty_proto,
    goto_stmt, unresolved_expr,
};
use super::instrs::{
    generic_for_control_update, generic_for_loop_continue_cond, is_control_terminator,
    lower_control_instr, lower_regular_instr,
};
use super::short_circuit::{
    recover_short_value_merge_expr_with_allowed_blocks, value_merge_candidates_in_block,
};
use super::structure::try_build_structured_body;
use crate::ast::AstTargetDialect;
use crate::decompile::{DecompileContext, DecompileState};
use crate::hir::common::{
    HirBlock, HirExpr, HirLValue, HirLabel, HirLabelId, HirProto, HirProtoRef, HirStmt, LocalId,
    ParamId, TempId, UpvalueId,
};
use crate::structure::{BlockRef, Cfg, CfgGraph, DataflowFacts, GraphFacts, PhiId};
use crate::structure::{ShortCircuitExit, StructureFacts};
use crate::transformer::{GenericForLoopInstr, InstrRef, LowInstr, LoweredProto, Reg};

pub(super) struct ProtoBindings {
    pub(super) params: Vec<ParamId>,
    pub(super) param_debug_hints: Vec<Option<String>>,
    pub(super) locals: Vec<LocalId>,
    pub(super) local_debug_hints: Vec<Option<String>>,
    pub(super) upvalues: Vec<UpvalueId>,
    pub(super) upvalue_debug_hints: Vec<Option<String>>,
    pub(super) temps: Vec<TempId>,
    pub(super) temp_debug_locals: Vec<Option<String>>,
    pub(super) fixed_temps: Vec<TempId>,
    pub(super) open_temps: Vec<TempId>,
    pub(super) phi_temps: Vec<TempId>,
    pub(super) instr_fixed_defs: Vec<Vec<TempId>>,
    pub(super) instr_open_defs: Vec<Option<TempId>>,
    pub(super) captured_temp_targets: BTreeMap<TempId, BoundSlotTarget>,
    pub(super) captured_temp_decl_locals: BTreeMap<TempId, LocalId>,
    pub(super) capture_empty_local_decls: BTreeMap<usize, Vec<LocalId>>,
    pub(super) closure_capture_targets: BTreeMap<(usize, usize), BoundSlotTarget>,
    pub(super) entry_local_regs: BTreeMap<Reg, LocalId>,
    pub(super) numeric_for_locals: BTreeMap<BlockRef, LocalId>,
    pub(super) generic_for_locals: BTreeMap<BlockRef, Vec<LocalId>>,
    pub(super) block_local_regs: BTreeMap<BlockRef, BTreeMap<Reg, LocalId>>,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(super) enum BoundSlotTarget {
    Local(LocalId),
}

impl BoundSlotTarget {
    pub(super) fn expr(self) -> HirExpr {
        match self {
            Self::Local(local) => HirExpr::LocalRef(local),
        }
    }

    pub(super) fn lvalue(self) -> HirLValue {
        match self {
            Self::Local(local) => HirLValue::Local(local),
        }
    }
}

impl ProtoBindings {
    pub(super) fn expr_for_temp(&self, temp: TempId) -> HirExpr {
        self.captured_temp_targets
            .get(&temp)
            .copied()
            .map_or(HirExpr::TempRef(temp), BoundSlotTarget::expr)
    }

    pub(super) fn lvalue_for_temp(&self, temp: TempId) -> HirLValue {
        self.captured_temp_targets
            .get(&temp)
            .copied()
            .map_or(HirLValue::Temp(temp), BoundSlotTarget::lvalue)
    }

    pub(super) fn closure_capture_target(
        &self,
        instr_ref: InstrRef,
        reg: Reg,
    ) -> Option<BoundSlotTarget> {
        self.closure_capture_targets
            .get(&(instr_ref.index(), reg.index()))
            .copied()
    }
}

pub(super) struct ProtoLowering<'a> {
    pub(super) proto: &'a LoweredProto,
    pub(super) cfg: &'a Cfg,
    pub(super) graph_facts: &'a GraphFacts,
    pub(super) dataflow: &'a DataflowFacts,
    pub(super) structure: &'a StructureFacts,
    pub(super) child_refs: &'a [HirProtoRef],
    pub(super) bindings: ProtoBindings,
    pub(super) dead_phis: BTreeSet<PhiId>,
}

#[derive(Default)]
pub(super) struct LowerArtifacts {
    pub(super) protos: Vec<HirProto>,
    pub(super) promotion_facts: Vec<ProtoPromotionFacts>,
}

pub(super) fn lower_proto(
    state: &DecompileState,
    context: &DecompileContext<'_>,
    artifacts: &mut LowerArtifacts,
) -> Result<HirProtoRef, crate::decompile::DecompileError> {
    let lowered = state.require_lowered()?;
    let cfg = state.require_cfg()?;
    let graph_facts = state.require_graph_facts()?;
    let dataflow = state.require_dataflow()?;
    let structure = state.require_structure_facts()?;
    Ok(lower_proto_node(
        context.requested_target,
        &lowered.main,
        cfg,
        graph_facts,
        dataflow,
        structure,
        artifacts,
    ))
}

fn lower_proto_node(
    target: AstTargetDialect,
    proto: &LoweredProto,
    cfg_graph: &CfgGraph,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    structure: &StructureFacts,
    artifacts: &mut LowerArtifacts,
) -> HirProtoRef {
    let cfg = &cfg_graph.cfg;
    let id = HirProtoRef(artifacts.protos.len());
    artifacts.protos.push(empty_proto(id));
    artifacts
        .promotion_facts
        .push(ProtoPromotionFacts::default());

    let child_refs = proto
        .children
        .iter()
        .zip(cfg_graph.children.iter())
        .zip(graph_facts.children.iter())
        .zip(dataflow.children.iter())
        .zip(structure.children.iter())
        .map(
            |((((child_proto, child_cfg), child_graph_facts), child_dataflow), child_structure)| {
                lower_proto_node(
                    target,
                    child_proto,
                    child_cfg,
                    child_graph_facts,
                    child_dataflow,
                    child_structure,
                    artifacts,
                )
            },
        )
        .collect::<Vec<_>>();

    let bindings = build_bindings(proto, cfg, dataflow, structure);
    let dead_phis = dataflow.compute_truly_dead_phis(cfg);
    let lowering = ProtoLowering {
        proto,
        cfg,
        graph_facts,
        dataflow,
        structure,
        child_refs: &child_refs,
        bindings,
        dead_phis,
    };

    artifacts.protos[id.index()] = HirProto {
        id,
        source: proto.source.as_ref().map(decode_raw_string),
        line_range: proto.line_range,
        signature: proto.signature,
        params: lowering.bindings.params.clone(),
        param_debug_hints: lowering.bindings.param_debug_hints.clone(),
        locals: lowering.bindings.locals.clone(),
        local_debug_hints: lowering.bindings.local_debug_hints.clone(),
        upvalues: lowering.bindings.upvalues.clone(),
        upvalue_debug_hints: lowering.bindings.upvalue_debug_hints.clone(),
        temps: lowering.bindings.temps.clone(),
        temp_debug_locals: lowering.bindings.temp_debug_locals.clone(),
        body: build_proto_body(target, &lowering),
        children: child_refs,
    };
    artifacts.promotion_facts[id.index()] = ProtoPromotionFacts::from_dataflow(proto, dataflow);

    id
}

fn build_proto_body(target: AstTargetDialect, lowering: &ProtoLowering<'_>) -> HirBlock {
    if let Some(body) = try_build_structured_body(target, lowering) {
        body
    } else {
        lower_label_goto_body(lowering)
    }
}

fn lower_label_goto_body(lowering: &ProtoLowering<'_>) -> HirBlock {
    let label_map = build_label_map_for_summary(lowering.cfg);
    let reachable_blocks = lowering
        .cfg
        .block_order
        .iter()
        .copied()
        .filter(|block| lowering.cfg.reachable_blocks.contains(block))
        .filter(|block| *block != lowering.cfg.exit_block)
        .collect::<Vec<_>>();

    let mut stmts = Vec::new();
    for (index, block) in reachable_blocks.iter().copied().enumerate() {
        if let Some(label_id) = label_map.get(&block) {
            stmts.push(HirStmt::Label(Box::new(HirLabel { id: *label_id })));
        }

        let next_block = reachable_blocks.get(index + 1).copied();
        stmts.extend(lower_block_with_edge_copies(
            lowering, block, next_block, &label_map,
        ));
    }

    HirBlock { stmts }
}

fn lower_block_with_edge_copies(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    next_block: Option<BlockRef>,
    label_map: &BTreeMap<BlockRef, HirLabelId>,
) -> Vec<HirStmt> {
    let range = lowering.cfg.blocks[block.index()].instrs;
    if range.is_empty() {
        return lower_linear_edge(lowering, block, next_block, label_map);
    }

    let last_instr = range
        .last()
        .expect("non-empty block should have a last instruction");
    let mut stmts = Vec::new();
    for instr_index in range.start.index()..range.end() {
        let instr_ref = InstrRef(instr_index);
        let instr = &lowering.proto.instrs[instr_index];
        if instr_ref == last_instr && is_control_terminator(instr) {
            stmts.extend(lower_control_instr_with_edge_copies(
                lowering, block, instr_ref, instr, next_block, label_map,
            ));
        } else {
            stmts.extend(lower_regular_instr(lowering, block, instr_ref, instr));
        }
    }

    if !is_control_terminator(&lowering.proto.instrs[last_instr.index()]) {
        stmts.extend(lower_linear_edge(lowering, block, next_block, label_map));
    }

    stmts
}

fn lower_linear_edge(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    next_block: Option<BlockRef>,
    label_map: &BTreeMap<BlockRef, HirLabelId>,
) -> Vec<HirStmt> {
    let Some(target) = lowering.cfg.unique_reachable_successor(block) else {
        return Vec::new();
    };
    if target == lowering.cfg.exit_block {
        return Vec::new();
    }

    lower_edge_block(lowering, block, target, next_block, label_map).stmts
}

fn lower_control_instr_with_edge_copies(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    instr: &LowInstr,
    next_block: Option<BlockRef>,
    label_map: &BTreeMap<BlockRef, HirLabelId>,
) -> Vec<HirStmt> {
    match instr {
        LowInstr::Jump(jump) => {
            lower_edge_block(
                lowering,
                block,
                lowering.cfg.instr_to_block[jump.target.index()],
                next_block,
                label_map,
            )
            .stmts
        }
        LowInstr::Branch(branch) => {
            let then_target = lowering.cfg.instr_to_block[branch.then_target.index()];
            let else_target = lowering.cfg.instr_to_block[branch.else_target.index()];
            vec![branch_stmt(
                lower_branch_cond(lowering, block, instr_ref, branch.cond),
                lower_edge_block(lowering, block, then_target, next_block, label_map),
                Some(lower_edge_block(
                    lowering,
                    block,
                    else_target,
                    next_block,
                    label_map,
                )),
            )]
        }
        LowInstr::GenericForLoop(generic_for) => vec![branch_stmt(
            generic_for_loop_continue_cond(lowering, block, instr_ref, generic_for),
            lower_generic_for_body_edge_block(lowering, block, generic_for, next_block, label_map),
            Some(lower_edge_block(
                lowering,
                block,
                lowering.cfg.instr_to_block[generic_for.exit_target.index()],
                next_block,
                label_map,
            )),
        )],
        _ => lower_control_instr(lowering, block, instr_ref, instr, label_map),
    }
}

fn lower_edge_block(
    lowering: &ProtoLowering<'_>,
    from: BlockRef,
    to: BlockRef,
    next_block: Option<BlockRef>,
    label_map: &BTreeMap<BlockRef, HirLabelId>,
) -> HirBlock {
    let mut stmts = lower_edge_phi_copies(lowering, from, to);
    if to != lowering.cfg.exit_block && Some(to) != next_block {
        stmts.push(goto_stmt(label_map[&to]));
    }
    HirBlock { stmts }
}

fn lower_edge_phi_copies(
    lowering: &ProtoLowering<'_>,
    from: BlockRef,
    to: BlockRef,
) -> Vec<HirStmt> {
    if to == lowering.cfg.exit_block {
        return Vec::new();
    }

    let mut targets = Vec::new();
    let mut values = Vec::new();
    for phi in lowering.dataflow.phi_candidates_in_block(to) {
        if lowering.dead_phis.contains(&phi.id) {
            continue;
        }
        targets.push(HirLValue::Temp(lowering.bindings.phi_temps[phi.id.index()]));
        values.push(expr_for_reg_at_block_exit(lowering, from, phi.reg));
    }

    if targets.is_empty() {
        Vec::new()
    } else {
        vec![assign_stmt(targets, values)]
    }
}

fn lower_generic_for_body_edge_block(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    generic_for: &GenericForLoopInstr,
    next_block: Option<BlockRef>,
    label_map: &BTreeMap<BlockRef, HirLabelId>,
) -> HirBlock {
    let instr_ref = lowering.cfg.blocks[block.index()]
        .instrs
        .last()
        .expect("generic-for-loop block should contain its terminator");
    let target = lowering.cfg.instr_to_block[generic_for.body_target.index()];
    let mut stmts = generic_for_control_update(lowering, block, instr_ref, generic_for);
    stmts.extend(lower_edge_block(lowering, block, target, next_block, label_map).stmts);
    HirBlock { stmts }
}

fn generic_phi_materializations_in_block<'a>(
    lowering: &'a ProtoLowering<'a>,
    block: BlockRef,
) -> impl Iterator<Item = crate::structure::GenericPhiMaterialization> + 'a {
    lowering
        .structure
        .generic_phi_materializations
        .iter()
        .copied()
        .filter(move |phi| phi.block == block)
}

/// 某些结构化路径会先把短路 header 的前缀语句物化出来，再跳到 merge block。
///
/// 这时 merge 上的 phi 表达式虽然跨过了候选区域，但其中引用的 header 临时值其实已经
/// 在当前 HIR 位置稳定存在。这里额外接收一组 `allowed_blocks`，显式告诉 phi 恢复逻辑
/// 哪些 block 的临时值已经“在更早的语句里落地”，避免把简单 `a and b` / `a or b`
/// 错误地退化回 `if + assign`。
pub(super) fn lower_phi_materialization_with_allowed_blocks_except(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    is_suppressed: impl Fn(PhiId) -> bool,
    allowed_blocks: &BTreeSet<BlockRef>,
) -> Vec<HirStmt> {
    let mut stmts = Vec::new();
    let mut covered_phi_ids = BTreeSet::new();
    let mut short_value_merges =
        value_merge_candidates_in_block(lowering, block).collect::<Vec<_>>();
    short_value_merges.sort_by_key(|candidate| match candidate.result_phi_id {
        Some(phi_id) => phi_id,
        None => unreachable!("value-merge short-circuit should carry a phi id"),
    });

    for short in short_value_merges {
        let Some(phi_id) = short.result_phi_id else {
            unreachable!("value-merge short-circuit should carry a phi id");
        };
        if is_suppressed(phi_id) || lowering.dead_phis.contains(&phi_id) {
            continue;
        }

        let ShortCircuitExit::ValueMerge(merge) = short.exit else {
            unreachable!("value merge candidate iterator should only yield value merges");
        };
        let Some(reg) = short.result_reg else {
            unreachable!("value merge short-circuit should carry a result reg");
        };
        let Some(temp) = lowering.bindings.phi_temps.get(phi_id.index()).copied() else {
            unreachable!("every phi id should have a temp binding");
        };
        covered_phi_ids.insert(phi_id);
        let value =
            recover_short_value_merge_expr_with_allowed_blocks(lowering, short, allowed_blocks)
                .unwrap_or_else(|| unresolved_phi_expr("short-circuit value merge", merge, reg));
        stmts.push(assign_stmt(vec![HirLValue::Temp(temp)], vec![value]));
    }

    stmts.extend(
        generic_phi_materializations_in_block(lowering, block)
            .filter(|phi| !is_suppressed(phi.phi_id))
            .filter(|phi| !lowering.dead_phis.contains(&phi.phi_id))
            .filter(|phi| !covered_phi_ids.contains(&phi.phi_id))
            .filter_map(|phi| {
                let temp = lowering
                    .bindings
                    .phi_temps
                    .get(phi.phi_id.index())
                    .copied()?;
                let value = generic_phi_materialization_value(lowering, phi);
                Some(assign_stmt(vec![HirLValue::Temp(temp)], vec![value]))
            }),
    );

    stmts
}

fn generic_phi_materialization_value(
    lowering: &ProtoLowering<'_>,
    phi: crate::structure::GenericPhiMaterialization,
) -> HirExpr {
    match phi.source {
        crate::structure::GenericPhiSource::IdomExit(source) => {
            expr_for_reg_at_block_exit(lowering, source, phi.reg)
        }
        crate::structure::GenericPhiSource::Unresolved => {
            unresolved_phi_expr("generic phi", phi.block, phi.reg)
        }
    }
}

fn unresolved_phi_expr(reason: &str, block: BlockRef, reg: Reg) -> HirExpr {
    unresolved_expr(format!(
        "{reason} block=#{} reg=r{}",
        block.index(),
        reg.index()
    ))
}
