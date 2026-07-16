//! 这个文件承载 HIR 初始恢复里真正的 lowering 内核。
//!
//! 外层 [analyze.rs](/Users/x3zvawq/workspace/unluac-rs/src/hir/analyze/mod.rs) 只负责组织模块和
//! 暴露主入口，这里集中放 proto 递归构造、线性 block 降低、edge phi copy 和 phi
//! 物化。单条 low-IR 指令到 HIR 语句的映射由 `instrs.rs` 负责，避免主流程再次
//! 膨胀成所有 lowering 细节的集合。

use std::collections::{BTreeMap, BTreeSet};

use super::super::promotion::{ProtoPromotionFacts, SlotEpochFacts};
use super::bindings::build_bindings;
use super::exprs::{expr_for_reg_at_block_exit, expr_for_ssa_value};
use super::helpers::{assign_stmt, decode_raw_string, empty_proto, unresolved_expr};
use super::short_circuit::{
    recover_short_value_merge_expr_with_allowed_blocks, value_merge_candidates_in_block,
};
use super::structure::build_structured_body;
use crate::ast::AstTargetDialect;
use crate::decompile::{DecompileContext, DecompileState};
use crate::hir::common::{
    HirBlock, HirExpr, HirLValue, HirProto, HirProtoRef, HirStmt, LocalId, ParamId, TempId,
    UpvalueId,
};
use crate::structure::{BlockRef, Cfg, CfgGraph, DataflowFacts, GraphFacts, OpenDefId, PhiId};
use crate::structure::{ShortCircuitExit, StructureFacts};
use crate::transformer::{
    AccessBase, AccessKey, CallKind, GetTableKind, InstrRef, LowInstr, LoweredProto, Reg,
    ResultPack, ValuePack,
};

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
    pub(super) phi_temps: Vec<TempId>,
    pub(super) instr_fixed_defs: Vec<Vec<TempId>>,
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
    pub(super) fn local_for_reg_in_block(&self, block: BlockRef, reg: Reg) -> Option<LocalId> {
        self.block_local_regs
            .get(&block)
            .and_then(|locals| locals.get(&reg))
            .copied()
    }

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
    pub(super) target: AstTargetDialect,
    pub(super) proto: &'a LoweredProto,
    pub(super) cfg: &'a Cfg,
    pub(super) graph_facts: &'a GraphFacts,
    pub(super) dataflow: &'a DataflowFacts,
    pub(super) structure: &'a StructureFacts,
    pub(super) child_refs: &'a [HirProtoRef],
    pub(super) bindings: ProtoBindings,
    pub(super) open_pack_owners: Vec<Option<InstrRef>>,
    pub(super) owned_open_producers: Vec<bool>,
}

#[derive(Default)]
pub(super) struct LowerArtifacts {
    pub(super) protos: Vec<HirProto>,
    pub(super) promotion_facts: Vec<ProtoPromotionFacts>,
}

struct LoweredProtoResult {
    id: HirProtoRef,
    mutable_upvalues: Vec<bool>,
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
    )
    .id)
}

fn lower_proto_node(
    target: AstTargetDialect,
    proto: &LoweredProto,
    cfg_graph: &CfgGraph,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    structure: &StructureFacts,
    artifacts: &mut LowerArtifacts,
) -> LoweredProtoResult {
    let cfg = &cfg_graph.cfg;
    let id = HirProtoRef(artifacts.protos.len());
    artifacts.protos.push(empty_proto(id));
    artifacts
        .promotion_facts
        .push(ProtoPromotionFacts::default());

    let child_results = proto
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
    let child_refs = child_results
        .iter()
        .map(|child| child.id)
        .collect::<Vec<_>>();
    let child_mutable_upvalues = child_results
        .into_iter()
        .map(|child| child.mutable_upvalues)
        .collect::<Vec<_>>();

    let slot_epochs = SlotEpochFacts::analyze(proto, cfg, graph_facts, dataflow);
    let bindings = build_bindings(
        proto,
        cfg,
        dataflow,
        structure,
        &slot_epochs,
        &child_mutable_upvalues,
    );
    let open_pack_owners = build_open_pack_owners(proto, cfg, dataflow);
    let mut owned_open_producers = vec![false; proto.instrs.len()];
    for def in &dataflow.open_defs {
        if open_pack_owners[def.id.index()].is_some() {
            owned_open_producers[def.instr.index()] = true;
        }
    }
    let lowering = ProtoLowering {
        target,
        proto,
        cfg,
        graph_facts,
        dataflow,
        structure,
        child_refs: &child_refs,
        bindings,
        open_pack_owners,
        owned_open_producers,
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
    artifacts.promotion_facts[id.index()] =
        ProtoPromotionFacts::from_dataflow(dataflow, &slot_epochs);

    LoweredProtoResult {
        id,
        mutable_upvalues: mutable_upvalues_for_proto(proto, &child_mutable_upvalues),
    }
}

fn mutable_upvalues_for_proto(
    proto: &LoweredProto,
    child_mutable_upvalues: &[Vec<bool>],
) -> Vec<bool> {
    let mut mutable = vec![false; usize::from(proto.upvalues.common.count)];
    for instr in &proto.instrs {
        match instr {
            LowInstr::SetUpvalue(set) => {
                let crate::transformer::UpvalueOperand::Upvalue(dst) = set.dst else {
                    continue;
                };
                if let Some(slot) = mutable.get_mut(dst.index()) {
                    *slot = true;
                }
            }
            LowInstr::Closure(closure) => {
                let Some(child_mutable) = child_mutable_upvalues.get(closure.proto.index()) else {
                    continue;
                };
                for (child_upvalue, can_write) in child_mutable.iter().copied().enumerate() {
                    if !can_write {
                        continue;
                    }
                    let Some(crate::transformer::CaptureSource::Upvalue(parent_upvalue)) = closure
                        .captures
                        .get(child_upvalue)
                        .map(|capture| capture.source)
                    else {
                        continue;
                    };
                    if let Some(slot) = mutable.get_mut(parent_upvalue.index()) {
                        *slot = true;
                    }
                }
            }
            _ => {}
        }
    }
    mutable
}

fn build_open_pack_owners(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
) -> Vec<Option<InstrRef>> {
    let mut owners = vec![None; dataflow.open_defs.len()];
    let mut conflicted = vec![false; dataflow.open_defs.len()];

    for consumer_index in 0..proto.instrs.len() {
        let consumer = InstrRef(consumer_index);
        let sources = dataflow.open_use_sources_at(consumer);
        if sources.has_entry() || sources.defs().len() != 1 {
            continue;
        }
        let def_id = *sources
            .defs()
            .iter()
            .next()
            .expect("single open source checked above");
        let Some(def) = dataflow.open_defs.get(def_id.index()) else {
            continue;
        };
        let consumer_block = cfg.instr_to_block[consumer_index];
        if def.block != consumer_block
            || !open_pack_bridge_has_owned_protocol(proto, def.instr, consumer)
        {
            continue;
        }

        match owners[def_id.index()] {
            None => owners[def_id.index()] = Some(consumer),
            Some(existing) if existing == consumer => {}
            Some(_) => conflicted[def_id.index()] = true,
        }
    }

    for (owner, conflicted) in owners.iter_mut().zip(conflicted) {
        if conflicted {
            *owner = None;
        }
    }
    owners
}

fn open_pack_bridge_has_owned_protocol(
    proto: &LoweredProto,
    producer: InstrRef,
    consumer: InstrRef,
) -> bool {
    let Some(start) = producer.index().checked_add(1) else {
        return false;
    };
    let Some(between) = proto.instrs.get(start..consumer.index()) else {
        return false;
    };

    if between.is_empty() {
        return true;
    }

    if matches!(
        proto.instrs.get(producer.index()),
        Some(LowInstr::VarArg(vararg)) if matches!(vararg.results, ResultPack::Open(_))
    ) {
        return true;
    }

    if between
        .iter()
        .all(|instr| matches!(instr, LowInstr::Close(_)))
    {
        // 只有 return/tail-call 协议会在表达式已经求值后、终结消费前执行词法 close。
        // 一般 consumer 若跨过 Close，可能把 producer 移到可观察的 __close 之后。
        return matches!(
            proto.instrs.get(consumer.index()),
            Some(LowInstr::Return(_) | LowInstr::TailCall(_))
        );
    }

    open_pack_bridge_is_method_setup(proto, producer, consumer, between)
        || open_pack_bridge_is_import_setup(proto, producer, consumer, between)
        || open_pack_bridge_is_callee_move(proto, producer, consumer, between)
}

fn open_pack_bridge_is_method_setup(
    proto: &LoweredProto,
    producer: InstrRef,
    consumer: InstrRef,
    between: &[LowInstr],
) -> bool {
    let Some(producer_start) = open_producer_start(proto, producer) else {
        return false;
    };
    let Some(LowInstr::Call(call)) = proto.instrs.get(consumer.index()) else {
        return false;
    };
    let ValuePack::Open(self_arg) = call.args else {
        return false;
    };
    let [LowInstr::Move(receiver), LowInstr::GetTable(method)] = between else {
        return false;
    };
    let crate::transformer::AccessBase::Reg(base) = method.base else {
        return false;
    };
    let crate::transformer::AccessKey::Const(method_key) = method.key else {
        return false;
    };

    matches!(call.kind, crate::transformer::CallKind::Method)
        && call
            .method_name
            .is_some_and(|hint| hint.const_ref == method_key)
        && method.kind == GetTableKind::Method
        && method.dst == call.callee
        && receiver.dst == self_arg
        && receiver.src == base
        && producer_start.index() > self_arg.index()
}

fn open_pack_bridge_is_import_setup(
    proto: &LoweredProto,
    producer: InstrRef,
    consumer: InstrRef,
    between: &[LowInstr],
) -> bool {
    let Some(producer_start) = open_producer_start(proto, producer) else {
        return false;
    };
    let Some(LowInstr::Call(call)) = proto.instrs.get(consumer.index()) else {
        return false;
    };
    let ValuePack::Open(args_start) = call.args else {
        return false;
    };
    let Some((LowInstr::GetTable(first), rest)) = between.split_first() else {
        return false;
    };

    matches!(call.kind, CallKind::Normal)
        && producer_start.index() >= args_start.index()
        && first.kind == GetTableKind::Import
        && first.dst == call.callee
        && matches!(first.base, AccessBase::Env)
        && matches!(first.key, AccessKey::Const(_))
        && rest.iter().all(|instr| {
            matches!(
                instr,
                LowInstr::GetTable(get)
                    if get.kind == GetTableKind::Import
                        && get.dst == first.dst
                        && get.base == AccessBase::Reg(first.dst)
                        && matches!(get.key, AccessKey::Const(_))
            )
        })
}

fn open_pack_bridge_is_callee_move(
    proto: &LoweredProto,
    producer: InstrRef,
    consumer: InstrRef,
    between: &[LowInstr],
) -> bool {
    let Some(producer_start) = open_producer_start(proto, producer) else {
        return false;
    };
    let Some(LowInstr::Call(call)) = proto.instrs.get(consumer.index()) else {
        return false;
    };
    let ValuePack::Open(args_start) = call.args else {
        return false;
    };
    let [LowInstr::Move(callee_move)] = between else {
        return false;
    };

    matches!(call.kind, CallKind::Normal)
        && producer_start.index() >= args_start.index()
        && callee_move.src.index() < producer_start.index()
        && callee_move.dst == call.callee
        && callee_move.dst.index() < args_start.index()
}

fn open_producer_start(proto: &LoweredProto, producer: InstrRef) -> Option<Reg> {
    match proto.instrs.get(producer.index())? {
        LowInstr::Call(call) => match call.results {
            ResultPack::Open(start) => Some(start),
            _ => None,
        },
        LowInstr::VarArg(vararg) => match vararg.results {
            ResultPack::Open(start) => Some(start),
            _ => None,
        },
        _ => None,
    }
}

impl ProtoLowering<'_> {
    pub(super) fn owns_open_pack(&self, def: OpenDefId, consumer: InstrRef) -> bool {
        self.open_pack_owners.get(def.index()).copied().flatten() == Some(consumer)
    }

    pub(super) fn open_pack_is_owned(&self, instr_ref: InstrRef) -> bool {
        self.owned_open_producers
            .get(instr_ref.index())
            .copied()
            .unwrap_or(false)
    }
}

fn build_proto_body(target: AstTargetDialect, lowering: &ProtoLowering<'_>) -> HirBlock {
    build_structured_body(target, lowering)
}

pub(super) fn lower_edge_phi_copies_for_edge(
    lowering: &ProtoLowering<'_>,
    edge_ref: crate::structure::EdgeRef,
) -> Vec<HirStmt> {
    let copies = lowering.structure.phi_edge_copies(edge_ref);
    if copies.is_empty() {
        return Vec::new();
    }

    let (targets, values): (Vec<HirLValue>, Vec<HirExpr>) = copies
        .iter()
        .map(|copy| {
            (
                HirLValue::Temp(lowering.bindings.phi_temps[copy.phi_id.index()]),
                expr_for_ssa_value(lowering, copy.value),
            )
        })
        .unzip();
    vec![assign_stmt(targets, values)]
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
        if is_suppressed(phi_id)
            || lowering.structure.phi_is_dead(phi_id)
            || lowering.structure.phi_is_edge_owned(phi_id)
        {
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
        lowering
            .structure
            .generic_phi_materializations_in_block(block)
            .iter()
            .copied()
            .filter(|phi| !is_suppressed(phi.phi_id))
            .filter(|phi| !lowering.structure.phi_is_dead(phi.phi_id))
            .filter(|phi| !lowering.structure.phi_is_edge_owned(phi.phi_id))
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
