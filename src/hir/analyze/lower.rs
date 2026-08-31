//! 这个文件承载 HIR 初始恢复里真正的 lowering 内核。
//!
//! 外层 [analyze.rs](/Users/x3zvawq/workspace/unluac-rs/src/hir/analyze/mod.rs) 只负责组织模块和
//! 暴露主入口，这里集中放 proto 递归构造和共享 lowering 上下文。final edge 的 phi
//! copy 由 plan 执行器消费；单条 low-IR 指令到 HIR 语句的映射由 `instrs.rs` 负责，
//! captured Luau shared closure 的词法 factory 由 `shared_closures.rs` 先冻结，再由这里
//! 预留并填充 synthetic proto；避免主流程重新猜 closure identity。

use std::collections::{BTreeMap, BTreeSet};

use super::super::promotion::{HomeSlotKey, ProtoPromotionFacts, SlotEpochFacts};
use super::bindings::build_bindings;
use super::global_decls::GlobalDeclProtocols;
use super::helpers::{decode_raw_string, empty_proto, return_stmt};
use super::instrs::local_decl_stmts;
use super::shared_closures::{
    CompositeCapture, CompositeFactoryPlan, CompositeFactoryRef, SharedClosurePlan,
    build_shared_closure_plan,
};
use super::structure::build_structured_body;
use crate::ast::AstTargetDialect;
use crate::decompile::{DecompileContext, DecompileState};
use crate::generate::GenerateMode;
use crate::hir::HirLowerError;
use crate::hir::common::{
    HirBlock, HirCapture, HirCaptureMode, HirClosureExpr, HirExpr, HirLValue, HirLocalDecl,
    HirProto, HirProtoRef, HirStmt, HirValuePack, LocalId, ParamId, TempId, UpvalueId,
};
use crate::recovery::{ProtoArtifactStage, ProtoFailure};
use crate::structure::{
    BlockRef, BlockTerminatorKind, CanonicalMoveIndex, Cfg, CfgGraph, DataflowFacts, GraphFacts,
    LoopSourceBindings, LoopVmProtocol, OpenDefId, PhiId, SsaValue, StructurePlan,
};
use crate::structure::{ReadyStructureFacts, StructureFacts};
use crate::transformer::{
    AccessBase, AccessKey, CallKind, CaptureSource, ClosureCreation, GetTableKind, InstrRef,
    LowInstr, LoweredProto, ProtoRef, Reg, ResultPack, SharedClosureRef, ValuePack,
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
    pub(super) temp_debug_scopes: Vec<Option<usize>>,
    pub(super) fixed_temps: Vec<TempId>,
    pub(super) phi_temps: Vec<TempId>,
    pub(super) loop_guard_temps: Vec<Option<TempId>>,
    pub(super) repeat_staged_temps: Vec<Vec<TempId>>,
    pub(super) instr_fixed_defs: Vec<Vec<TempId>>,
    pub(super) debug_temp_targets: BTreeMap<TempId, BoundSlotTarget>,
    pub(super) captured_temp_targets: BTreeMap<TempId, BoundSlotTarget>,
    pub(super) captured_temp_decl_locals: BTreeMap<TempId, LocalId>,
    pub(super) captured_local_home_slots: Vec<(LocalId, HomeSlotKey)>,
    pub(super) capture_empty_local_decls: BTreeMap<usize, Vec<LocalId>>,
    pub(super) capture_entry_local_decls: Vec<LocalId>,
    pub(super) debug_entry_local_decls: Vec<LocalId>,
    pub(super) capture_region_local_decls: BTreeMap<crate::structure::RegionId, Vec<LocalId>>,
    pub(super) closure_capture_targets: BTreeMap<(usize, usize), BoundSlotTarget>,
    pub(super) lexical_close_scope_starts: BTreeMap<usize, usize>,
    pub(super) reference_captured_regs: Vec<bool>,
    pub(super) entry_local_regs: BTreeMap<Reg, LocalId>,
    pub(super) numeric_for_locals: BTreeMap<BlockRef, LocalId>,
    pub(super) numeric_binding_phi_locals: Vec<Option<LocalId>>,
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
    fn temp_target(&self, temp: TempId) -> Option<BoundSlotTarget> {
        self.debug_temp_targets
            .get(&temp)
            .or_else(|| self.captured_temp_targets.get(&temp))
            .copied()
    }

    pub(super) fn local_for_reg_in_block(&self, block: BlockRef, reg: Reg) -> Option<LocalId> {
        self.block_local_regs
            .get(&block)
            .and_then(|locals| locals.get(&reg))
            .copied()
    }

    pub(super) fn expr_for_temp(&self, temp: TempId) -> HirExpr {
        self.temp_target(temp)
            .map_or(HirExpr::TempRef(temp), BoundSlotTarget::expr)
    }

    pub(super) fn lvalue_for_temp(&self, temp: TempId) -> HirLValue {
        self.temp_target(temp)
            .map_or(HirLValue::Temp(temp), BoundSlotTarget::lvalue)
    }

    /// 固定定义优先投影到当前 block 的 local owner，否则回退到 temp target。
    /// 同一个 VM 结果的读写必须使用这对投影，避免 closure 的 self capture 与接收
    /// closure 的 binding 分裂成两个身份。
    pub(super) fn expr_for_fixed_def(&self, block: BlockRef, reg: Reg, temp: TempId) -> HirExpr {
        self.local_for_reg_in_block(block, reg)
            .map_or_else(|| self.expr_for_temp(temp), HirExpr::LocalRef)
    }

    pub(super) fn lvalue_for_fixed_def(
        &self,
        block: BlockRef,
        reg: Reg,
        temp: TempId,
    ) -> HirLValue {
        self.local_for_reg_in_block(block, reg)
            .map_or_else(|| self.lvalue_for_temp(temp), HirLValue::Local)
    }

    pub(super) fn expr_for_phi(&self, phi: PhiId) -> HirExpr {
        self.numeric_binding_phi_locals
            .get(phi.index())
            .copied()
            .flatten()
            .map_or_else(
                || self.expr_for_temp(self.phi_temps[phi.index()]),
                HirExpr::LocalRef,
            )
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

    pub(super) fn reg_is_reference_captured(&self, reg: Reg) -> bool {
        self.reference_captured_regs
            .get(reg.index())
            .copied()
            .unwrap_or(false)
    }
}

pub(super) struct ProtoLowering<'a> {
    pub(super) target: AstTargetDialect,
    pub(super) proto: &'a LoweredProto,
    pub(super) cfg: &'a Cfg,
    pub(super) dataflow: &'a DataflowFacts,
    pub(super) structure: &'a ReadyStructureFacts,
    pub(super) child_refs: &'a [HirProtoRef],
    pub(super) bindings: ProtoBindings,
    pub(super) self_value_capture_locals: BTreeMap<InstrRef, LocalId>,
    pub(super) shared_closure_locals: BTreeMap<SharedClosureRef, (LocalId, ProtoRef)>,
    pub(super) captured_shared_closures: CapturedSharedClosureLowering,
    pub(super) open_pack_owners: Vec<Option<InstrRef>>,
    pub(super) owned_open_producers: Vec<bool>,
    pub(super) global_decls: GlobalDeclProtocols,
}

pub(super) struct CapturedSharedClosureLowering {
    plan: SharedClosurePlan,
    factory_locals: Vec<LocalId>,
    capture_barriers: Vec<Option<SharedCaptureBarrier>>,
    composite_protos: Vec<HirProtoRef>,
}

pub(super) struct SharedCaptureBarrier {
    pub(super) box_local: LocalId,
    pub(super) snapshots: Vec<Option<LocalId>>,
}

#[derive(Default)]
pub(super) struct LowerArtifacts {
    pub(super) protos: Vec<HirProto>,
    pub(super) promotion_facts: Vec<ProtoPromotionFacts>,
}

pub(super) struct LoweredProtoResult {
    pub(super) id: HirProtoRef,
    source_proto_id: usize,
    mutable_upvalues: Vec<bool>,
}

struct ProtoLowerFrame<'a> {
    target: AstTargetDialect,
    proto: &'a LoweredProto,
    cfg_graph: &'a CfgGraph,
    graph_facts: &'a GraphFacts,
    dataflow: &'a DataflowFacts,
    structure: &'a StructureFacts,
    id: HirProtoRef,
    source_proto_id: usize,
    captured_shared_plan: Option<Result<SharedClosurePlan, HirLowerError>>,
    composite_protos: Vec<HirProtoRef>,
    next_child: usize,
    child_results: Vec<LoweredProtoResult>,
}

#[derive(Clone, Copy)]
struct ProtoNodeFacts<'a> {
    proto: &'a LoweredProto,
    cfg_graph: &'a CfgGraph,
    graph_facts: &'a GraphFacts,
    dataflow: &'a DataflowFacts,
    structure: &'a StructureFacts,
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
        ProtoNodeFacts {
            proto: &lowered.main,
            cfg_graph: cfg,
            graph_facts,
            dataflow,
            structure,
        },
        artifacts,
        context.options.generate.mode == GenerateMode::Permissive,
    )?
    .id)
}

fn lower_proto_node(
    target: AstTargetDialect,
    node: ProtoNodeFacts<'_>,
    artifacts: &mut LowerArtifacts,
    recover_failures: bool,
) -> Result<LoweredProtoResult, HirLowerError> {
    fn make_frame<'a>(
        target: AstTargetDialect,
        node: ProtoNodeFacts<'a>,
        artifacts: &mut LowerArtifacts,
        source_proto_id: usize,
    ) -> ProtoLowerFrame<'a> {
        let id = HirProtoRef(artifacts.protos.len());
        artifacts.protos.push(empty_proto(id));
        artifacts
            .promotion_facts
            .push(ProtoPromotionFacts::default());
        let captured_shared_plan = node.structure.ready().map(|structure| {
            build_shared_closure_plan(
                node.proto,
                node.cfg_graph,
                node.graph_facts,
                node.dataflow,
                structure.plan(),
            )
        });
        let composite_protos = captured_shared_plan
            .as_ref()
            .and_then(|plan| plan.as_ref().ok())
            .map_or_else(Vec::new, |plan| {
                reserve_composite_factory_protos(plan.composites().len(), artifacts)
            });
        ProtoLowerFrame {
            target,
            proto: node.proto,
            cfg_graph: node.cfg_graph,
            graph_facts: node.graph_facts,
            dataflow: node.dataflow,
            structure: node.structure,
            id,
            source_proto_id,
            captured_shared_plan,
            composite_protos,
            next_child: 0,
            child_results: Vec::new(),
        }
    }

    let mut stack = vec![make_frame(target, node, artifacts, 0)];
    let mut next_source_proto_id = 1usize;
    loop {
        let child = {
            let frame = stack.last_mut().expect("HIR proto frame is non-empty");
            if frame.proto.children.len() != frame.cfg_graph.children.len()
                || frame.proto.children.len() != frame.graph_facts.children.len()
                || frame.proto.children.len() != frame.dataflow.children.len()
                || frame.proto.children.len() != frame.structure.children.len()
            {
                return Err(HirLowerError::invalid("proto fact child counts disagree"));
            }
            let index = frame.next_child;
            let child = frame.proto.children.get(index).map(|proto| {
                (
                    index,
                    proto,
                    &frame.cfg_graph.children[index],
                    &frame.graph_facts.children[index],
                    &frame.dataflow.children[index],
                    &frame.structure.children[index],
                )
            });
            if child.is_some() {
                frame.next_child += 1;
            }
            child
        };
        if let Some((
            _index,
            child_proto,
            child_cfg,
            child_graph,
            child_dataflow,
            child_structure,
        )) = child
        {
            let source_proto_id = next_source_proto_id;
            next_source_proto_id += 1;
            stack.push(make_frame(
                target,
                ProtoNodeFacts {
                    proto: child_proto,
                    cfg_graph: child_cfg,
                    graph_facts: child_graph,
                    dataflow: child_dataflow,
                    structure: child_structure,
                },
                artifacts,
                source_proto_id,
            ));
            continue;
        }

        let mut frame = stack.pop().expect("HIR proto frame is non-empty");
        let result = if let Some(failure) = frame.structure.failure() {
            fill_failed_proto(&frame, failure.clone(), artifacts)
        } else {
            match lower_proto_one(&mut frame, artifacts) {
                Ok(result) => result,
                Err(error) if recover_failures => {
                    super::artifact_recovery::discard_composite_factory_protos(
                        &mut frame.composite_protos,
                        &mut frame.child_results,
                        artifacts,
                    )?;
                    let ready = frame
                        .structure
                        .ready()
                        .ok_or_else(|| HirLowerError::invalid("missing ready structure facts"))?;
                    let failure = ProtoFailure {
                        proto: frame.source_proto_id,
                        failed_stage: ProtoArtifactStage::Hir,
                        last_completed_stage: ProtoArtifactStage::Structure,
                        error: error.to_string().into(),
                        last_completed_dump: crate::structure::dump_structure_proto(
                            frame.source_proto_id,
                            ready,
                        )
                        .into(),
                    };
                    fill_failed_proto(&frame, failure, artifacts)
                }
                Err(error) => return Err(error),
            }
        };
        if let Some(parent) = stack.last_mut() {
            parent.child_results.push(result);
        } else {
            return Ok(result);
        }
    }
}

fn lower_proto_one(
    frame: &mut ProtoLowerFrame<'_>,
    artifacts: &mut LowerArtifacts,
) -> Result<LoweredProtoResult, HirLowerError> {
    let target = frame.target;
    let proto = frame.proto;
    let cfg_graph = frame.cfg_graph;
    let graph_facts = frame.graph_facts;
    let dataflow = frame.dataflow;
    let structure = frame
        .structure
        .ready()
        .ok_or_else(|| HirLowerError::invalid("missing ready structure facts"))?;
    let id = frame.id;
    let captured_shared_plan = frame
        .captured_shared_plan
        .take()
        .ok_or_else(|| HirLowerError::invalid("missing HIR proto lowering plan"))??;
    let composite_protos = frame.composite_protos.clone();
    let child_results = &frame.child_results;
    let cfg = &cfg_graph.cfg;
    let child_refs = child_results
        .iter()
        .map(|child| child.id)
        .collect::<Vec<_>>();
    let child_mutable_upvalues = child_results
        .iter()
        .map(|child| child.mutable_upvalues.clone())
        .collect::<Vec<_>>();
    fill_composite_factory_protos(
        proto,
        &child_refs,
        &captured_shared_plan,
        &composite_protos,
        artifacts,
    )?;

    let slot_epochs = SlotEpochFacts::analyze(proto, cfg, graph_facts, dataflow);
    let mut bindings = build_bindings(
        proto,
        cfg,
        graph_facts,
        dataflow,
        structure,
        &slot_epochs,
        &child_mutable_upvalues,
    );
    let self_value_capture_locals = build_self_value_capture_locals(proto, &mut bindings);
    let shared_closure_locals =
        build_shared_closure_locals(proto, &captured_shared_plan, &mut bindings);
    let captured_shared_closures = CapturedSharedClosureLowering::new(
        captured_shared_plan,
        composite_protos.clone(),
        proto,
        dataflow,
        &mut bindings,
    );
    let open_pack_owners = build_open_pack_owners(proto, cfg, dataflow);
    let mut owned_open_producers = vec![false; proto.instrs.len()];
    for def in &dataflow.open_defs {
        if open_pack_owners[def.id.index()].is_some() {
            owned_open_producers[def.instr.index()] = true;
        }
    }
    let global_decls = GlobalDeclProtocols::analyze(target, proto, cfg, dataflow);
    let lowering = ProtoLowering {
        target,
        proto,
        cfg,
        dataflow,
        structure,
        child_refs: &child_refs,
        bindings,
        self_value_capture_locals,
        shared_closure_locals,
        captured_shared_closures,
        open_pack_owners,
        owned_open_producers,
        global_decls,
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
        physical_root_temps: BTreeSet::new(),
        physical_root_locals: BTreeSet::new(),
        upvalues: lowering.bindings.upvalues.clone(),
        upvalue_debug_hints: lowering.bindings.upvalue_debug_hints.clone(),
        temps: lowering.bindings.temps.clone(),
        temp_debug_locals: lowering.bindings.temp_debug_locals.clone(),
        temp_debug_scopes: lowering.bindings.temp_debug_scopes.clone(),
        body: build_proto_body(id, &lowering)?,
        children: lowering.hir_children(),
        failure: None,
        detached_children: Vec::new(),
    };
    let mut promotion_facts = ProtoPromotionFacts::from_plan(
        proto,
        dataflow,
        structure.plan(),
        &slot_epochs,
        &lowering.bindings.fixed_temps,
        &lowering.bindings.phi_temps,
    );
    // `entry_local_regs` 是 Entry(reg) 的可见 binding；它与 SSA entry leaf 一样属于
    // `(reg, epoch 0)`。把这份已知身份带入 simplify，避免异槽 reference capture 被误判
    // 为可能观察任意 local 写入。后续异槽合并仍会通过 promotion invalidation 使其失效。
    for (&reg, &local) in &lowering.bindings.entry_local_regs {
        promotion_facts.record_local_home_slot(local, HomeSlotKey::new(reg.index(), 0));
    }
    for &(local, home) in &lowering.bindings.captured_local_home_slots {
        promotion_facts.record_local_home_slot(local, home);
    }
    record_loop_binding_local_homes(
        structure.plan(),
        &slot_epochs,
        &lowering.bindings,
        &mut promotion_facts,
    );
    artifacts.promotion_facts[id.index()] = promotion_facts;

    Ok(LoweredProtoResult {
        id,
        source_proto_id: frame.source_proto_id,
        mutable_upvalues: mutable_upvalues_for_proto(proto, &child_mutable_upvalues),
    })
}

fn record_loop_binding_local_homes(
    plan: &StructurePlan,
    slot_epochs: &SlotEpochFacts,
    bindings: &ProtoBindings,
    facts: &mut ProtoPromotionFacts,
) {
    for (loop_id, loop_plan) in plan.loops() {
        match (loop_plan.source_bindings, plan.loop_protocol(loop_id)) {
            (
                Some(LoopSourceBindings::Numeric(reg)),
                Some(LoopVmProtocol::NumericFor(protocol)),
            ) => {
                let Some(local) = bindings.numeric_for_locals.get(&loop_plan.header).copied()
                else {
                    continue;
                };
                facts.record_local_home_slot(
                    local,
                    HomeSlotKey::new(reg.index(), slot_epochs.epoch_at(reg, protocol.init_instr)),
                );
                let Some(BlockTerminatorKind::NumericForLoop { instr, .. }) = plan
                    .block_terminator(loop_plan.header)
                    .map(|terminator| terminator.kind)
                else {
                    continue;
                };
                facts.record_local_home_slot(
                    local,
                    HomeSlotKey::new(reg.index(), slot_epochs.epoch_at(reg, instr)),
                );
            }
            (
                Some(LoopSourceBindings::Generic(regs)),
                Some(LoopVmProtocol::GenericFor(protocol)),
            ) => {
                let Some(locals) = bindings.generic_for_locals.get(&loop_plan.header) else {
                    continue;
                };
                for (offset, local) in locals.iter().copied().enumerate() {
                    let reg = Reg(regs.start.index() + offset);
                    facts.record_local_home_slot(
                        local,
                        HomeSlotKey::new(
                            reg.index(),
                            slot_epochs.epoch_at(reg, protocol.call_instr),
                        ),
                    );
                }
            }
            _ => {}
        }
    }
}

fn build_self_value_capture_locals(
    proto: &LoweredProto,
    bindings: &mut ProtoBindings,
) -> BTreeMap<InstrRef, LocalId> {
    proto
        .instrs
        .iter()
        .enumerate()
        .filter_map(|(index, instr)| {
            let LowInstr::Closure(closure) = instr else {
                return None;
            };
            closure
                .captures
                .iter()
                .any(|capture| {
                    matches!(capture.source, CaptureSource::ByValue(reg) if reg == closure.dst)
                })
                .then(|| {
                    let local = LocalId(bindings.locals.len());
                    bindings.locals.push(local);
                    bindings.local_debug_hints.push(None);
                    (InstrRef(index), local)
                })
        })
        .collect()
}

fn fill_failed_proto(
    frame: &ProtoLowerFrame<'_>,
    failure: ProtoFailure,
    artifacts: &mut LowerArtifacts,
) -> LoweredProtoResult {
    let proto = frame.proto;
    let id = frame.id;
    let named_vararg_locals = usize::from(proto.signature.has_vararg_param_reg);
    let detached_children = frame
        .child_results
        .iter()
        .enumerate()
        .map(|(index, child)| (LocalId(named_vararg_locals + index), child.id))
        .collect::<Vec<_>>();
    let locals = (0..named_vararg_locals + detached_children.len())
        .map(LocalId)
        .collect::<Vec<_>>();
    let mut local_debug_hints = vec![None; named_vararg_locals];
    local_debug_hints.extend(
        frame
            .child_results
            .iter()
            .map(|child| Some(format!("unluac_proto_{}", child.source_proto_id))),
    );
    let child_mutable_upvalues = frame
        .child_results
        .iter()
        .map(|child| child.mutable_upvalues.clone())
        .collect::<Vec<_>>();

    artifacts.protos[id.index()] = HirProto {
        id,
        source: proto.source.as_ref().map(decode_raw_string),
        line_range: proto.line_range,
        signature: proto.signature,
        params: (0..usize::from(proto.signature.num_params))
            .map(ParamId)
            .collect(),
        param_debug_hints: vec![None; usize::from(proto.signature.num_params)],
        locals,
        local_debug_hints,
        physical_root_temps: BTreeSet::new(),
        physical_root_locals: BTreeSet::new(),
        upvalues: (0..usize::from(proto.upvalues.common.count))
            .map(UpvalueId)
            .collect(),
        upvalue_debug_hints: (0..usize::from(proto.upvalues.common.count))
            .map(|index| {
                proto
                    .debug_info
                    .common
                    .upvalue_names
                    .get(index)
                    .and_then(|name| name.as_ref().map(decode_raw_string))
            })
            .collect(),
        temps: Vec::new(),
        temp_debug_locals: Vec::new(),
        temp_debug_scopes: Vec::new(),
        body: HirBlock::default(),
        children: frame.child_results.iter().map(|child| child.id).collect(),
        failure: Some(failure),
        detached_children,
    };

    LoweredProtoResult {
        id,
        source_proto_id: frame.source_proto_id,
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

fn build_shared_closure_locals(
    proto: &LoweredProto,
    captured_plan: &SharedClosurePlan,
    bindings: &mut ProtoBindings,
) -> BTreeMap<SharedClosureRef, (LocalId, ProtoRef)> {
    let mut occurrences = BTreeMap::<SharedClosureRef, (usize, ProtoRef)>::new();
    for (index, closure) in proto
        .instrs
        .iter()
        .enumerate()
        .filter_map(|(index, instr)| match instr {
            LowInstr::Closure(closure) if closure.captures.is_empty() => Some((index, closure)),
            _ => None,
        })
    {
        if captured_plan.is_consumed(InstrRef(index)) {
            continue;
        }
        let ClosureCreation::Reusable(identity) = closure.creation else {
            continue;
        };
        let (count, _) = occurrences.entry(identity).or_insert((0, closure.proto));
        *count += 1;
    }
    occurrences
        .into_iter()
        .filter(|(_, (count, _))| *count > 1)
        .map(|(identity, (_, proto))| {
            let local = LocalId(bindings.locals.len());
            bindings.locals.push(local);
            bindings.local_debug_hints.push(None);
            (identity, (local, proto))
        })
        .collect()
}

impl CapturedSharedClosureLowering {
    fn new(
        plan: SharedClosurePlan,
        composite_protos: Vec<HirProtoRef>,
        proto: &LoweredProto,
        dataflow: &DataflowFacts,
        bindings: &mut ProtoBindings,
    ) -> Self {
        let mut factory_locals = Vec::with_capacity(plan.composites().len());
        let mut capture_barriers = Vec::with_capacity(plan.composites().len());
        let mut canonical_moves = CanonicalMoveIndex::new(proto, dataflow);
        for composite in plan.composites() {
            let instr = composite.anchor;
            let index = instr.index();
            let local = LocalId(bindings.locals.len());
            bindings.locals.push(local);
            bindings.local_debug_hints.push(None);
            factory_locals.push(local);

            let owner_dst = match proto.instrs.get(index) {
                Some(LowInstr::Closure(closure)) => closure.dst,
                _ => {
                    capture_barriers.push(None);
                    continue;
                }
            };
            let sources = &composite.outer_captures;
            let mut snapshots = vec![None; sources.len()];
            for (source, snapshot) in sources.iter().copied().zip(&mut snapshots) {
                if !matches!(source, CaptureSource::ByValue(reg) if reg != owner_dst)
                    || !capture_needs_non_reflexive_barrier(
                        proto,
                        dataflow,
                        instr,
                        source,
                        &mut canonical_moves,
                    )
                {
                    continue;
                }
                let local = LocalId(bindings.locals.len());
                bindings.locals.push(local);
                bindings.local_debug_hints.push(None);
                *snapshot = Some(local);
            }
            let barrier = snapshots.iter().any(Option::is_some).then(|| {
                let box_local = LocalId(bindings.locals.len());
                bindings.locals.push(box_local);
                bindings.local_debug_hints.push(None);
                SharedCaptureBarrier {
                    box_local,
                    snapshots,
                }
            });
            capture_barriers.push(barrier);
        }
        Self {
            plan,
            factory_locals,
            capture_barriers,
            composite_protos,
        }
    }

    pub(super) fn factory_local(&self, factory: CompositeFactoryRef) -> LocalId {
        self.factory_locals[factory.0]
    }

    pub(super) fn composite_proto(&self, id: CompositeFactoryRef) -> HirProtoRef {
        self.composite_protos[id.0]
    }

    pub(super) fn composite_plan(&self, id: CompositeFactoryRef) -> &CompositeFactoryPlan {
        &self.plan.composites()[id.0]
    }

    pub(super) fn capture_barrier(
        &self,
        factory: CompositeFactoryRef,
    ) -> Option<&SharedCaptureBarrier> {
        self.capture_barriers[factory.0].as_ref()
    }
}

fn capture_needs_non_reflexive_barrier(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    instr: InstrRef,
    source: CaptureSource,
    canonical_moves: &mut CanonicalMoveIndex<'_>,
) -> bool {
    let CaptureSource::ByValue(reg) = source else {
        return false;
    };
    let Ok(SsaValue::Def(def)) = canonical_moves.resolve(dataflow.use_value(instr, reg)) else {
        return false;
    };
    let def_instr = dataflow.def_instr(def);
    match proto.instrs.get(def_instr.index()) {
        Some(LowInstr::LoadNumber(load)) => load.value.is_nan(),
        Some(LowInstr::LoadConst(load)) => {
            match proto.constants.common.literals.get(load.value.index()) {
                Some(crate::parser::RawLiteralConst::Number(value)) => value.is_nan(),
                Some(crate::parser::RawLiteralConst::Vector(value)) => value
                    .components
                    .iter()
                    .any(|bits| f32::from_bits(*bits).is_nan()),
                Some(crate::parser::RawLiteralConst::Complex { real, imag }) => {
                    real.is_nan() || imag.is_nan()
                }
                _ => false,
            }
        }
        _ => false,
    }
}

fn reserve_composite_factory_protos(
    count: usize,
    artifacts: &mut LowerArtifacts,
) -> Vec<HirProtoRef> {
    (0..count)
        .map(|_| {
            let id = HirProtoRef(artifacts.protos.len());
            artifacts.protos.push(empty_proto(id));
            artifacts
                .promotion_facts
                .push(ProtoPromotionFacts::default());
            id
        })
        .collect()
}

fn fill_composite_factory_protos(
    proto: &LoweredProto,
    child_refs: &[HirProtoRef],
    plan: &SharedClosurePlan,
    ids: &[HirProtoRef],
    artifacts: &mut LowerArtifacts,
) -> Result<(), HirLowerError> {
    for (composite, id) in plan.composites().iter().zip(ids) {
        artifacts.protos[id.index()] =
            build_composite_factory_proto(*id, proto, child_refs, composite)?;
    }
    Ok(())
}

fn build_composite_factory_proto(
    id: HirProtoRef,
    proto: &LoweredProto,
    child_refs: &[HirProtoRef],
    plan: &CompositeFactoryPlan,
) -> Result<HirProto, HirLowerError> {
    let error = || HirLowerError::UnrepresentableRepeatedCapturedSharedClosure {
        shared_index: plan.root_shared.0,
        instr: plan.anchor.index(),
    };
    let owner = proto
        .children
        .get(plan.lexical_owner_proto.index())
        .ok_or_else(error)?;
    let mut body = HirBlock::default();
    let mut children = Vec::new();
    let mut seen_children = BTreeSet::new();

    for (index, node) in plan.nodes.iter().enumerate() {
        let child = proto.children.get(node.proto.index()).ok_or_else(error)?;
        if usize::from(child.upvalues.common.count) != node.captures.len() {
            return Err(error());
        }
        let child_ref = *child_refs.get(node.proto.index()).ok_or_else(error)?;
        if seen_children.insert(child_ref) {
            children.push(child_ref);
        }

        let local = LocalId(index);
        let captures = node
            .captures
            .iter()
            .map(|capture| {
                let (mode, value) = match *capture {
                    CompositeCapture::Outer(outer) => {
                        if outer >= plan.outer_captures.len() {
                            return None;
                        }
                        (
                            HirCaptureMode::ByReference,
                            HirExpr::UpvalueRef(UpvalueId(outer)),
                        )
                    }
                    CompositeCapture::Dependency(dependency) => {
                        if dependency.index() >= index {
                            return None;
                        }
                        (
                            HirCaptureMode::ByValue,
                            HirExpr::LocalRef(LocalId(dependency.index())),
                        )
                    }
                };
                Some(HirCapture { mode, value })
            })
            .collect::<Option<Vec<_>>>()
            .ok_or_else(error)?;
        let closure = HirExpr::Closure(Box::new(HirClosureExpr {
            proto: child_ref,
            captures,
        }));
        body.stmts.push(HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: vec![local],
            values: HirValuePack::fixed(vec![closure]),
        })));
    }
    if plan.root.index() >= plan.nodes.len() {
        return Err(error());
    }
    body.stmts
        .push(return_stmt(HirValuePack::fixed(vec![HirExpr::LocalRef(
            LocalId(plan.root.index()),
        )])));

    Ok(HirProto {
        id,
        source: owner.source.as_ref().map(decode_raw_string),
        line_range: owner.line_range,
        signature: crate::parser::ProtoSignature {
            num_params: 0,
            is_vararg: false,
            has_vararg_param_reg: false,
            named_vararg_table: false,
            legacy_arg_slot: false,
        },
        params: Vec::new(),
        param_debug_hints: Vec::new(),
        locals: (0..plan.nodes.len()).map(LocalId).collect(),
        local_debug_hints: vec![None; plan.nodes.len()],
        physical_root_temps: BTreeSet::new(),
        physical_root_locals: BTreeSet::new(),
        upvalues: (0..plan.outer_captures.len()).map(UpvalueId).collect(),
        upvalue_debug_hints: vec![None; plan.outer_captures.len()],
        temps: Vec::new(),
        temp_debug_locals: Vec::new(),
        temp_debug_scopes: Vec::new(),
        body,
        children,
        failure: None,
        detached_children: Vec::new(),
    })
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
        let Some(def_id) = sources.defs().iter().next().copied() else {
            continue;
        };
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
        && base == self_arg
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

    matches!(call.kind, CallKind::Normal | CallKind::FastCall(_))
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

    matches!(call.kind, CallKind::Normal | CallKind::FastCall(_))
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
    pub(super) fn shared_closure_local(&self, creation: ClosureCreation) -> Option<LocalId> {
        let ClosureCreation::Reusable(identity) = creation else {
            return None;
        };
        self.shared_closure_locals
            .get(&identity)
            .map(|(local, _)| *local)
    }

    pub(super) fn shared_closure_replacement(
        &self,
        instr: InstrRef,
    ) -> Option<CompositeFactoryRef> {
        self.captured_shared_closures.plan.replacement_at(instr)
    }

    pub(super) fn shared_closure_owner(&self, instr: InstrRef) -> Option<CompositeFactoryRef> {
        self.captured_shared_closures.plan.owner_at(instr)
    }

    pub(super) fn shared_closure_is_consumed(&self, instr: InstrRef) -> bool {
        self.captured_shared_closures.plan.is_consumed(instr)
    }

    pub(super) fn shared_factory_local(&self, factory: CompositeFactoryRef) -> LocalId {
        self.captured_shared_closures.factory_local(factory)
    }

    pub(super) fn hir_children(&self) -> Vec<HirProtoRef> {
        self.child_refs
            .iter()
            .enumerate()
            .filter_map(|(index, child)| {
                (!self
                    .captured_shared_closures
                    .plan
                    .child_is_claimed(ProtoRef(index)))
                .then_some(*child)
            })
            .chain(
                self.captured_shared_closures
                    .composite_protos
                    .iter()
                    .copied(),
            )
            .collect()
    }

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

fn build_proto_body(
    proto: HirProtoRef,
    lowering: &ProtoLowering<'_>,
) -> Result<HirBlock, HirLowerError> {
    let mut body = build_structured_body(proto, lowering)?;
    let mut prefix = if lowering.bindings.debug_entry_local_decls.is_empty() {
        Vec::new()
    } else {
        vec![HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: lowering.bindings.debug_entry_local_decls.clone(),
            values: HirValuePack::fixed(vec![
                HirExpr::Nil;
                lowering.bindings.debug_entry_local_decls.len()
            ]),
        }))]
    };
    prefix.extend(local_decl_stmts(
        lowering.bindings.capture_entry_local_decls.clone(),
    ));
    prefix.extend(
        lowering
            .shared_closure_locals
            .values()
            .map(|(local, proto)| {
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![*local],
                    values: HirValuePack::fixed(vec![HirExpr::Closure(Box::new(HirClosureExpr {
                        proto: lowering.child_refs[proto.index()],
                        captures: Vec::new(),
                    }))]),
                }))
            }),
    );
    prefix.append(&mut body.stmts);
    body.stmts = prefix;
    Ok(body)
}
