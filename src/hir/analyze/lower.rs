//! 这个文件承载 HIR 初始恢复里真正的 lowering 内核。
//!
//! 外层 [analyze.rs](/Users/x3zvawq/workspace/unluac-rs/src/hir/analyze/mod.rs) 只负责组织模块和
//! 暴露主入口，这里集中放 proto 递归构造和共享 lowering 上下文。final edge 的 phi
//! copy 由 plan 执行器消费；单条 low-IR 指令到 HIR 语句的映射由 `instrs.rs` 负责，
//! captured Luau shared closure 的词法 factory 由 `shared_closures.rs` 先冻结，再由这里
//! 预留并填充 synthetic proto；Structure 已证明的控制流需求/unresolved requirement 也在这里
//! 蒸馏为不含 CFG/SSA/VM 类型的 HIR 退出事实，目标语法是否合法仍由 AST 判断。

use std::collections::{BTreeMap, BTreeSet};

use super::super::promotion::{HomeSlotKey, ProtoPromotionFacts, SlotEpochFacts};
use super::bindings::build_bindings;
use super::global_decls::GlobalDeclProtocols;
use super::helpers::{decode_raw_string, empty_proto, raw_lua_string, return_stmt};
use super::instrs::local_decl_stmts;
use super::shared_closures::{
    CompositeCapture, CompositeFactoryPlan, CompositeFactoryRef, SharedClosurePlan,
    build_shared_closure_plan,
};
use super::structure::build_structured_body;
use crate::decompile::{DecompileContext, DecompileDialect, DecompileState};
use crate::generate::GenerateMode;
use crate::hir::HirLowerError;
use crate::hir::common::{
    HirBlock, HirCapture, HirCaptureMode, HirClosureExpr, HirControlFlowFeature, HirDebugScope,
    HirExitRequirement, HirExpr, HirLValue, HirLocalDecl, HirProto, HirProtoRef, HirStmt,
    HirValuePack, LocalId, ParamId, TempId, UpvalueId,
};
use crate::hir::emission::HirEmissionFacts;
use crate::recovery::{ProtoArtifactStage, ProtoFailure};
use crate::structure::{
    BlockRef, BlockTerminatorKind, Cfg, CfgGraph, ControlFlowFeature, DataflowFacts, GraphFacts,
    LoopSourceBindings, LoopVmProtocol, OpenDefId, PhiId, PlanRequirement, SsaValue, StructurePlan,
};
use crate::structure::{ReadyStructureFacts, StructureFacts};
use crate::transformer::{
    AccessBase, AccessKey, CallKind, CaptureSource, ClosureCreation, GetTableKind, InstrRef,
    LowInstr, LoweredProto, ProtoRef, Reg, ResultPack, SharedClosureRef, ValuePack,
};

pub(super) struct ProtoBindings {
    pub(super) params: Vec<ParamId>,
    pub(super) param_debug_hints: Vec<Option<String>>,
    pub(super) local_count: usize,
    pub(super) vararg_param_local: Option<LocalId>,
    pub(super) local_debug_hints: Vec<Option<String>>,
    pub(super) local_debug_scopes: Vec<Option<usize>>,
    pub(super) upvalues: Vec<UpvalueId>,
    pub(super) upvalue_debug_hints: Vec<Option<String>>,
    pub(super) temp_count: usize,
    pub(super) temp_debug_locals: Vec<Option<String>>,
    pub(super) temp_debug_scopes: Vec<Option<usize>>,
    pub(super) fixed_temps: Vec<TempId>,
    pub(super) phi_temps: Vec<TempId>,
    pub(super) home_free_temps: BTreeSet<TempId>,
    pub(super) loop_guard_temps: Vec<Option<TempId>>,
    pub(super) repeat_staged_temps: Vec<Vec<TempId>>,
    pub(super) bound_temp_targets: BTreeMap<TempId, BoundSlotTarget>,
    pub(super) captured_temp_targets: BTreeMap<TempId, BoundSlotTarget>,
    pub(super) temp_decl_locals: BTreeMap<TempId, LocalId>,
    pub(super) captured_local_home_slots: Vec<(LocalId, HomeSlotKey)>,
    pub(super) capture_empty_local_decls: BTreeMap<usize, Vec<LocalId>>,
    pub(super) capture_entry_local_decls: Vec<LocalId>,
    pub(super) debug_entry_local_decls: Vec<LocalId>,
    pub(super) capture_region_local_decls: BTreeMap<crate::structure::RegionId, Vec<LocalId>>,
    pub(super) closure_capture_targets: BTreeMap<(usize, usize), LocalId>,
    pub(super) lexical_scopes: Vec<std::ops::Range<usize>>,
    pub(super) entry_local_regs: BTreeMap<Reg, LocalId>,
    pub(super) numeric_for_locals: BTreeMap<BlockRef, LocalId>,
    pub(super) numeric_binding_phi_locals: Vec<Option<LocalId>>,
    pub(super) generic_for_locals: BTreeMap<BlockRef, Vec<LocalId>>,
    pub(super) block_local_regs: BTreeMap<BlockRef, BTreeMap<Reg, LocalId>>,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(super) enum BoundSlotTarget {
    Local(LocalId),
    Param(ParamId),
}

impl BoundSlotTarget {
    pub(super) fn expr(self) -> HirExpr {
        match self {
            Self::Local(local) => HirExpr::LocalRef(local),
            Self::Param(param) => HirExpr::ParamRef(param),
        }
    }

    pub(super) fn lvalue(self) -> HirLValue {
        match self {
            Self::Local(local) => HirLValue::Local(local),
            Self::Param(param) => HirLValue::Param(param),
        }
    }
}

impl ProtoBindings {
    fn temp_target(&self, temp: TempId) -> Option<BoundSlotTarget> {
        self.bound_temp_targets
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

    /// 当前 block 的寄存器值优先投影到 local owner；旧值快照仍显式使用 temp 查询。
    pub(super) fn expr_for_reg_value(
        &self,
        block: BlockRef,
        reg: Reg,
        fallback: impl FnOnce() -> HirExpr,
    ) -> HirExpr {
        self.local_for_reg_in_block(block, reg)
            .map_or_else(fallback, HirExpr::LocalRef)
    }

    /// 固定定义优先投影到当前 block 的 local owner，否则回退到 temp target。
    /// 同一个 VM 结果的读写必须使用这对投影，避免 closure 的 self capture 与接收
    /// closure 的 binding 分裂成两个身份。
    pub(super) fn expr_for_fixed_def(&self, block: BlockRef, reg: Reg, temp: TempId) -> HirExpr {
        self.expr_for_reg_value(block, reg, || self.expr_for_temp(temp))
    }

    pub(super) fn lvalue_for_reg_result(
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
            .map(BoundSlotTarget::Local)
    }
}

pub(super) struct ProtoLowering<'a> {
    pub(super) target: DecompileDialect,
    pub(super) proto: &'a LoweredProto,
    pub(super) cfg: &'a Cfg,
    pub(super) dataflow: &'a DataflowFacts,
    pub(super) structure: &'a ReadyStructureFacts,
    pub(super) promotion_facts: &'a ProtoPromotionFacts,
    pub(super) child_refs: &'a [HirProtoRef],
    pub(super) bindings: ProtoBindings,
    pub(super) self_value_capture_locals: BTreeMap<InstrRef, LocalId>,
    pub(super) shared_closure_locals: BTreeMap<SharedClosureRef, (LocalId, ProtoRef)>,
    pub(super) captured_shared_closures: CapturedSharedClosureLowering<'a>,
    pub(super) open_pack_owners: Vec<Option<InstrRef>>,
    pub(super) owned_open_producers: Vec<bool>,
    pub(super) global_decls: GlobalDeclProtocols,
    pub(super) pending_frame_returns: BTreeSet<InstrRef>,
}

fn pending_frame_returns(proto: &LoweredProto, plan: &StructurePlan) -> BTreeSet<InstrRef> {
    proto
        .instrs
        .iter()
        .enumerate()
        .filter_map(|(index, instr)| {
            let LowInstr::Close(close) = instr else {
                return None;
            };
            let source = match close.kind {
                crate::transformer::CloseKind::Return(source)
                | crate::transformer::CloseKind::TailCall(source) => source,
                crate::transformer::CloseKind::Explicit => return None,
            };
            let instr = InstrRef(index);
            // 只有最终计划仍在原位置发射的 frame cleanup 需要 HIR 配对。词法 scope、
            // loop boundary/tail 已消费它们；IncomingEdges 只搬运 Explicit 协议。
            (plan.cleanup_disposition(instr)
                == Some(crate::structure::CleanupDisposition::ExplicitClose)
                && plan.loop_exit_tail_for_cleanup_instr(instr).is_none())
            .then_some(source)
        })
        .collect()
}

pub(super) struct CapturedSharedClosureLowering<'a> {
    plan: SharedClosurePlan,
    factory_locals: Vec<LocalId>,
    capture_barriers: Vec<Option<SharedCaptureBarrier>>,
    // frame 保留列表供失败回滚；lowering 只借用已预留的身份。
    composite_protos: &'a [HirProtoRef],
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
    target: DecompileDialect,
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
        context.requested_target.version,
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
    target: DecompileDialect,
    node: ProtoNodeFacts<'_>,
    artifacts: &mut LowerArtifacts,
    recover_failures: bool,
) -> Result<LoweredProtoResult, HirLowerError> {
    fn make_frame<'a>(
        target: DecompileDialect,
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
    let composite_protos = &frame.composite_protos;
    let child_results = &frame.child_results;
    let cfg = &cfg_graph.cfg;
    let child_refs = child_results
        .iter()
        .map(|child| child.id)
        .collect::<Vec<_>>();
    let child_mutable_upvalues = child_results
        .iter()
        .map(|child| child.mutable_upvalues.as_slice())
        .collect::<Vec<_>>();
    fill_composite_factory_protos(
        proto,
        &child_refs,
        &child_mutable_upvalues,
        &captured_shared_plan,
        composite_protos,
        artifacts,
    )?;

    let slot_epochs = SlotEpochFacts::analyze(proto, cfg, graph_facts, dataflow);
    let emission = HirEmissionFacts::new(structure.plan());
    let mut bindings = build_bindings(
        proto,
        cfg,
        graph_facts,
        dataflow,
        structure,
        &emission,
        &slot_epochs,
        &child_mutable_upvalues,
    );
    let self_value_capture_locals = build_self_value_capture_locals(proto, &mut bindings);
    let shared_closure_locals =
        build_shared_closure_locals(proto, &captured_shared_plan, &mut bindings);
    let captured_shared_closures = CapturedSharedClosureLowering::new(
        captured_shared_plan,
        composite_protos,
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
    let global_decls = GlobalDeclProtocols::analyze(proto, cfg, dataflow);
    let mut promotion_facts = ProtoPromotionFacts::from_plan(
        proto,
        cfg,
        graph_facts,
        dataflow,
        structure.plan(),
        &slot_epochs,
        &bindings.fixed_temps,
        &bindings.phi_temps,
    );
    promotion_facts.record_copy_root_retirements(
        proto,
        cfg,
        dataflow,
        &bindings.fixed_temps,
        &bindings.temp_debug_scopes,
        &emission,
    );
    super::bindings::bind_copy_root_scopes(
        proto,
        cfg,
        dataflow,
        graph_facts,
        structure,
        &emission,
        &mut bindings,
        &mut promotion_facts,
    )?;
    drop(emission);
    let copy_root_holders =
        super::bindings::bind_copy_root_holders(&mut bindings, &mut promotion_facts);
    super::method_setups::record_method_setup_protocols(
        proto,
        dataflow,
        &bindings,
        &mut promotion_facts,
    );
    for &temp in &bindings.home_free_temps {
        promotion_facts.record_home_free_temp(temp);
    }
    // `entry_local_regs` 是 Entry(reg) 的可见 binding；它与 SSA entry leaf 一样属于
    // `(reg, epoch 0)`。把这份已知身份带入 lowering/simplify，避免异槽 reference capture
    // 被误判为可能观察任意 local 写入。后续异槽合并仍会通过 invalidation 使其失效。
    for (&reg, &local) in &bindings.entry_local_regs {
        promotion_facts.record_local_home_slot(local, HomeSlotKey::new(reg.index(), 0));
    }
    for &(local, home) in &bindings.captured_local_home_slots {
        promotion_facts.record_local_home_slot(local, home);
    }
    record_loop_binding_local_homes(
        structure.plan(),
        &slot_epochs,
        &bindings,
        &mut promotion_facts,
    );
    let mut lowering = ProtoLowering {
        target,
        proto,
        cfg,
        dataflow,
        structure,
        promotion_facts: &promotion_facts,
        child_refs: &child_refs,
        bindings,
        self_value_capture_locals,
        shared_closure_locals,
        captured_shared_closures,
        open_pack_owners,
        owned_open_producers,
        global_decls,
        pending_frame_returns: pending_frame_returns(proto, structure.plan()),
    };
    let mutable_upvalues = mutable_upvalues_for_proto(proto, &child_mutable_upvalues);

    let environment_upvalues = proto
        .environment_upvalues
        .iter()
        .map(|upvalue| lowering.bindings.upvalues[upvalue.index()])
        .collect();
    let mut body = build_proto_body(id, &mut lowering)?;
    let copy_roots = promotion_facts
        .copy_root_temps()
        .iter()
        .copied()
        .filter(|temp| matches!(lowering.bindings.lvalue_for_temp(*temp), HirLValue::Temp(_)))
        .collect::<Vec<_>>();
    if !copy_roots.is_empty() {
        body.stmts.insert(
            0,
            super::helpers::assign_stmt(
                copy_roots.iter().copied().map(HirLValue::Temp).collect(),
                vec![HirExpr::Nil; copy_roots.len()],
            ),
        );
    }
    if !copy_root_holders.is_empty() {
        body.stmts.insert(
            0,
            HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: copy_root_holders.clone(),
                values: vec![HirExpr::Nil; copy_root_holders.len()].into(),
                initializer_merge_transaction: None,
            })),
        );
    }
    let children = lowering.hir_children();
    let bindings = lowering.bindings;

    let physical_root_locals = promotion_facts
        .copy_scoped_temps()
        .iter()
        .map(|temp| bindings.temp_decl_locals[temp])
        .chain(copy_root_holders)
        .collect();
    artifacts.protos[id.index()] = HirProto {
        id,
        source: proto.source.as_ref().map(raw_lua_string),
        line_range: proto.line_range,
        signature: proto.signature,
        params: bindings.params,
        param_debug_hints: bindings.param_debug_hints,
        local_count: bindings.local_count,
        vararg_param_local: bindings.vararg_param_local,
        local_debug_hints: bindings.local_debug_hints,
        local_debug_scopes: bindings.local_debug_scopes,
        debug_scopes: accepted_debug_scopes(proto, structure),
        physical_root_temps: promotion_facts.protect_copy_root_temps(),
        physical_root_locals,
        inline_dispositions: Default::default(),
        upvalues: bindings.upvalues,
        environment_upvalues,
        mutable_upvalues: mutable_upvalue_ids(&mutable_upvalues),
        upvalue_debug_hints: bindings.upvalue_debug_hints,
        temp_count: bindings.temp_count,
        temp_debug_locals: bindings.temp_debug_locals,
        temp_debug_scopes: bindings.temp_debug_scopes,
        exit_requirements: collect_exit_requirements(frame.source_proto_id, structure),
        body,
        children,
        failure: None,
        detached_children: Vec::new(),
    };
    artifacts.promotion_facts[id.index()] = promotion_facts;

    Ok(LoweredProtoResult {
        id,
        source_proto_id: frame.source_proto_id,
        mutable_upvalues,
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
                    let local = LocalId(bindings.local_count);
                    bindings.local_count += 1;
                    bindings.local_debug_hints.push(None);
                    bindings.local_debug_scopes.push(None);
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
    let vararg_param_locals = usize::from(proto.signature.has_vararg_param_reg);
    let detached_children = frame
        .child_results
        .iter()
        .enumerate()
        .map(|(index, child)| (LocalId(vararg_param_locals + index), child.id))
        .collect::<Vec<_>>();
    let local_count = vararg_param_locals + detached_children.len();
    let mut local_debug_hints = vec![None; vararg_param_locals];
    local_debug_hints.extend(
        frame
            .child_results
            .iter()
            .map(|child| Some(format!("unluac_proto_{}", child.source_proto_id))),
    );
    let child_mutable_upvalues = frame
        .child_results
        .iter()
        .map(|child| child.mutable_upvalues.as_slice())
        .collect::<Vec<_>>();
    let mutable_upvalues = mutable_upvalues_for_proto(proto, &child_mutable_upvalues);

    artifacts.protos[id.index()] = HirProto {
        id,
        source: proto.source.as_ref().map(raw_lua_string),
        line_range: proto.line_range,
        signature: proto.signature,
        params: (0..usize::from(proto.signature.num_params))
            .map(ParamId)
            .collect(),
        param_debug_hints: vec![None; usize::from(proto.signature.num_params)],
        local_count,
        vararg_param_local: proto.signature.has_vararg_param_reg.then_some(LocalId(0)),
        local_debug_hints,
        local_debug_scopes: vec![None; vararg_param_locals + detached_children.len()],
        debug_scopes: Vec::new(),
        physical_root_temps: BTreeSet::new(),
        physical_root_locals: BTreeSet::new(),
        inline_dispositions: Default::default(),
        upvalues: (0..usize::from(proto.upvalue_count))
            .map(UpvalueId)
            .collect(),
        environment_upvalues: proto
            .environment_upvalues
            .iter()
            .map(|upvalue| UpvalueId(upvalue.index()))
            .collect(),
        mutable_upvalues: mutable_upvalue_ids(&mutable_upvalues),
        upvalue_debug_hints: (0..usize::from(proto.upvalue_count))
            .map(|index| {
                proto
                    .upvalue_debug_names
                    .get(index)
                    .and_then(|name| name.as_ref().map(decode_raw_string))
            })
            .collect(),
        temp_count: 0,
        temp_debug_locals: Vec::new(),
        temp_debug_scopes: Vec::new(),
        exit_requirements: frame.structure.ready().map_or_else(Vec::new, |structure| {
            collect_exit_requirements(frame.source_proto_id, structure)
        }),
        body: HirBlock::default(),
        children: frame.child_results.iter().map(|child| child.id).collect(),
        failure: Some(failure),
        detached_children,
    };

    LoweredProtoResult {
        id,
        source_proto_id: frame.source_proto_id,
        mutable_upvalues,
    }
}

fn accepted_debug_scopes(
    proto: &LoweredProto,
    structure: &ReadyStructureFacts,
) -> Vec<Option<HirDebugScope>> {
    let mut scopes = vec![None; proto.debug_locals.len()];
    for fact in structure.debug_bindings().accepted() {
        scopes[fact.scope] = Some(HirDebugScope {
            start_pc: fact.start_pc,
            end_pc: fact.end_pc,
            ends_before_return: fact
                .end_instr
                .is_some_and(|instr| debug_scope_end_precedes_return(proto, instr)),
        });
    }
    scopes
}

fn collect_exit_requirements(
    source_proto: usize,
    structure: &ReadyStructureFacts,
) -> Vec<HirExitRequirement> {
    let requirements = structure.plan().requirements();
    let mut exit_requirements = requirements
        .required_features()
        .iter()
        .copied()
        .map(|feature| HirExitRequirement::RequiredControlFlow {
            source_proto,
            feature: match feature {
                ControlFlowFeature::GotoLabel => HirControlFlowFeature::GotoLabel,
                ControlFlowFeature::ContinueStatement => HirControlFlowFeature::ContinueStatement,
            },
        })
        .collect::<Vec<_>>();
    exit_requirements.extend(requirements.iter().filter_map(|(_, requirement)| {
        let PlanRequirement::UnresolvedValue { phi_id, block, reg } = requirement else {
            return None;
        };
        Some(HirExitRequirement::UnresolvedValue {
            source_proto,
            phi: phi_id.index(),
            block: block.index(),
            register: reg.index(),
        })
    }));
    exit_requirements
}

fn debug_scope_end_precedes_return(proto: &LoweredProto, instr: InstrRef) -> bool {
    let tail = &proto.instrs[instr.index()..];
    let close_count = tail
        .iter()
        .take_while(|instr| matches!(instr, LowInstr::Close(_)))
        .count();
    matches!(tail.get(close_count), Some(LowInstr::Return(_))) && close_count + 1 == tail.len()
}

fn mutable_upvalues_for_proto(
    proto: &LoweredProto,
    child_mutable_upvalues: &[&[bool]],
) -> Vec<bool> {
    let mut mutable = vec![false; usize::from(proto.upvalue_count)];
    for instr in &proto.instrs {
        match instr {
            LowInstr::SetUpvalue(set) => {
                let dst = match set.dst {
                    crate::transformer::UpvalueOperand::Env(dst)
                    | crate::transformer::UpvalueOperand::Upvalue(dst) => dst,
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

fn mutable_upvalue_ids(mutable: &[bool]) -> BTreeSet<UpvalueId> {
    mutable
        .iter()
        .copied()
        .enumerate()
        .filter_map(|(index, can_write)| can_write.then_some(UpvalueId(index)))
        .collect()
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
            let local = LocalId(bindings.local_count);
            bindings.local_count += 1;
            bindings.local_debug_hints.push(None);
            bindings.local_debug_scopes.push(None);
            (identity, (local, proto))
        })
        .collect()
}

impl<'a> CapturedSharedClosureLowering<'a> {
    fn new(
        plan: SharedClosurePlan,
        composite_protos: &'a [HirProtoRef],
        proto: &LoweredProto,
        dataflow: &DataflowFacts,
        bindings: &mut ProtoBindings,
    ) -> Self {
        let mut factory_locals = Vec::with_capacity(plan.composites().len());
        let mut capture_barriers = Vec::with_capacity(plan.composites().len());
        for composite in plan.composites() {
            let instr = composite.anchor;
            let index = instr.index();
            let local = LocalId(bindings.local_count);
            bindings.local_count += 1;
            bindings.local_debug_hints.push(None);
            bindings.local_debug_scopes.push(None);
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
                    || !capture_needs_non_reflexive_barrier(proto, dataflow, instr, source)
                {
                    continue;
                }
                let local = LocalId(bindings.local_count);
                bindings.local_count += 1;
                bindings.local_debug_hints.push(None);
                bindings.local_debug_scopes.push(None);
                *snapshot = Some(local);
            }
            let barrier = snapshots.iter().any(Option::is_some).then(|| {
                let box_local = LocalId(bindings.local_count);
                bindings.local_count += 1;
                bindings.local_debug_hints.push(None);
                bindings.local_debug_scopes.push(None);
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
) -> bool {
    let CaptureSource::ByValue(reg) = source else {
        return false;
    };
    let Some(SsaValue::Def(def)) = dataflow.canonical_move_value(dataflow.use_value(instr, reg))
    else {
        return false;
    };
    let def_instr = dataflow.def_instr(def);
    match proto.instrs.get(def_instr.index()) {
        Some(LowInstr::LoadNumber(load)) => load.value.is_nan(),
        Some(LowInstr::LoadConst(load)) => match proto.constants.get(load.value.index()) {
            Some(crate::parser::RawLiteralConst::Number(value)) => value.is_nan(),
            Some(crate::parser::RawLiteralConst::Vector(value)) => value
                .components
                .iter()
                .any(|bits| f32::from_bits(*bits).is_nan()),
            Some(crate::parser::RawLiteralConst::Complex { real, imag }) => {
                real.is_nan() || imag.is_nan()
            }
            _ => false,
        },
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
    child_mutable_upvalues: &[&[bool]],
    plan: &SharedClosurePlan,
    ids: &[HirProtoRef],
    artifacts: &mut LowerArtifacts,
) -> Result<(), HirLowerError> {
    for (composite, id) in plan.composites().iter().zip(ids) {
        let (factory_proto, promotion_facts) = build_composite_factory_proto(
            *id,
            proto,
            child_refs,
            child_mutable_upvalues,
            composite,
        )?;
        artifacts.protos[id.index()] = factory_proto;
        artifacts.promotion_facts[id.index()] = promotion_facts;
    }
    Ok(())
}

fn build_composite_factory_proto(
    id: HirProtoRef,
    proto: &LoweredProto,
    child_refs: &[HirProtoRef],
    child_mutable_upvalues: &[&[bool]],
    plan: &CompositeFactoryPlan,
) -> Result<(HirProto, ProtoPromotionFacts), HirLowerError> {
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
    let mut mutable_upvalues = BTreeSet::new();

    for (index, node) in plan.nodes.iter().enumerate() {
        let child = proto.children.get(node.proto.index()).ok_or_else(error)?;
        if usize::from(child.upvalue_count) != node.captures.len() {
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
            .enumerate()
            .map(|(capture_index, capture)| {
                let (mode, binding) = match *capture {
                    CompositeCapture::Outer(outer) => {
                        if outer >= plan.outer_captures.len() {
                            return None;
                        }
                        if child_mutable_upvalues
                            .get(node.proto.index())
                            .and_then(|mutable| mutable.get(capture_index))
                            .copied()
                            .unwrap_or(false)
                        {
                            mutable_upvalues.insert(UpvalueId(outer));
                        }
                        (
                            HirCaptureMode::ByReference,
                            crate::hir::HirBinding::Upvalue(UpvalueId(outer)),
                        )
                    }
                    CompositeCapture::Dependency(dependency) => {
                        if dependency.index() >= index {
                            return None;
                        }
                        (
                            HirCaptureMode::ByValue,
                            crate::hir::HirBinding::Local(LocalId(dependency.index())),
                        )
                    }
                };
                Some(HirCapture { mode, binding })
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
            initializer_merge_transaction: None,
        })));
    }
    if plan.root.index() >= plan.nodes.len() {
        return Err(error());
    }
    body.stmts.push(return_stmt(
        HirValuePack::fixed(vec![HirExpr::LocalRef(LocalId(plan.root.index()))]),
        None,
    ));
    let local_count = plan.nodes.len();
    let mut promotion_facts = ProtoPromotionFacts::default();
    for local in (0..local_count).map(LocalId) {
        promotion_facts.record_home_free_local(local);
    }

    let proto = HirProto {
        id,
        source: owner.source.as_ref().map(raw_lua_string),
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
        local_count,
        vararg_param_local: None,
        local_debug_hints: vec![None; plan.nodes.len()],
        local_debug_scopes: vec![None; plan.nodes.len()],
        debug_scopes: Vec::new(),
        physical_root_temps: BTreeSet::new(),
        physical_root_locals: BTreeSet::new(),
        inline_dispositions: Default::default(),
        upvalues: (0..plan.outer_captures.len()).map(UpvalueId).collect(),
        environment_upvalues: plan
            .outer_captures
            .iter()
            .enumerate()
            .filter_map(|(index, source)| match source {
                CaptureSource::Upvalue(upvalue) if proto.environment_upvalues.contains(upvalue) => {
                    Some(UpvalueId(index))
                }
                _ => None,
            })
            .collect(),
        mutable_upvalues,
        upvalue_debug_hints: vec![None; plan.outer_captures.len()],
        temp_count: 0,
        temp_debug_locals: Vec::new(),
        temp_debug_scopes: Vec::new(),
        exit_requirements: Vec::new(),
        body,
        children,
        failure: None,
        detached_children: Vec::new(),
    };
    Ok((proto, promotion_facts))
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
        && matches!(
            first.base,
            AccessBase::Env | AccessBase::EnvironmentUpvalue(_)
        )
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
    /// 消费 canonical SSA 身份的寄存器归属，不按 temp 编号或物理 home 反推。
    pub(super) fn ssa_reg(&self, value: SsaValue) -> Option<Reg> {
        match value {
            SsaValue::Entry(reg) => Some(reg),
            SsaValue::Def(def) => self.dataflow.defs.get(def.index()).map(|def| def.reg),
            SsaValue::Phi(phi) => self.structure.plan().phi_plan(phi).map(|phi| phi.reg),
        }
    }

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
    lowering: &mut ProtoLowering<'_>,
) -> Result<HirBlock, HirLowerError> {
    let mut body = build_structured_body(proto, lowering)?;
    let debug_entry_bindings = std::mem::take(&mut lowering.bindings.debug_entry_local_decls);
    let mut prefix = if debug_entry_bindings.is_empty() {
        Vec::new()
    } else {
        vec![HirStmt::LocalDecl(Box::new(HirLocalDecl {
            values: HirValuePack::fixed(vec![HirExpr::Nil; debug_entry_bindings.len()]),
            bindings: debug_entry_bindings,
            initializer_merge_transaction: None,
        }))]
    };
    prefix.extend(local_decl_stmts(std::mem::take(
        &mut lowering.bindings.capture_entry_local_decls,
    )));
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
                    initializer_merge_transaction: None,
                }))
            }),
    );
    prefix.append(&mut body.stmts);
    body.stmts = prefix;
    Ok(body)
}
