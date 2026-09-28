//! HIR 初始恢复的 proto 构造与共享 lowering 上下文。
//!
//! 消费冻结的 StructurePlan、绑定和闭包事实，构造 HIR artifact 与退出要求；
//! 指令和结构发射由对应子模块执行。

use std::collections::{BTreeMap, BTreeSet};

use super::super::promotion::{HomeSlotKey, ProtoPromotionFacts, SlotEpochFacts};
use super::bindings::build_bindings;
use super::global_decls::GlobalDeclProtocols;
use super::helpers::{decode_raw_string, empty_proto, raw_lua_string, return_stmt};
use super::instrs::local_decl_stmts;
use super::shared_closures::{
    CompositeCapture, CompositeFactoryPlan, CompositeFactoryRef, SharedClosurePlan,
    SharedFactoryEffectKind, build_shared_closure_plan,
};
use super::structure::build_structured_body;
use crate::decompile::{DecompileContext, DecompileDialect, DecompileState};
use crate::generate::GenerateMode;
use crate::hir::HirLowerError;
use crate::hir::common::{
    HirBlock, HirCapture, HirCaptureMode, HirClosureExpr, HirControlFlowFeature,
    HirDebugBranchInitializer, HirDebugScope, HirExitRequirement, HirExpr, HirLValue, HirLocalDecl,
    HirProto, HirProtoRef, HirStmt, HirValuePack, LocalId, ParamId, TempId, UpvalueId,
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

/// 已证明的 low 词法窗口；首条 LOADNIL 或 VM Entry nil 可同时初始化窗口外的低槽声明。
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct LexicalScope {
    pub(super) start: usize,
    pub(super) end: usize,
    /// 小于该槽的初始 nil 声明在 Start 边界之前发射，其余成员在窗口内。
    pub(super) initial_nil_floor: Option<Reg>,
}

impl From<std::ops::Range<usize>> for LexicalScope {
    fn from(range: std::ops::Range<usize>) -> Self {
        Self {
            start: range.start,
            end: range.end,
            initial_nil_floor: None,
        }
    }
}

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
    pub(super) declared_local_home_slots: Vec<(LocalId, HomeSlotKey)>,
    pub(super) capture_empty_local_decls: BTreeMap<usize, Vec<LocalId>>,
    pub(super) capture_entry_local_decls: Vec<LocalId>,
    pub(super) entry_nil_local_decls: Vec<LocalId>,
    pub(super) capture_region_local_decls: BTreeMap<crate::structure::RegionId, Vec<LocalId>>,
    pub(super) closure_capture_targets: BTreeMap<(usize, usize), LocalId>,
    pub(super) closed_capture_temps: BTreeSet<TempId>,
    pub(super) lexical_scopes: Vec<LexicalScope>,
    pub(super) entry_local_regs: BTreeMap<Reg, LocalId>,
    pub(super) numeric_for_locals: BTreeMap<BlockRef, LocalId>,
    pub(super) numeric_binding_copies: BTreeSet<InstrRef>,
    pub(super) for_binding_phi_locals: Vec<Option<LocalId>>,
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
        self.for_binding_phi_locals
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
    pub(super) id: HirProtoRef,
    pub(super) target: DecompileDialect,
    pub(super) proto: &'a LoweredProto,
    pub(super) cfg: &'a Cfg,
    pub(super) dataflow: &'a DataflowFacts,
    pub(super) structure: &'a ReadyStructureFacts,
    pub(super) promotion_facts: &'a ProtoPromotionFacts,
    pub(super) emission: &'a HirEmissionFacts<'a>,
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
    /// 原 scalar NaN 定义的相邻初始化事务；后续同 Def 的 factory 复用其不透明快照。
    literal_initializers: BTreeMap<InstrRef, TempId>,
    pub(super) identity_initializers: BTreeMap<InstrRef, IdentityCaptureInitializer>,
    // frame 保留列表供失败回滚；lowering 只借用已预留的身份。
    composite_protos: &'a [HirProtoRef],
}

#[derive(Clone, Copy)]
pub(super) struct IdentityCaptureInitializer {
    pub(super) callee: LocalId,
    child: ProtoRef,
    temp: TempId,
}

pub(super) struct SharedCaptureBarrier {
    pub(super) box_local: Option<LocalId>,
    pub(super) snapshots: Vec<Option<LocalId>>,
}

#[derive(Default)]
pub(super) struct LowerArtifacts {
    pub(super) protos: Vec<HirProto>,
    pub(super) promotion_facts: Vec<ProtoPromotionFacts>,
    pub(super) required_luau_inlining: Vec<crate::hir::common::HirRequiredLuauInlining>,
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
        lowered.header.version,
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
    source: DecompileDialect,
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
            match lower_proto_one(&mut frame, artifacts, source) {
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
    source: DecompileDialect,
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

    let slot_epochs = SlotEpochFacts::analyze(proto, cfg, graph_facts, dataflow);
    let emission = HirEmissionFacts::new(structure.plan(), cfg, target);
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
    let self_value_capture_locals =
        build_self_value_capture_locals(proto, cfg, dataflow, &slot_epochs, &mut bindings);
    let shared_closure_locals =
        build_shared_closure_locals(proto, &captured_shared_plan, &mut bindings);
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
        source,
        id,
        cfg,
        graph_facts,
        dataflow,
        structure.plan(),
        structure.debug_bindings(),
        &slot_epochs,
        &bindings.fixed_temps,
        &bindings.phi_temps,
    );
    super::bindings::bind_parameter_slots(&mut bindings, &promotion_facts, dataflow, &emission);
    let lexical_environment_local =
        global_decls.bind_environment(&mut bindings, &mut promotion_facts)?;
    let captured_shared_closures = CapturedSharedClosureLowering::new(
        captured_shared_plan,
        composite_protos,
        proto,
        cfg,
        dataflow,
        &promotion_facts,
        &mut bindings,
        id.index() == 0
            && target == DecompileDialect::Luau
            && identity_control_scope(proto, dataflow, structure.plan()),
    );
    fill_composite_factory_protos(
        proto,
        &child_refs,
        &child_mutable_upvalues,
        &captured_shared_closures.plan,
        composite_protos,
        artifacts,
    )?;
    promotion_facts.record_copy_root_retirements(
        proto,
        cfg,
        graph_facts,
        dataflow,
        &bindings.fixed_temps,
        &bindings.temp_debug_scopes,
        &emission,
        target,
    );
    let initialized_copy_root_locals = super::bindings::bind_copy_root_initializers(
        proto,
        cfg,
        graph_facts,
        dataflow,
        &emission,
        &mut bindings,
        &mut promotion_facts,
    );
    super::bindings::bind_allocation_copy_scopes(
        proto,
        cfg,
        dataflow,
        &emission,
        &mut bindings,
        &mut promotion_facts,
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
    // 原副本根先发布完整身份，后续帧候选才能按现有绑定拒绝冲突，不能反向覆盖声明的读取目标。
    let copy_root_holders =
        super::bindings::bind_copy_root_holders(&mut bindings, &mut promotion_facts);
    let reused_frame_locals = super::bindings::bind_reused_frames(
        proto,
        cfg,
        dataflow,
        structure,
        &emission,
        &mut bindings,
        &mut promotion_facts,
    );
    let discarded_call_locals = super::bindings::bind_discarded_call_results(
        proto,
        cfg,
        dataflow,
        &emission,
        &mut bindings,
        &mut promotion_facts,
    );
    super::bindings::bind_scalar_slots(
        proto,
        cfg,
        graph_facts,
        dataflow,
        &emission,
        &mut bindings,
        &mut promotion_facts,
    );
    super::method_setups::record_method_setup_protocols(
        proto,
        dataflow,
        &bindings,
        &mut promotion_facts,
    );
    for &temp in &bindings.home_free_temps {
        promotion_facts.record_home_free_temp(temp);
    }
    promotion_facts.record_closed_capture_temps(&bindings.closed_capture_temps);
    // `entry_local_regs` 是 Entry(reg) 的可见 binding；它与 SSA entry leaf 一样属于
    // `(reg, epoch 0)`。把这份已知身份带入 lowering/simplify，避免异槽 reference capture
    // 被误判为可能观察任意 local 写入。后续异槽合并仍会通过 invalidation 使其失效。
    for (&reg, &local) in &bindings.entry_local_regs {
        promotion_facts.record_local_home_slot(local, HomeSlotKey::new(reg.index(), 0));
    }
    // Lua 5.5 的隐式 vararg 参数占用固定参数之后的源码槽，即使没有 Entry 读取也存在。
    if let Some(local) = bindings.vararg_param_local {
        promotion_facts.record_local_home_slot(
            local,
            HomeSlotKey::new(usize::from(proto.signature.num_params), 0),
        );
    }
    for &(local, home) in &bindings.declared_local_home_slots {
        promotion_facts.record_local_home_slot(local, home);
    }
    // 原声明和 simplify 后的提升都拥有真实 Temp→Local 身份；只记录 home 会使
    // 完整原写组无法识别已在 lowering 物化的成员，debug nil 因而丢失其帧末端。
    for (&temp, &local) in &bindings.temp_decl_locals {
        promotion_facts.record_temp_to_local_merge(temp, local);
    }
    // debug 与 capture cell 内的后续写已直接降低成同一个 Local；完整赋值帧
    // 仍需要每个原 SSA Def 的身份。与 temp_target 相同，显式绑定覆盖 capture 默认值。
    for (&temp, &target) in bindings
        .captured_temp_targets
        .iter()
        .chain(&bindings.bound_temp_targets)
    {
        if let BoundSlotTarget::Local(local) = target {
            promotion_facts.record_temp_local_binding(temp, local);
        }
    }
    record_loop_binding_local_homes(
        structure.plan(),
        &slot_epochs,
        &bindings,
        &mut promotion_facts,
    );
    promotion_facts.record_binary_local_inputs(proto.instrs.iter().enumerate().filter_map(
        |(index, instr)| {
            let LowInstr::Branch(branch) = instr else {
                return None;
            };
            let crate::transformer::BranchSubject::Compare { lhs, rhs, .. } = branch.cond.subject
            else {
                return None;
            };
            let block = cfg.instr_to_block[index];
            let inputs = [lhs, rhs].map(|operand| match operand {
                crate::transformer::CondOperand::Reg(reg) => {
                    bindings.local_for_reg_in_block(block, reg)
                }
                _ => None,
            });
            inputs
                .iter()
                .any(Option::is_some)
                .then_some((InstrRef(index), inputs))
        },
    ));
    promotion_facts.record_table_write_local_inputs(proto.instrs.iter().enumerate().filter_map(
        |(index, instr)| {
            let LowInstr::SetTable(set) = instr else {
                return None;
            };
            let block = cfg.instr_to_block[index];
            let inputs = [
                match set.base {
                    crate::transformer::AccessBase::Reg(reg) => {
                        bindings.local_for_reg_in_block(block, reg)
                    }
                    _ => None,
                },
                match set.key {
                    crate::transformer::AccessKey::Reg(reg) => {
                        bindings.local_for_reg_in_block(block, reg)
                    }
                    _ => None,
                },
            ];
            inputs
                .iter()
                .any(Option::is_some)
                .then_some((InstrRef(index), inputs))
        },
    ));
    captured_shared_closures.record_anchor_homes(
        proto,
        dataflow,
        &slot_epochs,
        &bindings,
        &mut promotion_facts,
    );
    let mut lowering = ProtoLowering {
        id,
        target,
        proto,
        cfg,
        dataflow,
        structure,
        promotion_facts: &promotion_facts,
        emission: &emission,
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
    let mut inline_dispositions = crate::hir::common::HirInlineDispositions::default();
    if let Some(local) = lexical_environment_local {
        inline_dispositions.preserve_local(
            local,
            crate::hir::common::HirInlineRetentionReason::LexicalEnvironment,
        );
    }
    for local in reused_frame_locals
        .into_iter()
        .chain(discarded_call_locals.iter().copied())
    {
        inline_dispositions.preserve_local(
            local,
            crate::hir::common::HirInlineRetentionReason::PhysicalFramePrefix,
        );
    }
    if let Some((_, initializer)) = lowering
        .captured_shared_closures
        .identity_initializers
        .first_key_value()
    {
        inline_dispositions.preserve_local(
            initializer.callee,
            crate::hir::common::HirInlineRetentionReason::PhysicalFramePrefix,
        );
        let occurrences = lowering
            .captured_shared_closures
            .identity_initializers
            .iter()
            .map(|(&instr, initializer)| {
                if !matches!(proto.instrs[instr.index()], LowInstr::LoadBool(_)) {
                    inline_dispositions.preserve_temp(
                        initializer.temp,
                        crate::hir::common::HirInlineRetentionReason::SharedClosureIdentity,
                    );
                }
                crate::hir::common::HirSourceSite { proto: id, instr }
            })
            .collect();
        artifacts
            .required_luau_inlining
            .push(crate::hir::common::HirRequiredLuauInlining {
                owner: id,
                callee: initializer.callee,
                child: child_refs[initializer.child.index()],
                field: "".into(),
                body: crate::hir::common::HirLuauInliningBody::Identity,
                capture: None,
                occurrences,
                result_frame_slots: BTreeMap::new(),
            });
    }
    for (index, composite) in lowering
        .captured_shared_closures
        .plan
        .composites()
        .iter()
        .enumerate()
    {
        if let Some(event) = &composite.effect {
            artifacts
                .required_luau_inlining
                .push(crate::hir::common::HirRequiredLuauInlining {
                    owner: id,
                    callee: lowering.shared_factory_local(CompositeFactoryRef(index)),
                    child: composite_protos[index],
                    field: event.field.clone(),
                    body: match event.kind {
                        SharedFactoryEffectKind::Print => {
                            crate::hir::common::HirLuauInliningBody::EventClosureFactory {
                                intermediate: proto.children[composite.nodes[0].proto.index()]
                                    .origin
                                    .span
                                    .offset,
                                result: proto.children[composite.nodes[1].proto.index()]
                                    .origin
                                    .span
                                    .offset,
                            }
                        }
                        SharedFactoryEffectKind::Publish => {
                            crate::hir::common::HirLuauInliningBody::PublishedClosureFactory {
                                intermediate: proto.children[composite.nodes[0].proto.index()]
                                    .origin
                                    .span
                                    .offset,
                                leaf: proto.children[composite.nodes[0].proto.index()].children[0]
                                    .origin
                                    .span
                                    .offset,
                                result: proto.children[composite.nodes[1].proto.index()]
                                    .origin
                                    .span
                                    .offset,
                            }
                        }
                    },
                    capture: None,
                    result_frame_slots: event
                        .calls
                        .keys()
                        .map(|&instr| {
                            let LowInstr::Closure(closure) = &proto.instrs[instr.index()] else {
                                unreachable!()
                            };
                            (
                                crate::hir::common::HirSourceSite { proto: id, instr },
                                closure.dst.index(),
                            )
                        })
                        .collect(),
                    occurrences: event
                        .calls
                        .keys()
                        .map(|&instr| crate::hir::common::HirSourceSite { proto: id, instr })
                        .collect(),
                });
        }
    }
    for &temp in lowering
        .captured_shared_closures
        .literal_initializers
        .values()
    {
        inline_dispositions.preserve_temp(
            temp,
            crate::hir::common::HirInlineRetentionReason::SharedClosureIdentity,
        );
    }
    if lowering
        .captured_shared_closures
        .plan
        .composites()
        .is_empty()
    {
        super::capture_initializers::preserve(&lowering, &mut body, &mut inline_dispositions);
    }
    let bindings = lowering.bindings;

    let physical_root_locals = promotion_facts
        .copy_scoped_temps()
        .iter()
        .map(|temp| bindings.temp_decl_locals[temp])
        .chain(copy_root_holders)
        .chain(initialized_copy_root_locals)
        .chain(discarded_call_locals)
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
        debug_scopes: accepted_debug_scopes(
            id,
            proto,
            cfg,
            dataflow,
            structure,
            &bindings.fixed_temps,
            &bindings.phi_temps,
        ),
        physical_root_temps: promotion_facts
            .protect_copy_root_temps()
            .into_iter()
            .chain(promotion_facts.return_copy_roots())
            .chain(promotion_facts.entry_parameter_copy_roots())
            .collect(),
        physical_root_locals,
        inline_dispositions,
        upvalues: bindings.upvalues,
        environment_upvalues,
        lexical_environment_local,
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
                let (site, reg) = protocol
                    .writable_binding
                    .unwrap_or((protocol.init_instr, reg));
                facts.record_local_home_slot(
                    local,
                    HomeSlotKey::new(reg.index(), slot_epochs.epoch_at(reg, site)),
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
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    slot_epochs: &SlotEpochFacts,
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
                    let site = InstrRef(index);
                    let def = dataflow.instr_def_for_reg(site, closure.dst)
                        .expect("closure has a fixed result definition");
                    let temp = bindings.fixed_temps[def.index()];
                    let owns_result = temp == crate::hir::common::TempId(def.index())
                        && bindings.temp_target(temp).is_none()
                        && bindings.local_for_reg_in_block(cfg.instr_to_block[index], closure.dst).is_none();
                    let local = LocalId(bindings.local_count);
                    bindings.local_count += 1;
                    bindings.local_debug_hints.push(owns_result.then(|| bindings.temp_debug_locals[temp.index()].clone()).flatten());
                    bindings.local_debug_scopes.push(owns_result.then_some(bindings.temp_debug_scopes[temp.index()]).flatten());
                    if owns_result {
                        // 新结果 Def 本身可持有不可变自引用；后续同槽定义仍是另一身份。
                        // 已有参数、循环 binding 或 captured cell 的覆盖仍需要独立快照。
                        bindings.bound_temp_targets.insert(temp, BoundSlotTarget::Local(local));
                        bindings.temp_decl_locals.insert(temp, local);
                        bindings.declared_local_home_slots.push((local, HomeSlotKey::new(
                            closure.dst.index(), slot_epochs.epoch_at(closure.dst, site),
                        )));
                    }
                    (site, local)
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
    // 失败产物只保留诊断和独立展示的子 proto；这些占位 local 不是已恢复的 VM binding。
    // 与合成 factory 一样显式登记 home-free，后层不能把缺失原型事实当作未知物理根。
    for local in (0..local_count).map(LocalId) {
        artifacts.promotion_facts[id.index()].record_home_free_local(local);
    }
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
        lexical_environment_local: None,
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
    id: HirProtoRef,
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    structure: &ReadyStructureFacts,
    fixed_temps: &[TempId],
    phi_temps: &[TempId],
) -> Vec<Option<HirDebugScope>> {
    use crate::structure::DebugBindingValue;
    let mut scopes = vec![None; proto.debug_locals.len()];
    for fact in structure.debug_bindings().accepted() {
        let unused_initializer = match fact.value {
            DebugBindingValue::BranchInitializer(owner) => structure
                .plan()
                .unused_comparison_initializer(owner, proto, cfg, dataflow)
                .and_then(|initializer| {
                    let [first, second] = initializer.defs;
                    let result = fixed_temps[first.index()];
                    (result == fixed_temps[second.index()]).then_some(HirDebugBranchInitializer {
                        result,
                        condition: crate::hir::common::HirSourceSite {
                            proto: id,
                            instr: initializer.predicate,
                        },
                    })
                }),
            DebugBindingValue::Ssa(_) => None,
        };
        scopes[fact.scope] = Some(HirDebugScope {
            initializer_end_instr: fact.initializer_end_instr,
            end_instr: fact.end_instr,
            initializer_temp: match fact.value.ssa() {
                Some(SsaValue::Def(def)) => fixed_temps.get(def.index()).copied(),
                Some(SsaValue::Entry(_) | SsaValue::Phi(_)) | None => {
                    unused_initializer.map(|initializer| initializer.result)
                }
            },
            initializer_phi: match fact.value.ssa() {
                Some(SsaValue::Phi(phi)) => phi_temps.get(phi.index()).copied(),
                _ => None,
            },
            branch_initializer: match fact.value.ssa() {
                Some(SsaValue::Phi(phi)) => debug_branch_initializer(
                    id,
                    proto,
                    dataflow,
                    structure.plan(),
                    phi,
                    fact.start_pc,
                    phi_temps,
                ),
                Some(SsaValue::Entry(_) | SsaValue::Def(_)) | None => unused_initializer,
            },
            start_pc: fact.start_pc,
            end_pc: fact.end_pc,
            ends_before_return: fact
                .end_instr
                .is_some_and(|instr| debug_scope_end_precedes_return(proto, instr)),
        });
    }
    scopes
}

/// 只有原 scope 从已选 branch 的 continuation 开始，才把合流临时声明还原成
/// initializer；不能将比较前已可见的 local（regress_342）误判为新声明。
fn debug_branch_initializer(
    id: HirProtoRef,
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    phi: PhiId,
    start_pc: u32,
    phi_temps: &[TempId],
) -> Option<HirDebugBranchInitializer> {
    use crate::structure::{PhiIncomingDisposition, RegionPlan};

    let phi_plan = plan.phi_plan(phi)?;
    let [first, second] = phi_plan.incomings.as_slice() else {
        return None;
    };
    let PhiIncomingDisposition::RegionResult(owner) = first.disposition else {
        return None;
    };
    if second.disposition != PhiIncomingDisposition::RegionResult(owner) {
        return None;
    }
    let RegionPlan::Branch {
        plan: branch,
        continuation: Some(continuation),
        ..
    } = plan.region(owner)?
    else {
        return None;
    };
    let scope_entry = proto.lowering_map.low_instr_at_or_after_pc(start_pc)?;
    if *continuation != phi_plan.block
        || plan.block_terminator(phi_plan.block)?.instrs.start != scope_entry
    {
        return None;
    }
    let condition = plan.condition(plan.branch(*branch)?.condition)?;
    let [node] = condition.nodes.as_slice() else {
        return None;
    };
    if node.materialized_value.is_some()
        || !matches!(proto.instrs.get(node.predicate.index()),
            Some(LowInstr::Branch(branch))
                if matches!(branch.cond.subject, crate::transformer::BranchSubject::Compare { .. }))
    {
        return None;
    }
    let mut values = [false; 2];
    for (index, incoming) in [first, second].into_iter().enumerate() {
        let SsaValue::Def(def) = incoming.value else {
            return None;
        };
        let site = dataflow.def_instr(def);
        let LowInstr::LoadBool(value) = proto.instrs.get(site.index())? else {
            return None;
        };
        if value.dst != phi_plan.reg
            || site.index() <= node.predicate.index()
            || site.index() >= scope_entry.index()
        {
            return None;
        }
        values[index] = value.value;
    }
    (values[0] != values[1]).then_some(HirDebugBranchInitializer {
        result: *phi_temps.get(phi.index())?,
        condition: crate::hir::common::HirSourceSite {
            proto: id,
            instr: node.predicate,
        },
    })
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
        if captured_plan.is_consumed(InstrRef(index))
            || captured_plan.replacement_at(InstrRef(index)).is_some()
        {
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
    #[expect(
        clippy::too_many_arguments,
        reason = "入口许可与既有 capture lowering 共享原始事实"
    )]
    fn new(
        mut plan: SharedClosurePlan,
        composite_protos: &'a [HirProtoRef],
        proto: &LoweredProto,
        cfg: &Cfg,
        dataflow: &DataflowFacts,
        facts: &ProtoPromotionFacts,
        bindings: &mut ProtoBindings,
        allow_identity: bool,
    ) -> Self {
        let publication_plan = allow_identity.then(|| {
            let mut candidate = plan.clone();
            candidate.restore_publications(proto, cfg, dataflow);
            candidate
        });
        let allow_identity = publication_plan
            .as_ref()
            .is_some_and(|candidate| identity_inline_scope(proto, candidate));
        let mut identity_initializers = BTreeMap::new();
        let mut factory_locals = Vec::with_capacity(plan.composites().len());
        let mut capture_barriers = Vec::with_capacity(plan.composites().len());
        let mut literal_initializers = BTreeMap::new();
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
                if let Some(def) = captured_fixed_def(dataflow, instr, source) {
                    let producer = dataflow.def_instr(def);
                    if literal_initializers.contains_key(&producer)
                        || identity_initializers.contains_key(&producer)
                    {
                        continue;
                    }
                    // 只移动严格相邻的 scalar NaN 屏障；原 slot 相邻且存在原 scratch
                    // 容量，不把跨调用/控制流或多分量字面量准备当作无观察初始化。
                    let scalar_nan = match proto.instrs.get(producer.index()) {
                        Some(LowInstr::LoadNumber(load)) => load.value.is_nan(),
                        Some(LowInstr::LoadConst(load)) => matches!(
                            proto.constants.get(load.value.index()),
                            Some(crate::parser::RawLiteralConst::Number(value)) if value.is_nan()
                        ),
                        _ => false,
                    };
                    let temp = bindings.fixed_temps[def.index()];
                    if scalar_nan
                        && allow_identity
                        && producer.index() + 1 == index
                        && !composite.preserve_owner_value
                        && plan.owner_at(InstrRef(0)).is_none()
                        && plan.replacement_at(InstrRef(0)).is_none()
                        && !plan.is_consumed(InstrRef(0))
                        && bindings.temp_target(temp).is_none()
                        && let Some(identity) = identity_capture_initializer(
                            proto, cfg, dataflow, facts, bindings, producer, temp,
                        )
                    {
                        identity_initializers.insert(producer, identity);
                        continue;
                    }
                    if scalar_nan
                        && producer.index() + 1 == index
                        && cfg.instr_to_block[producer.index()] == cfg.instr_to_block[index]
                        && dataflow.def_reg(def).index() + 1 == owner_dst.index()
                        && owner_dst.index() + 1 < usize::from(proto.frame.max_stack_size)
                        && bindings.temp_target(temp).is_none()
                        && !composite.preserve_owner_value
                        // 表分配先于读取写回；原 NaN 槽的旧资源不能因此跨过 GC 观察。
                        && facts.overwrites_gc_inert(temp)
                    {
                        literal_initializers.insert(producer, temp);
                        continue;
                    }
                }
                let local = LocalId(bindings.local_count);
                bindings.local_count += 1;
                bindings.local_debug_hints.push(None);
                bindings.local_debug_scopes.push(None);
                *snapshot = Some(local);
            }
            let barrier = snapshots.iter().any(Option::is_some).then(|| {
                let box_local = (snapshots.iter().flatten().count() > 1).then(|| {
                    let local = LocalId(bindings.local_count);
                    bindings.local_count += 1;
                    bindings.local_debug_hints.push(None);
                    bindings.local_debug_scopes.push(None);
                    local
                });
                SharedCaptureBarrier {
                    box_local,
                    snapshots,
                }
            });
            capture_barriers.push(barrier);
        }
        // 同一恒等宏也保留原常量 TEST 的编译边界；只接相邻、唯一读取的 Boolean 准备。
        // 它在条件语境直接发射，不能额外声明一个持续占槽的结果 local。
        if let Some(identity) = identity_initializers.values().next().copied() {
            // 同一模块中的整数 capture 也保持不透明，否则 O2 会将子函数改成常量
            // 返回，并在保留 debug 的再编译中为每个原 capture 添一份准备写。
            for composite in plan.composites() {
                for &source in &composite.outer_captures {
                    let Some(def) = captured_fixed_def(dataflow, composite.anchor, source) else {
                        continue;
                    };
                    let producer = dataflow.def_instr(def);
                    let temp = bindings.fixed_temps[def.index()];
                    if matches!(&proto.instrs[producer.index()], LowInstr::LoadInteger(load)
                        if (-32768..=32767).contains(&load.value))
                        && producer.index() + 1 == composite.anchor.index()
                        && cfg.instr_to_block[producer.index()]
                            == cfg.instr_to_block[composite.anchor.index()]
                        && bindings.temp_target(temp).is_none()
                    {
                        identity_initializers
                            .insert(producer, IdentityCaptureInitializer { temp, ..identity });
                    }
                }
            }
            for (index, pair) in proto.instrs.windows(2).enumerate() {
                let [LowInstr::LoadBool(load), LowInstr::Branch(branch)] = pair else {
                    continue;
                };
                if !matches!(branch.cond.subject, crate::transformer::BranchSubject::Truthy(crate::transformer::CondOperand::Reg(reg)) if reg == load.dst)
                {
                    continue;
                }
                let site = InstrRef(index);
                let Some(def) = dataflow.instr_def_for_reg(site, load.dst) else {
                    continue;
                };
                let uses = &dataflow.def_uses[def.index()];
                let temp = bindings.fixed_temps[def.index()];
                if uses.len() == 1
                    && uses[0].instr == InstrRef(index + 1)
                    && dataflow.def_phi_uses[def.index()].is_empty()
                    && bindings.temp_target(temp).is_none()
                {
                    identity_initializers
                        .insert(site, IdentityCaptureInitializer { temp, ..identity });
                }
            }
        }
        if !identity_initializers.is_empty() {
            plan = publication_plan.expect("identity contract requires a checked publication plan");
            plan.restore_effect_prefixes(proto, cfg, dataflow);
        }
        Self {
            plan,
            factory_locals,
            capture_barriers,
            literal_initializers,
            identity_initializers,
            composite_protos,
        }
    }

    pub(super) fn effect_prefix_at(&self, site: InstrRef) -> bool {
        self.plan.effect_prefix_at(site)
    }

    pub(super) fn factory_local(&self, factory: CompositeFactoryRef) -> LocalId {
        self.factory_locals[factory.0]
    }

    pub(super) fn has_literal_initializer(&self, instr: InstrRef) -> bool {
        self.literal_initializers.contains_key(&instr)
    }

    /// factory 独占替换原 owner 的一次写时，沿用该写的物理 home，不能传播原函数值身份。
    /// 保留 owner 或 NaN capture 屏障会新增声明，不能把最后一个 factory 冒充原 dst；
    /// 已打开引用的 dst 也属于现有 cell。最终源码声明顺序仍由 source_frames 核对。
    fn record_anchor_homes(
        &self,
        proto: &LoweredProto,
        dataflow: &DataflowFacts,
        slot_epochs: &SlotEpochFacts,
        bindings: &ProtoBindings,
        facts: &mut ProtoPromotionFacts,
    ) {
        for (index, composite) in self.plan.composites().iter().enumerate() {
            let anchor = composite.anchor;
            if composite.preserve_owner_value
                || self.plan.is_consumed(anchor)
                || self.capture_barriers[index].is_some()
                || bindings
                    .capture_empty_local_decls
                    .get(&anchor.index())
                    .is_some_and(|locals| !locals.is_empty())
            {
                continue;
            }
            let Some(LowInstr::Closure(closure)) = proto.instrs.get(anchor.index()) else {
                continue;
            };
            if slot_epochs.reference_capture_may_be_open(closure.dst, anchor) {
                continue;
            }
            let Some(def) = dataflow.instr_def_for_reg(anchor, closure.dst) else {
                continue;
            };
            let temp = bindings.fixed_temps[def.index()];
            if bindings.temp_target(temp).is_some() {
                continue;
            }
            if let Some(home) = facts.trusted_temp_home_slot(temp) {
                facts.record_local_home_slot(self.factory_locals[index], home);
            }
        }
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

/// 只在值分支和可原样重发的字面量 TEST 中启用宏；普通控制臂仍需独立的 O2 证明。
fn identity_control_scope(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
) -> bool {
    use crate::structure::RegionPlan;
    use crate::transformer::{BranchSubject, CondOperand};
    plan.regions().all(|(_, region)| match region {
        RegionPlan::Block { .. }
        | RegionPlan::Sequence { .. }
        | RegionPlan::ValueDecision { .. } => true,
        RegionPlan::Branch { plan: branch, .. } => plan.branch(*branch).is_some_and(|branch| {
            branch.value_plan.is_some()
                && plan.condition(branch.condition).is_some_and(|condition| {
                    condition.nodes.iter().all(|node| {
                        let LowInstr::Branch(branch) = &proto.instrs[node.predicate.index()] else {
                            return false;
                        };
                        let BranchSubject::Truthy(operand) = branch.cond.subject else {
                            return true;
                        };
                        let CondOperand::Reg(reg) = operand else {
                            return false;
                        };
                        let SsaValue::Def(def) = dataflow.use_value(node.predicate, reg) else {
                            return false;
                        };
                        let producer = dataflow.def_instr(def);
                        matches!(proto.instrs[producer.index()], LowInstr::LoadBool(_))
                            && producer.index() + 1 == node.predicate.index()
                            && dataflow.def_uses[def.index()].len() == 1
                            && dataflow.def_phi_uses[def.index()].is_empty()
                    })
                })
        }),
        _ => false,
    })
}

/// O2 许可会作用于整份源码；这里只接受原值决策、普通输出/断言和已证明的共享工厂。
/// 后层仍按最终 AST 核对声明、opaque callee 与工厂成本，不能仅凭恒等函数本身放行。
fn identity_inline_scope(proto: &LoweredProto, plan: &SharedClosurePlan) -> bool {
    let reads_value = |child: &LoweredProto| {
        matches!(child.instrs.as_slice(), [LowInstr::GetUpvalue(load), LowInstr::Return(ret)]
            if matches!(ret.values, ValuePack::Fixed(range) if range.start == load.dst && range.len == 1))
            || matches!(child.instrs.as_slice(), [LowInstr::LoadInteger(load), LowInstr::Return(ret)]
            if matches!(ret.values, ValuePack::Fixed(range) if range.start == load.dst && range.len == 1))
    };
    let publications = plan
        .composites()
        .iter()
        .filter_map(|composite| composite.effect.as_ref())
        .filter(|effect| effect.kind == SharedFactoryEffectKind::Publish)
        .map(|effect| &effect.field)
        .collect::<BTreeSet<_>>();
    proto.instrs.iter().enumerate().all(|(index, instr)| match instr {
        LowInstr::Move(_) | LowInstr::LoadNil(_) | LowInstr::LoadBool(_)
        | LowInstr::LoadConst(_) | LowInstr::LoadInteger(_) | LowInstr::LoadNumber(_)
        | LowInstr::Closure(_) | LowInstr::Call(_) | LowInstr::Branch(_) | LowInstr::Jump(_)
        | LowInstr::Return(_) => true,
        LowInstr::SetTable(_) => plan.effect_prefix_at(InstrRef(index)),
        LowInstr::GetTable(get) if get.base == AccessBase::Env => {
            matches!(get.key, AccessKey::Const(key) if matches!(proto.constants.get(key.index()),
                Some(crate::parser::RawLiteralConst::String(name)) if matches!(name.bytes.as_ref(), b"print" | b"assert") || publications.contains(&raw_lua_string(name))))
        }
        _ => false,
    }) && plan.composites().iter().all(|composite| {
        if composite.effect.as_ref().is_some_and(|effect| effect.kind == SharedFactoryEffectKind::Publish) { return true; }
        match composite.nodes.as_slice() {
            [node] => proto.children.get(node.proto.index()).is_some_and(|child|
                child.signature.num_params == 0 && !child.signature.is_vararg && reads_value(child)),
            [dependency, root] => {
                let Some(owner) = proto.children.get(dependency.proto.index()) else { return false; };
                let Some(child) = proto.children.get(root.proto.index()) else { return false; };
                owner.signature.num_params == 0 && owner.signature.is_vararg && reads_value(owner)
                    && child.signature.num_params == 0 && !child.signature.is_vararg
                    && matches!(child.instrs.as_slice(), [LowInstr::GetUpvalue(load), LowInstr::Call(call), LowInstr::Return(ret)]
                        if load.dst == call.callee && matches!(call.args, ValuePack::Fixed(range) if range.len == 0)
                        && matches!((call.results, ret.values), (ResultPack::Open(result), ValuePack::Open(value)) if result == value))
            }
            _ => false,
        }
    })
}

fn identity_capture_initializer(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    facts: &ProtoPromotionFacts,
    bindings: &mut ProtoBindings,
    producer: InstrRef,
    temp: TempId,
) -> Option<IdentityCaptureInitializer> {
    if producer.index() != 1
        || proto.signature.num_params != 0
        || cfg.instr_to_block[0] != cfg.instr_to_block[1]
        || facts.trusted_temp_home_slot(temp) != Some(HomeSlotKey::new(1, 0))
    {
        return None;
    }
    let LowInstr::Closure(closure) = proto.instrs.first()? else {
        return None;
    };
    if closure.dst != Reg(0) || !closure.captures.is_empty() {
        return None;
    }
    let child = proto.children.get(closure.proto.index())?;
    if child.signature.num_params != 1 || child.signature.is_vararg || !child.children.is_empty() {
        return None;
    }
    let [LowInstr::Return(ret)] = child.instrs.as_slice() else {
        return None;
    };
    if !matches!(ret.values, ValuePack::Fixed(range) if range.start == Reg(0) && range.len == 1) {
        return None;
    }
    let def = dataflow.instr_def_for_reg(InstrRef(0), Reg(0))?;
    let callee_temp = bindings.fixed_temps[def.index()];
    if !dataflow.def_uses[def.index()].is_empty()
        || !dataflow.def_phi_uses[def.index()].is_empty()
        || bindings.temp_target(callee_temp).is_some()
        || facts.trusted_temp_home_slot(callee_temp) != Some(HomeSlotKey::new(0, 0))
    {
        return None;
    }
    let local = LocalId(bindings.local_count);
    bindings.local_count += 1;
    bindings.local_debug_hints.push(None);
    bindings.local_debug_scopes.push(None);
    bindings.temp_decl_locals.insert(callee_temp, local);
    bindings
        .bound_temp_targets
        .insert(callee_temp, BoundSlotTarget::Local(local));
    bindings
        .declared_local_home_slots
        .push((local, HomeSlotKey::new(0, 0)));
    Some(IdentityCaptureInitializer {
        callee: local,
        child: closure.proto,
        temp,
    })
}

fn capture_needs_non_reflexive_barrier(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    instr: InstrRef,
    source: CaptureSource,
) -> bool {
    let Some(def) = captured_fixed_def(dataflow, instr, source) else {
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

fn captured_fixed_def(
    dataflow: &DataflowFacts,
    instr: InstrRef,
    source: CaptureSource,
) -> Option<crate::structure::DefId> {
    let CaptureSource::ByValue(reg) = source else {
        return None;
    };
    match dataflow.canonical_move_value(dataflow.use_value(instr, reg))? {
        SsaValue::Def(def) => Some(def),
        _ => None,
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

    let print_effect = plan
        .effect
        .as_ref()
        .filter(|effect| effect.kind == SharedFactoryEffectKind::Print);
    if let Some(event) = print_effect {
        body.stmts.push(HirStmt::CallStmt(Box::new(
            crate::hir::common::HirCallStmt {
                call: crate::hir::common::HirCallExpr {
                    required_luau_inlining: None,
                    source_site: None,
                    argument_roots: Vec::new(),
                    frame_root_ends: Vec::new(),
                    callee: HirExpr::GlobalRef(crate::hir::common::HirGlobalRef {
                        sources: Default::default(),
                        key: "print".into(),
                    }),
                    args: vec![
                        HirExpr::String(event.field.clone()),
                        HirExpr::ParamRef(ParamId(0)),
                    ]
                    .into(),
                    method: false.into(),
                    fastcall: None,
                    method_key: None,
                    callee_root_handoff: None,
                    method_rewrite_transaction: None,
                    plain_method_syntax: false,
                    boolean_prewrite_arguments: Vec::new(),
                },
            },
        )));
    }

    let mut integer_locals = BTreeMap::new();
    for capture in plan.nodes.iter().flat_map(|node| &node.captures) {
        if let CompositeCapture::Integer(value) = capture {
            let local = LocalId(plan.nodes.len() + integer_locals.len());
            if let std::collections::btree_map::Entry::Vacant(entry) = integer_locals.entry(*value)
            {
                entry.insert(local);
                body.stmts.push(HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![local],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(*value)]),
                    initializer_merge_transaction: None,
                })));
            }
        }
    }

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
                    CompositeCapture::Integer(value) => (
                        HirCaptureMode::ByValue,
                        crate::hir::HirBinding::Local(*integer_locals.get(&value)?),
                    ),
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
            source_site: None,
            // MatchedShape 的每个 dependency 都已配对 ReusableGroup；搬回词法 owner
            // 不丢掉原模板身份，也不伪造一个属于 synthetic proto 的指令坐标。
            creation: Some(crate::hir::HirClosureCreation::MayReuse {
                template: child.origin.span.offset,
            }),
            proto: child_ref,
            captures,
        }));
        body.stmts.push(HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: vec![local],
            values: HirValuePack::fixed(vec![closure]),
            initializer_merge_transaction: None,
        })));
        if index == 0
            && let Some(effect) = plan
                .effect
                .as_ref()
                .filter(|effect| effect.kind == SharedFactoryEffectKind::Publish)
        {
            // 内层调用必须保留源码边界：先让 O2 内联 inner，再内联 outer 才能重发原创建槽。
            body.stmts.push(super::helpers::assign_stmt(
                vec![HirLValue::Global(crate::hir::common::HirGlobalRef {
                    sources: Default::default(),
                    key: effect.field.clone(),
                })],
                vec![HirExpr::Call(Box::new(crate::hir::common::HirCallExpr {
                    required_luau_inlining: None,
                    source_site: None,
                    argument_roots: Vec::new(),
                    frame_root_ends: Vec::new(),
                    callee: HirExpr::LocalRef(local),
                    args: Default::default(),
                    method: false.into(),
                    fastcall: None,
                    method_key: None,
                    callee_root_handoff: None,
                    method_rewrite_transaction: None,
                    plain_method_syntax: false,
                    boolean_prewrite_arguments: Vec::new(),
                }))],
            ));
        }
    }
    if plan.root.index() >= plan.nodes.len() {
        return Err(error());
    }
    body.stmts.push(return_stmt(
        HirValuePack::fixed(vec![HirExpr::LocalRef(LocalId(plan.root.index()))]),
        None,
        None,
    ));
    let local_count = plan.nodes.len() + integer_locals.len();
    let mut promotion_facts = ProtoPromotionFacts::default();
    for local in (0..local_count).map(LocalId) {
        promotion_facts.record_home_free_local(local);
    }

    let proto = HirProto {
        id,
        source: owner.source.as_ref().map(raw_lua_string),
        line_range: owner.line_range,
        signature: crate::parser::ProtoSignature {
            num_params: u8::from(print_effect.is_some()),
            is_vararg: false,
            has_vararg_param_reg: false,
            named_vararg_table: false,
            legacy_arg_slot: false,
            legacy_arg_table: false,
        },
        params: print_effect.map(|_| vec![ParamId(0)]).unwrap_or_default(),
        param_debug_hints: print_effect.map(|_| vec![None]).unwrap_or_default(),
        local_count,
        vararg_param_local: None,
        local_debug_hints: vec![None; local_count],
        local_debug_scopes: vec![None; local_count],
        debug_scopes: Vec::new(),
        physical_root_temps: BTreeSet::new(),
        physical_root_locals: BTreeSet::new(),
        inline_dispositions: Default::default(),
        upvalues: (0..plan.outer_captures.len()).map(UpvalueId).collect(),
        lexical_environment_local: None,
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
        || open_pack_bridge_is_fastcall_library_lookup(proto, producer, consumer, between)
        || open_pack_bridge_is_callee_move(proto, producer, consumer, between)
}

fn open_pack_bridge_is_fastcall_library_lookup(
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
    let [LowInstr::GetTable(get)] = between else {
        return false;
    };
    // FASTCALL 的 fallback 也可从保存的库表读取字段。该查找不覆盖开放结果，
    // 且仍属于同一调用协议；普通查表不能借此把 producer 越过潜在 __index。
    matches!(call.kind, CallKind::FastCall(protocol) if protocol.tail_is_direct())
        && producer_start.index() >= args_start.index()
        && get.dst == call.callee
        && get.dst.index() < args_start.index()
        && get.kind == GetTableKind::Normal
        && matches!(get.base, AccessBase::Reg(base) if base.index() < args_start.index())
        && matches!(get.key, AccessKey::Const(_))
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
    let entry_nil_bindings = std::mem::take(&mut lowering.bindings.entry_nil_local_decls);
    let mut prefix = if entry_nil_bindings.is_empty() {
        Vec::new()
    } else {
        vec![HirStmt::LocalDecl(Box::new(HirLocalDecl {
            values: HirValuePack::fixed(vec![HirExpr::Nil; entry_nil_bindings.len()]),
            bindings: entry_nil_bindings,
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
                        source_site: None,
                        creation: None,
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
