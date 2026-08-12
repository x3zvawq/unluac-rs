//! 这个文件承载 HIR 初始恢复里真正的 lowering 内核。
//!
//! 外层 [analyze.rs](/Users/x3zvawq/workspace/unluac-rs/src/hir/analyze/mod.rs) 只负责组织模块和
//! 暴露主入口，这里集中放 proto 递归构造和共享 lowering 上下文。final edge 的 phi
//! copy 由 plan 执行器消费；单条 low-IR 指令到 HIR 语句的映射由 `instrs.rs` 负责，
//! captured Luau shared closure 的词法 factory 由 `shared_closures.rs` 先冻结，再由这里
//! 预留并填充 synthetic proto；避免主流程重新猜 closure identity。

use std::collections::{BTreeMap, BTreeSet};

use super::super::promotion::{ProtoPromotionFacts, SlotEpochFacts};
use super::bindings::build_bindings;
use super::helpers::{decode_raw_string, empty_proto, return_stmt};
use super::instrs::local_decl_stmts;
use super::shared_closures::{
    CompositeCapture, CompositeFactoryPlan, CompositeFactoryRef, SharedClosurePlan,
    build_shared_closure_plan,
};
use super::structure::build_structured_body;
use crate::ast::AstTargetDialect;
use crate::decompile::{DecompileContext, DecompileState};
use crate::hir::HirLowerError;
use crate::hir::common::{
    HirBlock, HirCapture, HirCaptureMode, HirClosureExpr, HirExpr, HirLValue, HirLocalDecl,
    HirProto, HirProtoRef, HirStmt, HirValuePack, LocalId, ParamId, TempId, UpvalueId,
};
use crate::structure::StructureFacts;
use crate::structure::{
    BlockRef, CanonicalMoveIndex, Cfg, CfgGraph, DataflowFacts, GraphFacts, OpenDefId, SsaValue,
};
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
    pub(super) fixed_temps: Vec<TempId>,
    pub(super) phi_temps: Vec<TempId>,
    pub(super) loop_guard_temps: Vec<Option<TempId>>,
    pub(super) repeat_staged_temps: Vec<Vec<TempId>>,
    pub(super) instr_fixed_defs: Vec<Vec<TempId>>,
    pub(super) captured_temp_targets: BTreeMap<TempId, BoundSlotTarget>,
    pub(super) captured_temp_decl_locals: BTreeMap<TempId, LocalId>,
    pub(super) capture_empty_local_decls: BTreeMap<usize, Vec<LocalId>>,
    pub(super) capture_entry_local_decls: Vec<LocalId>,
    pub(super) capture_region_local_decls: BTreeMap<crate::structure::RegionId, Vec<LocalId>>,
    pub(super) closure_capture_targets: BTreeMap<(usize, usize), BoundSlotTarget>,
    pub(super) reference_captured_regs: Vec<bool>,
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
    pub(super) structure: &'a StructureFacts,
    pub(super) child_refs: &'a [HirProtoRef],
    pub(super) bindings: ProtoBindings,
    pub(super) shared_closure_locals: BTreeMap<SharedClosureRef, (LocalId, ProtoRef)>,
    pub(super) captured_shared_closures: CapturedSharedClosureLowering,
    pub(super) open_pack_owners: Vec<Option<InstrRef>>,
    pub(super) owned_open_producers: Vec<bool>,
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
    )?
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
) -> Result<LoweredProtoResult, HirLowerError> {
    let cfg = &cfg_graph.cfg;
    let captured_shared_plan =
        build_shared_closure_plan(proto, cfg_graph, graph_facts, dataflow, structure.plan())?;
    let id = HirProtoRef(artifacts.protos.len());
    artifacts.protos.push(empty_proto(id));
    artifacts
        .promotion_facts
        .push(ProtoPromotionFacts::default());
    let composite_protos =
        reserve_composite_factory_protos(captured_shared_plan.composites().len(), artifacts);

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
        .collect::<Result<Vec<_>, _>>()?;
    let child_refs = child_results
        .iter()
        .map(|child| child.id)
        .collect::<Vec<_>>();
    let child_mutable_upvalues = child_results
        .into_iter()
        .map(|child| child.mutable_upvalues)
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
    let lowering = ProtoLowering {
        target,
        proto,
        cfg,
        dataflow,
        structure,
        child_refs: &child_refs,
        bindings,
        shared_closure_locals,
        captured_shared_closures,
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
        body: build_proto_body(id, &lowering)?,
        children: lowering.hir_children(),
    };
    artifacts.promotion_facts[id.index()] =
        ProtoPromotionFacts::from_plan(dataflow, structure.plan(), &slot_epochs);

    Ok(LoweredProtoResult {
        id,
        mutable_upvalues: mutable_upvalues_for_proto(proto, &child_mutable_upvalues),
    })
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
        upvalues: (0..plan.outer_captures.len()).map(UpvalueId).collect(),
        upvalue_debug_hints: vec![None; plan.outer_captures.len()],
        temps: Vec::new(),
        temp_debug_locals: Vec::new(),
        body,
        children,
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
    let mut prefix = local_decl_stmts(lowering.bindings.capture_entry_local_decls.clone());
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
