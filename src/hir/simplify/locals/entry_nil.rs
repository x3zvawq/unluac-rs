//! 删除 Structure 为 Entry(nil) region-result 物化的冗余 nil 边写入。
//!
//! 消费 canonical phi provenance、物理身份与共享 HIR 控制流，证明原 nil 状态仍有效后提交。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::simplify::stmt_plan::{PathComponent, StmtPath, remove_planned_stmts};

use crate::hir::common::{
    HirAssign, HirExpr, HirIf, HirLValue, HirLocalDecl, HirProto, HirStmt, LocalId, TempId,
};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

use super::super::label_refs::count_label_references;
use super::super::lexical_cfg::{HirFlowGraph, HirFlowNodeId, HirFlowNodeKind, HirForBindings};
use super::super::local_shapes::empty_single_local_decl_binding;
use crate::hir::visit::{self, HirVisitor};

// bit 下标为 known_nil * 2 + reference_exposed；只存在四个路径状态。
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct NilStates(u8);

impl NilStates {
    fn entry() -> Self {
        Self(0b0100)
    }
    fn unknown() -> Self {
        Self(0b0010)
    }
    fn is_empty(&self) -> bool {
        self.0 == 0
    }
    fn all_known_nil(&self) -> bool {
        !self.is_empty() && self.0 & 0b0011 == 0
    }
    fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }
    fn set_known_nil(self, known_nil: bool) -> Self {
        Self(((self.0 | (self.0 >> 2)) & 0b0011) << (u32::from(known_nil) * 2))
    }
    fn expose_reference(self) -> Self {
        Self((self.0 & 0b1010) | ((self.0 & 0b0101) << 1))
    }
    fn opaque_callback(self) -> Self {
        Self((self.0 & 0b0111) | ((self.0 & 0b1000) >> 2))
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PruneError {
    DeferredDecision,
    DiagnosticResidual,
    BindingInvariant,
}

#[derive(Default)]
struct PrunePlan {
    redundant: BTreeSet<HirFlowNodeId>,
    not_redundant: BTreeSet<HirFlowNodeId>,
}

impl PrunePlan {
    fn observe_nil_write(&mut self, node: HirFlowNodeId, states: &NilStates) {
        if states.all_known_nil() && !self.not_redundant.contains(&node) {
            self.redundant.insert(node);
        } else {
            self.redundant.remove(&node);
            self.not_redundant.insert(node);
        }
    }
}

pub(super) fn prune_redundant_entry_nil_writes(
    proto: &mut HirProto,
    facts: &mut ProtoPromotionFacts,
    safety: HirExprSafety,
) -> bool {
    if proto.body.stmts.len() < 2 {
        return false;
    }

    let debug_homes = debug_identity_homes(proto, facts);
    let owner_label_refs = count_label_references(&proto.body.stmts);
    let mut changed = false;
    for index in 0..proto.body.stmts.len() - 1 {
        let Some(local) = empty_single_local_decl_binding(&proto.body.stmts[index]) else {
            continue;
        };
        if !facts.is_entry_nil_phi_local(local) {
            // 普通空 local 没有 canonical Entry(nil) phi provenance，不属于
            // 这个定向裁剪器的候选集；这里没有待交给其他 pass 的候选。
            continue;
        }
        let candidate_home = facts
            .trusted_local_home_slot(local)
            .expect("entry-nil phi local must retain its trusted home");
        if debug_homes
            .as_ref()
            .is_none_or(|homes| homes.contains(&candidate_home))
        {
            // 候选拒绝[PolicyBoundary]：候选自身或已证明同 home 的 binding 带 source debug identity 时保留显式 nil 边写，维护源码/调试形状。
            continue;
        }
        let if_owner = &proto.body.stmts[index + 1];
        if !matches!(if_owner, HirStmt::If(_)) {
            continue;
        }

        let analyzer = EntryNilAnalyzer {
            local,
            candidate_home,
            facts,
            safety,
            owner_label_refs: &owner_label_refs,
        };
        let redundant = match analyzer.analyze(if_owner) {
            Ok(plan) => plan,
            Err(error) => {
                match error {
                    PruneError::DeferredDecision => {
                        // 候选拒绝[LayerBoundary]：Decision 的执行路径由 decision/eliminate owner
                        // 收敛；owner 会 invalidates LocalBinding/TempChain/BlockStructure，locals
                        // 依赖这些 tag，因此物化后会重审本候选。
                    }
                    PruneError::DiagnosticResidual => {
                        // 候选拒绝[PolicyBoundary]：Unresolved 是 permissive 输出保留的失败证据，
                        // entry-nil 不据未知路径删除边写。
                    }
                    PruneError::BindingInvariant => {
                        panic!("entry-nil local must not be redeclared or reused as a for binding")
                    }
                }
                continue;
            }
        };
        if redundant.is_empty() {
            continue;
        }

        let HirStmt::If(if_stmt) = &mut proto.body.stmts[index + 1] else {
            unreachable!()
        };
        apply_if_plan(if_stmt, &redundant);
        changed = true;
    }
    changed
}

struct EntryNilAnalyzer<'a> {
    local: LocalId,
    candidate_home: HomeSlotKey,
    facts: &'a ProtoPromotionFacts,
    safety: HirExprSafety,
    owner_label_refs: &'a std::collections::BTreeMap<crate::hir::HirLabelId, usize>,
}

impl<'a> EntryNilAnalyzer<'a> {
    fn analyze(&self, if_owner: &HirStmt) -> Result<BTreeSet<StmtPath>, PruneError> {
        let stmts = std::slice::from_ref(if_owner);
        let internal_refs = count_label_references(stmts);
        let mut paths = BTreeMap::new();
        let mut external_entries = Vec::new();
        let Ok(graph) = HirFlowGraph::for_stmts_with_locations(
            stmts,
            self.safety,
            |id, event, block, index| {
                match event {
                    HirFlowNodeKind::Stmt(HirStmt::Assign(assign))
                        if is_direct_nil_write(assign, self.local) =>
                    {
                        let mut path = block.to_stmt_path(index);
                        // 区域根是单条 If；既有提交器从它的 Then/Else 开始导航。
                        path.remove(0);
                        paths.insert(id, path);
                    }
                    HirFlowNodeKind::Stmt(HirStmt::Label(label))
                        if internal_refs.get(&label.id) != self.owner_label_refs.get(&label.id) =>
                    {
                        // 区域外的到达不能继承入口 nil；种子也参与回边不动点。
                        external_entries.push((id, NilStates::unknown()));
                    }
                    _ => {}
                }
            },
        ) else {
            // 候选拒绝[ProofIncomplete]：label 身份不唯一，无法为删除计划证明完整路径。
            return Ok(BTreeSet::new());
        };
        if paths.is_empty() {
            return Ok(BTreeSet::new());
        }
        let transfers: Vec<_> = graph
            .nodes()
            .iter()
            .map(|node| self.collect_event(node.kind()))
            .collect();
        let mut plan = PrunePlan::default();
        let mut error = None;
        graph.solve_forward_with_entries(
            NilStates::entry(),
            external_entries,
            |current, incoming| {
                let joined = current.union(*incoming);
                let changed = *current != joined;
                *current = joined;
                changed
            },
            |id, _, states| {
                if states.is_empty() {
                    return;
                }
                let transfer = &transfers[id.index()];
                let evaluated = transfer
                    .failure
                    .map_or_else(|| transfer.evaluation.apply(*states), Err);
                match evaluated {
                    Ok(mut next) => {
                        if paths.contains_key(&id) {
                            plan.observe_nil_write(id, &next);
                        }
                        if let Some(known_nil) = transfer.overwrite {
                            next = next.set_known_nil(known_nil);
                        }
                        *states = next;
                    }
                    Err(failure) => {
                        error.get_or_insert(failure);
                        *states = NilStates::default();
                    }
                }
            },
        );
        if let Some(error) = error {
            return Err(error);
        }
        Ok(plan
            .redundant
            .into_iter()
            .map(|id| {
                paths
                    .remove(&id)
                    .expect("nil write must retain its snapshot path")
            })
            .collect())
    }

    fn collect_event(&self, event: HirFlowNodeKind<'_>) -> NilTransfer<'a> {
        let mut transfer = NilTransfer::default();
        match event {
            HirFlowNodeKind::Stmt(HirStmt::If(stmt)) => transfer.evaluation = self.expr(&stmt.cond),
            HirFlowNodeKind::Stmt(HirStmt::While(stmt)) => {
                transfer.evaluation = self.expr(&stmt.cond)
            }
            HirFlowNodeKind::RepeatCondition(stmt) => transfer.evaluation = self.expr(&stmt.cond),
            HirFlowNodeKind::Stmt(HirStmt::NumericFor(stmt)) => {
                if stmt.binding == self.local {
                    transfer.failure = Some(PruneError::BindingInvariant);
                }
                transfer.evaluation = self.exprs([&stmt.start, &stmt.limit, &stmt.step]);
            }
            HirFlowNodeKind::GenericForInit(flow) => {
                if flow.for_stmt().bindings.contains(&self.local) {
                    transfer.failure = Some(PruneError::BindingInvariant);
                }
                transfer.evaluation = self.exprs(&flow.for_stmt().iterator);
            }
            HirFlowNodeKind::GenericForDispatch(_) | HirFlowNodeKind::Stmt(HirStmt::Close(_)) => {
                transfer.evaluation = NilEvaluation::Opaque;
            }
            HirFlowNodeKind::ForBinding(bindings) => {
                let writes = match bindings {
                    HirForBindings::Numeric(local) => {
                        !matches!(self.local_binding_relation(local), BindingRelation::None)
                    }
                    HirForBindings::Generic(flow) => {
                        flow.for_stmt().bindings.iter().any(|&local| {
                            !matches!(self.local_binding_relation(local), BindingRelation::None)
                        })
                    }
                };
                transfer.overwrite = writes.then_some(false);
            }
            HirFlowNodeKind::Stmt(HirStmt::LocalRootRelease(local)) => {
                transfer.overwrite = (*local == self.local).then_some(true);
            }
            HirFlowNodeKind::Exit
            | HirFlowNodeKind::FunctionExit
            | HirFlowNodeKind::NumericForDispatch
            | HirFlowNodeKind::Stmt(
                HirStmt::Label(_) | HirStmt::Goto(_) | HirStmt::Break | HirStmt::Continue,
            ) => {}
            HirFlowNodeKind::UnknownControl => {
                unreachable!("region graph has no unknown-control sink")
            }
            HirFlowNodeKind::Stmt(
                HirStmt::Block(_) | HirStmt::Repeat(_) | HirStmt::GenericFor(_),
            ) => {
                unreachable!("shared graph must split structured owners into typed events")
            }
            HirFlowNodeKind::Stmt(stmt) => {
                let mut effects = ExprEffects::new(self.candidate_home, self.facts);
                visit::visit_stmts(std::slice::from_ref(stmt), &mut effects);
                transfer.evaluation = NilEvaluation::Expr(effects);
                match stmt {
                    HirStmt::Assign(assign) => {
                        transfer.overwrite = assign
                            .targets
                            .iter()
                            .enumerate()
                            .filter_map(|(index, target)| {
                                self.binding_relation(target)
                                    .written_value(assigned_value_is_nil(assign, index))
                            })
                            .next_back();
                    }
                    HirStmt::LocalDecl(decl) => {
                        if decl.bindings.contains(&self.local) {
                            transfer.failure = Some(PruneError::BindingInvariant);
                        }
                        transfer.overwrite = decl
                            .bindings
                            .iter()
                            .enumerate()
                            .filter_map(|(index, &local)| {
                                self.local_binding_relation(local)
                                    .written_value(declared_value_is_nil(decl, index))
                            })
                            .next_back();
                    }
                    _ => {}
                }
            }
        }
        transfer
    }

    fn expr(&self, expr: &HirExpr) -> NilEvaluation<'a> {
        NilEvaluation::Expr(self.expr_effects(expr))
    }

    fn expr_effects(&self, expr: &HirExpr) -> ExprEffects<'a> {
        let mut effects = ExprEffects::new(self.candidate_home, self.facts);
        visit::visit_expr(expr, &mut effects);
        effects
    }

    fn exprs<'e>(&self, exprs: impl IntoIterator<Item = &'e HirExpr>) -> NilEvaluation<'a> {
        NilEvaluation::Ordered(
            exprs
                .into_iter()
                .map(|expr| self.expr_effects(expr))
                .collect(),
        )
    }

    fn binding_relation(&self, target: &HirLValue) -> BindingRelation {
        match target {
            HirLValue::Local(local) => self.local_binding_relation(*local),
            HirLValue::Param(param) => relation_for_home(
                self.facts.trusted_param_home_slot(*param),
                self.candidate_home,
            ),
            HirLValue::Temp(temp) => relation_for_home(
                self.facts.trusted_temp_home_slot(*temp),
                self.candidate_home,
            ),
            HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_) => {
                BindingRelation::None
            }
        }
    }

    fn local_binding_relation(&self, local: LocalId) -> BindingRelation {
        if local == self.local {
            BindingRelation::Definite
        } else {
            relation_for_home(
                self.facts.trusted_local_home_slot(local),
                self.candidate_home,
            )
        }
    }
}

#[derive(Clone, Copy)]
enum BindingRelation {
    None,
    Possible,
    Definite,
}

impl BindingRelation {
    fn written_value(self, known_nil: bool) -> Option<bool> {
        match self {
            Self::None => None,
            Self::Possible => Some(false),
            Self::Definite => Some(known_nil),
        }
    }
}

fn relation_for_home(home: Option<HomeSlotKey>, candidate: HomeSlotKey) -> BindingRelation {
    match home {
        Some(home) if home == candidate => BindingRelation::Definite,
        Some(_) => BindingRelation::None,
        None => BindingRelation::Possible,
    }
}

fn is_direct_nil_write(assign: &HirAssign, local: LocalId) -> bool {
    matches!(assign.targets.as_slice(), [HirLValue::Local(target)] if *target == local)
        && matches!(assign.values.fixed.as_slice(), [HirExpr::Nil])
        && assign.values.tail.is_none()
}

fn assigned_value_is_nil(assign: &HirAssign, target_index: usize) -> bool {
    value_at_is_nil(
        &assign.values.fixed,
        assign.values.tail.is_some(),
        target_index,
    )
}

fn declared_value_is_nil(decl: &HirLocalDecl, binding_index: usize) -> bool {
    value_at_is_nil(
        &decl.values.fixed,
        decl.values.tail.is_some(),
        binding_index,
    )
}

fn value_at_is_nil(fixed: &[HirExpr], has_tail: bool, index: usize) -> bool {
    fixed
        .get(index)
        .is_some_and(|value| matches!(value, HirExpr::Nil))
        || (!has_tail && index >= fixed.len())
}

#[derive(Default)]
struct NilTransfer<'a> {
    evaluation: NilEvaluation<'a>,
    overwrite: Option<bool>,
    failure: Option<PruneError>,
}

#[derive(Default)]
enum NilEvaluation<'a> {
    #[default]
    Identity,
    Opaque,
    Expr(ExprEffects<'a>),
    Ordered(Box<[ExprEffects<'a>]>),
}

impl NilEvaluation<'_> {
    fn apply(&self, states: NilStates) -> Result<NilStates, PruneError> {
        match self {
            Self::Identity => Ok(states),
            Self::Opaque => Ok(states.opaque_callback()),
            Self::Expr(effects) => effects.apply(states),
            Self::Ordered(effects) => effects
                .iter()
                .try_fold(states, |states, effect| effect.apply(states)),
        }
    }
}

struct ExprEffects<'a> {
    candidate_home: HomeSlotKey,
    facts: &'a ProtoPromotionFacts,
    captures_reference: bool,
    has_call: bool,
    decision: bool,
    unresolved: bool,
}

impl<'a> ExprEffects<'a> {
    fn new(candidate_home: HomeSlotKey, facts: &'a ProtoPromotionFacts) -> Self {
        Self {
            candidate_home,
            facts,
            captures_reference: false,
            has_call: false,
            decision: false,
            unresolved: false,
        }
    }

    fn apply(&self, mut states: NilStates) -> Result<NilStates, PruneError> {
        if self.decision {
            return Err(PruneError::DeferredDecision);
        }
        if self.unresolved {
            return Err(PruneError::DiagnosticResidual);
        }
        if self.has_call {
            states = states.opaque_callback();
        }
        if self.captures_reference {
            states = states.expose_reference();
            if self.has_call {
                states = states.set_known_nil(false);
            }
        }
        Ok(states)
    }
}

impl HirVisitor<'_> for ExprEffects<'_> {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        self.has_call |= matches!(stmt, HirStmt::GlobalDecl(_));
    }

    fn visit_expr(&mut self, expr: &HirExpr) {
        match expr {
            HirExpr::GlobalRef(_)
            | HirExpr::TableAccess(_)
            | HirExpr::Unary(_)
            | HirExpr::Binary(_)
            | HirExpr::Call(_) => self.has_call = true,
            HirExpr::Decision(_) => self.decision = true,
            HirExpr::Unresolved(_) => self.unresolved = true,
            _ => {}
        }
    }

    fn visit_capture(&mut self, capture: &crate::hir::HirCapture) {
        if !self.captures_reference && capture.mode == crate::hir::HirCaptureMode::ByReference {
            self.captures_reference = capture_binding_may_reference_home(
                capture.binding,
                self.candidate_home,
                self.facts,
            );
        }
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.has_call |= matches!(lvalue, HirLValue::Global(_) | HirLValue::TableAccess(_));
    }

    fn visit_call(&mut self, _call: &crate::hir::common::HirCallExpr) {
        self.has_call = true;
    }
}

fn capture_binding_may_reference_home(
    binding: crate::hir::HirBinding,
    candidate_home: HomeSlotKey,
    facts: &ProtoPromotionFacts,
) -> bool {
    use crate::hir::HirBinding;
    let homes = match binding {
        HirBinding::Local(local) => facts.possible_local_home_slots(local),
        HirBinding::Param(param) => facts.possible_param_home_slots(param),
        HirBinding::Temp(temp) => facts.possible_temp_home_slots(temp),
        HirBinding::Upvalue(_) => return false,
    };
    homes
        .as_ref()
        .is_none_or(|homes| homes.contains(&candidate_home))
}

fn apply_if_plan(if_stmt: &mut HirIf, redundant: &BTreeSet<StmtPath>) {
    remove_planned_stmts(
        &mut if_stmt.then_block,
        &mut vec![PathComponent::Then],
        redundant,
    );
    if let Some(else_block) = &mut if_stmt.else_block {
        remove_planned_stmts(else_block, &mut vec![PathComponent::Else], redundant);
    }
}

fn debug_identity_homes(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
) -> Option<BTreeSet<HomeSlotKey>> {
    let locals = (0..proto.local_count)
        .map(LocalId)
        .filter(|local| {
            matches!(proto.local_debug_hints.get(local.index()), Some(Some(_)))
                || matches!(proto.local_debug_scopes.get(local.index()), Some(Some(_)))
        })
        .map(|local| facts.possible_local_home_slots(local));
    let params = proto
        .params
        .iter()
        .zip(&proto.param_debug_hints)
        .filter_map(|(param, hint)| {
            hint.as_ref()
                .map(|_| facts.possible_param_home_slots(*param))
        });
    let temps = (0..proto.temp_count)
        .map(TempId)
        .filter(|temp| {
            matches!(proto.temp_debug_locals.get(temp.index()), Some(Some(_)))
                || matches!(proto.temp_debug_scopes.get(temp.index()), Some(Some(_)))
        })
        .map(|temp| facts.possible_temp_home_slots(temp));
    // home 映射在本 pass 内不变；未知来源保护任意 home，明确 home-free 则不贡献条目。
    locals
        .chain(params)
        .chain(temps)
        .try_fold(BTreeSet::new(), |mut homes, possible| {
            homes.extend(possible?.iter().copied());
            Some(homes)
        })
}

/// 循环入口的 nil 声明与 phi 共用同一物理帧；稀疏 phi 省略的槽由 VM 入口清零。
/// 显式 LOADNIL 只接回连续且尚无 debug/capture 身份的组。恢复完整低槽区后，
/// 每个 exact-home 写仍落在原 cell；高槽 CALL/SETLIST 才能验证自己的源码声明前缀。
pub(in crate::hir::simplify) fn restore_entry_frame(
    proto: &mut HirProto,
    facts: &mut ProtoPromotionFacts,
) -> bool {
    let base = proto.params.len() + usize::from(proto.vararg_param_local.is_some());
    let mut seeds = BTreeMap::new();
    let mut homes = BTreeSet::new();
    let mut prefix_len = 0;
    for stmt in &proto.body.stmts {
        let HirStmt::Assign(assign) = stmt else {
            break;
        };
        if assign.values.tail.is_some()
            || assign.values.fixed.len() != assign.targets.len()
            || assign.initializer_merge_transaction.is_some()
            || assign.generic_for_initializer_producer.is_some()
            || assign.generic_for_dispatch_release.is_some()
            || assign.method_rewrite_transaction.is_some()
        {
            break;
        }
        let mut additions = Vec::new();
        for (target, value) in assign.targets.iter().zip(&assign.values.fixed) {
            let HirLValue::Temp(temp) = target else {
                break;
            };
            let Some(home) = facts.trusted_temp_home_slot(*temp) else {
                break;
            };
            if home.slot() < base || home != HomeSlotKey::new(home.slot(), 0) {
                break;
            }
            match value {
                HirExpr::Nil if !homes.contains(&home) => {}
                HirExpr::TempRef(source) if seeds.get(source) == Some(&home) => {}
                _ => break,
            }
            additions.push((*temp, home));
        }
        if additions.len() != assign.targets.len() {
            break;
        }
        for (temp, home) in additions {
            seeds.insert(temp, home);
            homes.insert(home);
        }
        prefix_len += 1;
    }
    if homes.len() < 2 || !seeds.keys().any(|temp| facts.is_loop_carrier_temp(*temp)) {
        return false;
    }
    let end = homes.last().unwrap().slot() + 1;
    // 只省略未读槽的 Entry phi 才能用 VM 入口 nil 填补空缺；显式初始化必须连续。
    if end >= crate::SOURCE_LOCAL_LIMIT
        || (end - base != homes.len()
            && !seeds.keys().all(|temp| facts.is_entry_nil_phi_temp(*temp)))
    {
        return false;
    }
    // 既有 debug/closure cell 不能按物理槽合并。当前只承接未声明的匿名入口区。
    if (0..proto.local_count).any(|index| {
        facts
            .trusted_local_home_slot(LocalId(index))
            .is_some_and(|home| (base..end).contains(&home.slot()))
    }) {
        return false;
    }
    let mut members = BTreeMap::new();
    for index in 0..proto.temp_count {
        let temp = TempId(index);
        let Some(home) = facts.trusted_temp_home_slot(temp) else {
            continue;
        };
        if !(base..end).contains(&home.slot()) {
            continue;
        }
        if !facts
            .complete_temp_definition_write_homes(temp)
            .iter()
            .copied()
            .eq([home])
        {
            continue;
        }
        if home != HomeSlotKey::new(home.slot(), 0)
            || proto
                .temp_debug_locals
                .get(index)
                .is_some_and(Option::is_some)
            || proto
                .temp_debug_scopes
                .get(index)
                .is_some_and(Option::is_some)
        {
            return false;
        }
        members.insert(temp, home);
    }
    if !seeds.keys().all(|temp| members.contains_key(temp)) {
        return false;
    }
    let mut captures =
        super::CaptureCollector::new(crate::hir::common::HirCaptureMode::ByReference);
    visit::visit_stmts(&proto.body.stmts, &mut captures);
    if captures
        .bindings
        .temps
        .iter()
        .any(|temp| members.contains_key(temp))
    {
        return false;
    }
    let start = proto.local_count;
    let locals: Vec<_> = (0..end - base)
        .map(|offset| LocalId(start + offset))
        .collect();
    let mapping: BTreeMap<_, _> = members
        .iter()
        .map(|(&temp, home)| (temp, locals[home.slot() - base]))
        .collect();
    proto.local_count += locals.len();
    proto.local_debug_hints.resize(proto.local_count, None);
    proto.local_debug_scopes.resize(proto.local_count, None);
    for (offset, &local) in locals.iter().enumerate() {
        facts.record_local_home_slot(local, HomeSlotKey::new(base + offset, 0));
        proto.inline_dispositions.preserve_local(
            local,
            crate::hir::common::HirInlineRetentionReason::PhysicalFramePrefix,
        );
    }
    for (&temp, &local) in &mapping {
        facts.record_entry_nil_phi_promotion(temp, local);
        facts.record_temp_to_local_merge(temp, local);
        if proto.physical_root_temps.remove(&temp) {
            proto.physical_root_locals.insert(local);
        }
        proto.inline_dispositions.promote_temp_to_local(temp, local);
    }
    super::rewrite::bindings(proto, &mapping);
    let values = vec![HirExpr::Nil; locals.len()].into();
    proto.body.stmts.splice(
        ..prefix_len,
        [HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: locals,
            values,
            initializer_merge_transaction: None,
        }))],
    );
    true
}
