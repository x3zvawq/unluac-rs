//! 这个文件负责清理已经失去职责的值物化分支壳。
//!
//! 它依赖更前面的 HIR 决策已经把“真正承载语义的 merge 值”恢复成直接表达式；
//! 走到这里时，某些 `if cond then t=true else t=false end` 只剩下机械性的值物化。
//! 这里专门删除这一类纯值壳，或者把它们折回单条赋值，避免把真正承担控制语义的
//! `if/else` 结构误删掉。删除死写前还要证明目标没有外部读取、capture、debug identity
//! 或物理根职责；把相邻空声明吸收到初始化器时，则必须保留条件求值期间的词法作用域。
//! 条件是否可删除、arm 结果是否承载 GC root 统一消费入口按目标方言构造的表达式安全上下文。
//!
//! 它不会越权去重新判断 branch/loop 是否应该结构化，也不会替前层补决策。
//! 这里唯一关心的是：当前 `if` 是否已经退化成“无副作用的布尔值搬运壳”。table
//! 左值的地址在分支条件之后已经确定，不能把它挪到合并后赋值的 RHS 之前重新求值。
//!
//! 例子：
//! - 输入：`if cond then t = true else t = false end`
//! - 输出：`t = cond or false`
//! - 如果 `t` 后面已经没人再读，且 `cond/true/false` 都无副作用，则整段壳会被删除

mod old_values;

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirAssign, HirBlock, HirExpr, HirLValue, HirLocalDecl, HirLogicalExpr, HirProto, HirStmt,
    HirUnaryExpr, HirUnaryOpKind, HirValuePack, LocalId, ParamId, TempId,
};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

use super::expr_facts::expr_is_boolean_valued;
use super::local_shapes::empty_single_local_decl_binding;
use super::mention::{expr_mentions_local, stmts_reference_captured_bindings};
use super::visit::{HirVisitor, visit_proto, visit_stmts};
use super::walk::{HirRewritePass, rewrite_proto};

pub(super) fn remove_boolean_materialization_shells_in_proto(
    proto: &mut HirProto,
    promotion_facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
) -> bool {
    let facts = BooleanShellFacts::collect(proto, promotion_facts);
    let old_value_plan = old_values::DeadShellPlan::collect(proto, &facts, promotion_facts, safety);
    let old_value_changed = old_value_plan.apply(&mut proto.body);
    let mut pass = BooleanShellPass {
        facts: &facts,
        safety,
    };
    old_value_changed | rewrite_proto(proto, &mut pass)
}

struct BooleanShellPass<'a> {
    facts: &'a BooleanShellFacts,
    safety: HirExprSafety,
}

impl HirRewritePass for BooleanShellPass<'_> {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        let dead_changed =
            remove_dead_materialization_shells_from_block(block, self.facts, self.safety);
        let collapse_changed =
            collapse_live_boolean_materialization_shells_in_block(block, self.facts);
        dead_changed || collapse_changed
    }
}

#[derive(Default)]
struct BindingUseCounts {
    temps: BTreeMap<TempId, usize>,
    locals: BTreeMap<LocalId, usize>,
}

#[derive(Default)]
struct VisibleHomeUseCounts {
    counts: BTreeMap<HomeSlotKey, usize>,
    proof_complete: bool,
}

impl VisibleHomeUseCounts {
    fn collect_from_proto(
        proto: &HirProto,
        param_homes: &BTreeMap<ParamId, HomeSlotKey>,
        local_homes: &BTreeMap<LocalId, HomeSlotKey>,
    ) -> Self {
        let mut collector = VisibleHomeUseCollector {
            uses: Self {
                counts: BTreeMap::new(),
                proof_complete: true,
            },
            param_homes,
            local_homes,
        };
        visit_proto(proto, &mut collector);
        collector.uses
    }

    fn collect_from_stmt(
        stmt: &HirStmt,
        param_homes: &BTreeMap<ParamId, HomeSlotKey>,
        local_homes: &BTreeMap<LocalId, HomeSlotKey>,
    ) -> Self {
        let mut collector = VisibleHomeUseCollector {
            uses: Self {
                counts: BTreeMap::new(),
                proof_complete: true,
            },
            param_homes,
            local_homes,
        };
        visit_stmts(std::slice::from_ref(stmt), &mut collector);
        collector.uses
    }
}

struct VisibleHomeUseCollector<'a> {
    uses: VisibleHomeUseCounts,
    param_homes: &'a BTreeMap<ParamId, HomeSlotKey>,
    local_homes: &'a BTreeMap<LocalId, HomeSlotKey>,
}

#[derive(Default)]
struct ToBeClosedSlots(BTreeSet<usize>);

impl HirVisitor for ToBeClosedSlots {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        if let HirStmt::ToBeClosed(to_be_closed) = stmt {
            self.0.insert(to_be_closed.reg_index);
        }
    }
}

impl HirVisitor for VisibleHomeUseCollector<'_> {
    fn visit_expr(&mut self, expr: &HirExpr) {
        let home = match expr {
            HirExpr::ParamRef(param) => self.param_homes.get(param).copied(),
            HirExpr::LocalRef(local) => self.local_homes.get(local).copied(),
            _ => return,
        };
        let Some(home) = home else {
            self.uses.proof_complete = false;
            return;
        };
        *self.uses.counts.entry(home).or_default() += 1;
    }
}

impl BindingUseCounts {
    fn collect_from_proto(proto: &HirProto) -> Self {
        let mut counts = Self::default();
        visit_proto(proto, &mut counts);
        counts
    }

    fn collect_from_stmt(stmt: &HirStmt) -> Self {
        let mut counts = Self::default();
        visit_stmts(std::slice::from_ref(stmt), &mut counts);
        counts
    }
}

impl HirVisitor for BindingUseCounts {
    fn visit_expr(&mut self, expr: &HirExpr) {
        match expr {
            HirExpr::TempRef(temp) => *self.temps.entry(*temp).or_default() += 1,
            HirExpr::LocalRef(local) => *self.locals.entry(*local).or_default() += 1,
            _ => {}
        }
    }
}

struct BooleanShellFacts {
    uses: BindingUseCounts,
    debug_temps: BTreeSet<TempId>,
    debug_locals: BTreeSet<LocalId>,
    physical_root_locals: BTreeSet<LocalId>,
    temp_homes: BTreeMap<TempId, HomeSlotKey>,
    param_homes: BTreeMap<ParamId, HomeSlotKey>,
    trusted_local_homes: BTreeMap<LocalId, HomeSlotKey>,
    visible_home_uses: VisibleHomeUseCounts,
    reference_captured_homes: Option<BTreeSet<HomeSlotKey>>,
    to_be_closed_slots: BTreeSet<usize>,
    reference_captured_locals: BTreeSet<LocalId>,
    possibly_reference_captured_locals: BTreeSet<LocalId>,
}

impl BooleanShellFacts {
    fn collect(proto: &HirProto, promotion_facts: &ProtoPromotionFacts) -> Self {
        let reference_captured = stmts_reference_captured_bindings(&proto.body.stmts);
        let mut reference_captured_locals = BTreeSet::new();
        let mut possibly_reference_captured_locals = BTreeSet::new();
        for local in &proto.locals {
            match local_reference_capture_relation(*local, &reference_captured, promotion_facts) {
                BindingRelation::None => {}
                BindingRelation::Possible => {
                    possibly_reference_captured_locals.insert(*local);
                }
                BindingRelation::Definite => {
                    reference_captured_locals.insert(*local);
                }
            }
        }
        let param_homes = proto
            .params
            .iter()
            .filter_map(|param| {
                promotion_facts
                    .trusted_param_home_slot(*param)
                    .map(|home| (*param, home))
            })
            .collect::<BTreeMap<_, _>>();
        let trusted_local_homes = proto
            .locals
            .iter()
            .filter_map(|local| {
                promotion_facts
                    .trusted_local_home_slot(*local)
                    .map(|home| (*local, home))
            })
            .collect::<BTreeMap<_, _>>();
        let visible_home_uses =
            VisibleHomeUseCounts::collect_from_proto(proto, &param_homes, &trusted_local_homes);
        let mut to_be_closed_slots = ToBeClosedSlots::default();
        visit_proto(proto, &mut to_be_closed_slots);
        Self {
            uses: BindingUseCounts::collect_from_proto(proto),
            debug_temps: proto
                .temps
                .iter()
                .zip(&proto.temp_debug_locals)
                .filter_map(|(temp, hint)| hint.as_ref().map(|_| *temp))
                .collect(),
            debug_locals: proto
                .locals
                .iter()
                .zip(&proto.local_debug_hints)
                .filter_map(|(local, hint)| hint.as_ref().map(|_| *local))
                .collect(),
            physical_root_locals: proto.physical_root_locals.clone(),
            temp_homes: proto
                .temps
                .iter()
                .filter_map(|temp| promotion_facts.home_slot(*temp).map(|home| (*temp, home)))
                .collect(),
            param_homes,
            trusted_local_homes,
            visible_home_uses,
            reference_captured_homes: reference_capture_home_slots(
                &reference_captured,
                promotion_facts,
            ),
            to_be_closed_slots: to_be_closed_slots.0,
            reference_captured_locals,
            possibly_reference_captured_locals,
        }
    }

    fn target_write_is_unobservable(
        &self,
        target: &HirLValue,
        written_value_is_gc_inert: bool,
        internal_uses: &BindingUseCounts,
        internal_home_uses: &VisibleHomeUseCounts,
        adjacent_nil_local: Option<LocalId>,
        old_values: &DeadShellOldValueFacts,
    ) -> bool {
        match target {
            HirLValue::Temp(temp) => {
                // 候选拒绝[PolicyBoundary]：debug temp 是源码 binding；删除其分支写入会抹掉保留的 source identity。
                if self.debug_temps.contains(temp) {
                    return false;
                }
                if let Some(home) = self.temp_homes.get(temp) {
                    if !written_value_is_gc_inert {
                        // 候选拒绝[SemanticBarrier:Lifetime]：把对象引用写入 raw home 会建立新的 VM root；删除死写可能让该对象在后续显式 GC 中提前终结。
                        return false;
                    }
                    let Some(captured_homes) = &self.reference_captured_homes else {
                        // 候选拒绝[ProofIncomplete]：存在缺 trusted home 的 ByReference capture，尚不能排除 closure 通过 candidate home 观察布尔写。
                        return false;
                    };
                    if captured_homes.contains(home) {
                        // 候选拒绝[SemanticBarrier:Capture]：同 home 的 ByReference closure 会观察这次布尔写；删除后它继续读取旧值。
                        return false;
                    }
                    if self.to_be_closed_slots.contains(&home.slot()) {
                        // 候选拒绝[ProofIncomplete]：同物理槽承载过 TBC resource；当前尚缺 shell 点位与 Close epoch 的精确作用域关系，不能证明删除写入不改变 close owner。
                        return false;
                    }
                    if !self.visible_home_uses.proof_complete {
                        // 候选拒绝[ProofIncomplete]：proto 内存在缺 trusted home 的可见 binding 读取，尚不能排除它观察 candidate home。
                        return false;
                    }
                    if !use_is_internal_only(
                        &self.visible_home_uses.counts,
                        &internal_home_uses.counts,
                        *home,
                    ) {
                        // 候选拒绝[SemanticBarrier:ValueFlow]：shell 外仍通过同一物理 home 的 param/local 读取布尔写；仅检查 target TempId 会漏掉该观察者。
                        return false;
                    }
                    match old_values.home(*home) {
                        OldValueClass::GcInert => {
                            // 候选接受：所有 reaching path 上该 raw home 的旧值均为 nil/primitive；布尔新值也不承载 GC root。
                        }
                        OldValueClass::ProofIncomplete => {
                            // 候选拒绝[ProofIncomplete]：raw-home temp 的入口或某个同槽写入端缺少精确资源事实；尚不能证明删除覆盖写不延长旧 root 生命周期。
                            return false;
                        }
                        OldValueClass::MayCarryResource => {
                            // 候选拒绝[SemanticBarrier:Lifetime]：regress_342 local-gc 中 reaching old value 是可终结的 call result；删除覆盖写会让它跨显式 GC 继续存活。
                            return false;
                        }
                    }
                }
                // 候选拒绝[SemanticBarrier:ValueFlow]：shell 外仍读取或 capture 该 temp 时，删除写入会改变后续值。
                use_is_internal_only(&self.uses.temps, &internal_uses.temps, *temp)
            }
            HirLValue::Local(local) => {
                if !written_value_is_gc_inert {
                    // 候选拒绝[SemanticBarrier:Lifetime]：把对象引用写入 local 会建立新的可见 root；删除死写可能让该对象在后续显式 GC 中提前终结。
                    return false;
                }
                // 候选拒绝[PolicyBoundary]：retain-debug local 的显式分支写入属于项目选择保留的源码身份。
                if self.debug_locals.contains(local) {
                    return false;
                }
                // 候选拒绝[SemanticBarrier:Lifetime]：物理根 local 的写入决定可观察的 GC 存活区间，不能按普通死值删除。
                if self.physical_root_locals.contains(local) {
                    return false;
                }
                if self.reference_captured_locals.contains(local) {
                    // 候选拒绝[SemanticBarrier:Capture]：`local f=function() return x end; <boolean shell x>; return f()` 中 closure 会观察被删掉的布尔写；同 trusted home 的 reference capture 等价。
                    return false;
                }
                if self.possibly_reference_captured_locals.contains(local) {
                    // 候选拒绝[ProofIncomplete]：reference capture 的 binding 或候选 local 缺 trusted home，尚不能排除 closure 通过同一物理 cell 观察布尔写；相邻 nil 只证明旧值，不能证明写入无人观察。
                    return false;
                }
                if adjacent_nil_local == Some(*local) {
                    // 候选接受：紧邻空声明已把旧值确定为 nil；域外无读取/capture，删除布尔写不会改变值流或 GC root 生命周期。
                    return use_is_internal_only(&self.uses.locals, &internal_uses.locals, *local);
                }
                match old_values.local(*local) {
                    OldValueClass::GcInert => {
                        // 候选接受：所有 reaching path 都证明旧值为 nil/primitive；域外无读取/capture，删除布尔写不会改变值流或 GC root 生命周期。
                        use_is_internal_only(&self.uses.locals, &internal_uses.locals, *local)
                    }
                    OldValueClass::ProofIncomplete => {
                        // 候选拒绝[ProofIncomplete]：入口旧值或 possible same-home 写入的某个合流端仍缺精确资源事实；尚不能证明旧值恒为 GC-inert。
                        false
                    }
                    OldValueClass::MayCarryResource => {
                        // 候选拒绝[SemanticBarrier:Lifetime]：regress_342 local-gc 的 reaching old value 是可终结对象，删除覆盖写会推迟显式 GC 可观察的释放。
                        false
                    }
                }
            }
            HirLValue::Param(_) => {
                // 候选拒绝[SemanticBarrier:Lifetime]：regress_342 中参数写入会释放任意可回收实参；即使没有值读取，删除写入仍会推迟 GC。
                false
            }
            // 候选拒绝[SemanticBarrier:ValueFlow]：upvalue 写入可被共享该 cell 的 closure 观察，不能由当前 proto 的读取数证明为死写。
            HirLValue::Upvalue(_) => false,
            // 候选拒绝[SemanticBarrier:Metamethod]：global 写入会更新外部环境，并可能触发环境表的 `__newindex`。
            HirLValue::Global(_) => false,
            // 候选拒绝[SemanticBarrier:Metamethod]：table 写入会更新外部对象，并可能触发目标表的 `__newindex`。
            HirLValue::TableAccess(_) => false,
        }
    }
}

#[derive(Clone, Copy)]
enum BindingRelation {
    None,
    Possible,
    Definite,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum OldValueClass {
    GcInert,
    MayCarryResource,
    ProofIncomplete,
}

#[derive(Default)]
struct DeadShellOldValueFacts {
    locals: BTreeMap<LocalId, OldValueClass>,
    homes: BTreeMap<HomeSlotKey, OldValueClass>,
}

impl DeadShellOldValueFacts {
    fn local(&self, local: LocalId) -> OldValueClass {
        self.locals
            .get(&local)
            .copied()
            .unwrap_or(OldValueClass::ProofIncomplete)
    }

    fn home(&self, home: HomeSlotKey) -> OldValueClass {
        self.homes
            .get(&home)
            .copied()
            .unwrap_or(OldValueClass::ProofIncomplete)
    }
}

fn reference_capture_home_slots(
    captured: &super::mention::ReferenceCapturedBindings,
    facts: &ProtoPromotionFacts,
) -> Option<BTreeSet<HomeSlotKey>> {
    captured
        .params
        .iter()
        .map(|param| facts.trusted_param_home_slot(*param))
        .chain(
            captured
                .locals
                .iter()
                .map(|local| facts.trusted_local_home_slot(*local)),
        )
        .chain(
            captured
                .temps
                .iter()
                .map(|temp| facts.trusted_temp_home_slot(*temp)),
        )
        .collect()
}

fn local_reference_capture_relation(
    local: LocalId,
    captured: &super::mention::ReferenceCapturedBindings,
    facts: &ProtoPromotionFacts,
) -> BindingRelation {
    let candidate_home = facts.trusted_local_home_slot(local);
    let mut possible = false;
    for captured_local in &captured.locals {
        if *captured_local == local {
            return BindingRelation::Definite;
        }
        match home_relation(
            candidate_home,
            facts.trusted_local_home_slot(*captured_local),
        ) {
            BindingRelation::None => {}
            BindingRelation::Possible => possible = true,
            BindingRelation::Definite => return BindingRelation::Definite,
        }
    }
    for captured_param in &captured.params {
        match home_relation(
            candidate_home,
            facts.trusted_param_home_slot(*captured_param),
        ) {
            BindingRelation::None => {}
            BindingRelation::Possible => possible = true,
            BindingRelation::Definite => return BindingRelation::Definite,
        }
    }
    for captured_temp in &captured.temps {
        match home_relation(candidate_home, facts.trusted_temp_home_slot(*captured_temp)) {
            BindingRelation::None => {}
            BindingRelation::Possible => possible = true,
            BindingRelation::Definite => return BindingRelation::Definite,
        }
    }
    if possible {
        BindingRelation::Possible
    } else {
        BindingRelation::None
    }
}

fn home_relation(left: Option<HomeSlotKey>, right: Option<HomeSlotKey>) -> BindingRelation {
    match (left, right) {
        (Some(left), Some(right)) if left == right => BindingRelation::Definite,
        (Some(_), Some(_)) => BindingRelation::None,
        (None, _) | (_, None) => BindingRelation::Possible,
    }
}

fn use_is_internal_only<K: Ord + Copy>(
    total: &BTreeMap<K, usize>,
    internal: &BTreeMap<K, usize>,
    binding: K,
) -> bool {
    total.get(&binding).copied().unwrap_or(0) == internal.get(&binding).copied().unwrap_or(0)
}

fn remove_dead_materialization_shells_from_block(
    block: &mut HirBlock,
    facts: &BooleanShellFacts,
    safety: HirExprSafety,
) -> bool {
    let no_old_value_facts = DeadShellOldValueFacts::default();
    let old_len = block.stmts.len();
    let adjacent_nil_locals = block
        .stmts
        .iter()
        .enumerate()
        .map(|(index, _)| {
            index
                .checked_sub(1)
                .and_then(|previous| block.stmts.get(previous))
                .and_then(empty_single_local_decl_binding)
        })
        .collect::<Vec<_>>();
    let mut index = 0;
    block.stmts.retain(|stmt| {
        let adjacent_nil_local = adjacent_nil_locals[index];
        index += 1;
        !removable_dead_materialization_shell(
            stmt,
            facts,
            adjacent_nil_local,
            &no_old_value_facts,
            safety,
        )
    });
    block.stmts.len() != old_len
}

fn collapse_live_boolean_materialization_shells_in_block(
    block: &mut HirBlock,
    facts: &BooleanShellFacts,
) -> bool {
    let mut index = 0;
    let mut changed = false;
    while index < block.stmts.len() {
        let Some((target, value)) =
            collapsible_live_boolean_materialization_shell(&block.stmts[index])
        else {
            index += 1;
            continue;
        };

        if index > 0
            && let HirLValue::Local(local) = &target
            && empty_single_local_decl_binding(&block.stmts[index - 1]) == Some(*local)
            && declaration_can_absorb_boolean_shell(*local, &value, facts)
        {
            block.stmts[index - 1] = HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: vec![*local],
                values: HirValuePack::fixed(vec![value]),
            }));
            block.stmts.remove(index);
            changed = true;
            index = index.saturating_sub(1);
            continue;
        }

        block.stmts[index] = HirStmt::Assign(Box::new(HirAssign {
            targets: vec![target],
            values: HirValuePack::fixed(vec![value]),
        }));
        changed = true;
        index += 1;
    }

    changed
}

fn declaration_can_absorb_boolean_shell(
    local: LocalId,
    value: &HirExpr,
    facts: &BooleanShellFacts,
) -> bool {
    // 候选拒绝[SemanticBarrier:Scope]：regress_342 retain-debug 证明条件中的调用能观察到原声明；合并会把 debug 作用域起点后移。
    if facts.debug_locals.contains(&local) {
        return false;
    }
    // 候选拒绝[SemanticBarrier:Scope]：regress_342 stripped 证明初始化器中的同名引用会改绑到外层 local，而不是读取已经声明的当前 local。
    !expr_mentions_local(value, local)
}

fn collapsible_live_boolean_materialization_shell(stmt: &HirStmt) -> Option<(HirLValue, HirExpr)> {
    let HirStmt::If(if_stmt) = stmt else {
        return None;
    };
    let Some(else_block) = &if_stmt.else_block else {
        return None;
    };

    let (then_target, then_value) = single_fixed_assign_pattern(&if_stmt.then_block)?;
    let (else_target, else_value) = single_fixed_assign_pattern(else_block)?;
    let target = canonical_shared_target(then_target, else_target)?;
    // 候选拒绝[SemanticBarrier:EvalOrder]：regress_249 中 table 左值会把地址求值移出已选分支，条件改写的 holder 因而指向不同 table。
    if !target_address_can_follow_condition_eval(&target) {
        return None;
    }

    match (then_value, else_value) {
        (HirExpr::Boolean(true), HirExpr::Boolean(false)) => {
            Some((target, booleanized_truthiness_expr(if_stmt.cond.clone())))
        }
        (HirExpr::Boolean(false), HirExpr::Boolean(true)) => Some((
            target,
            HirExpr::Unary(Box::new(HirUnaryExpr {
                op: HirUnaryOpKind::Not,
                expr: if_stmt.cond.clone(),
            })),
        )),
        _ => None,
    }
}

fn canonical_shared_target(then_target: &HirLValue, else_target: &HirLValue) -> Option<HirLValue> {
    if then_target == else_target {
        return Some(then_target.clone());
    }
    // 候选拒绝[SemanticBarrier:ValueFlow]：same-home 不代表可见 binding 等价；`then local=true else param=false; return local,param` 若统一写 param 会改变 true 臂结果。
    None
}

fn removable_dead_materialization_shell(
    stmt: &HirStmt,
    facts: &BooleanShellFacts,
    adjacent_nil_local: Option<LocalId>,
    old_values: &DeadShellOldValueFacts,
    safety: HirExprSafety,
) -> bool {
    let HirStmt::If(if_stmt) = stmt else {
        return false;
    };
    let Some(else_block) = &if_stmt.else_block else {
        return false;
    };
    let Some((then_target, then_value)) = single_fixed_assign_pattern(&if_stmt.then_block) else {
        return false;
    };
    let Some((else_target, else_value)) = single_fixed_assign_pattern(else_block) else {
        return false;
    };
    let internal_uses = BindingUseCounts::collect_from_stmt(stmt);
    let internal_home_uses = VisibleHomeUseCounts::collect_from_stmt(
        stmt,
        &facts.param_homes,
        &facts.trusted_local_homes,
    );
    if !facts.target_write_is_unobservable(
        then_target,
        safety.result_is_gc_inert(then_value),
        &internal_uses,
        &internal_home_uses,
        adjacent_nil_local,
        old_values,
    ) || !facts.target_write_is_unobservable(
        else_target,
        safety.result_is_gc_inert(else_value),
        &internal_uses,
        &internal_home_uses,
        adjacent_nil_local,
        old_values,
    ) {
        return false;
    }
    // 候选拒绝[SemanticBarrier:EvalCount]：删除 `if f() then t=true else t=false end` 会漏掉仍需执行一次的 `f()`。
    // 候选拒绝[SemanticBarrier:Metamethod]：LuaJIT cdata 与 primitive 的 equality 可能调用 ctype `__eq`；删除布尔壳会漏掉这次调用（regress_391）。
    // 候选拒绝[LayerBoundary]：Unresolved 是 residual owner 的显式诊断，不能随死布尔壳静默删除。
    if !safety.is_discard_safe_without_residual(&if_stmt.cond) {
        return false;
    }

    // 候选拒绝[SemanticBarrier:EvalCount]：死 binding 的 `t=f()` 仍必须调用一次 `f()`，不能随布尔壳一起丢弃。
    // 候选拒绝[LayerBoundary]：任一 arm 的 Unresolved 必须继续交给 residual owner。
    safety.is_discard_safe_without_residual(then_value)
        && safety.is_discard_safe_without_residual(else_value)
}

fn single_fixed_assign_pattern(block: &HirBlock) -> Option<(&HirLValue, &HirExpr)> {
    let [HirStmt::Assign(assign)] = block.stmts.as_slice() else {
        return None;
    };
    let [target] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.fixed.as_slice() else {
        return None;
    };
    if assign.values.tail.is_some() {
        return None;
    }

    Some((target, value))
}

fn target_address_can_follow_condition_eval(target: &HirLValue) -> bool {
    matches!(
        target,
        HirLValue::Param(_)
            | HirLValue::Temp(_)
            | HirLValue::Local(_)
            | HirLValue::Upvalue(_)
            | HirLValue::Global(_)
    )
}

fn booleanized_truthiness_expr(cond: HirExpr) -> HirExpr {
    if expr_is_boolean_valued(&cond) {
        cond
    } else {
        HirExpr::LogicalOr(Box::new(HirLogicalExpr {
            lhs: HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
                lhs: cond,
                rhs: HirExpr::Boolean(true),
            })),
            rhs: HirExpr::Boolean(false),
        }))
    }
}
