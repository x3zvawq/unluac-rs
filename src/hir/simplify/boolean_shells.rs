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
    definite_counts: BTreeMap<HomeSlotKey, usize>,
    possible_counts: BTreeMap<HomeSlotKey, usize>,
}

impl VisibleHomeUseCounts {
    fn collect_from_proto(
        proto: &HirProto,
        param_homes: &BTreeMap<ParamId, HomeSlotKey>,
        local_homes: &BTreeMap<LocalId, HomeSlotKey>,
        possible_param_homes: &BTreeMap<ParamId, BTreeSet<HomeSlotKey>>,
        possible_local_homes: &BTreeMap<LocalId, BTreeSet<HomeSlotKey>>,
    ) -> Self {
        let mut collector = VisibleHomeUseCollector {
            uses: Self {
                definite_counts: BTreeMap::new(),
                possible_counts: BTreeMap::new(),
            },
            param_homes,
            local_homes,
            possible_param_homes,
            possible_local_homes,
        };
        visit_proto(proto, &mut collector);
        collector.uses
    }

    fn collect_from_stmt(
        stmt: &HirStmt,
        param_homes: &BTreeMap<ParamId, HomeSlotKey>,
        local_homes: &BTreeMap<LocalId, HomeSlotKey>,
        possible_param_homes: &BTreeMap<ParamId, BTreeSet<HomeSlotKey>>,
        possible_local_homes: &BTreeMap<LocalId, BTreeSet<HomeSlotKey>>,
    ) -> Self {
        let mut collector = VisibleHomeUseCollector {
            uses: Self {
                definite_counts: BTreeMap::new(),
                possible_counts: BTreeMap::new(),
            },
            param_homes,
            local_homes,
            possible_param_homes,
            possible_local_homes,
        };
        visit_stmts(std::slice::from_ref(stmt), &mut collector);
        collector.uses
    }
}

struct VisibleHomeUseCollector<'a> {
    uses: VisibleHomeUseCounts,
    param_homes: &'a BTreeMap<ParamId, HomeSlotKey>,
    local_homes: &'a BTreeMap<LocalId, HomeSlotKey>,
    possible_param_homes: &'a BTreeMap<ParamId, BTreeSet<HomeSlotKey>>,
    possible_local_homes: &'a BTreeMap<LocalId, BTreeSet<HomeSlotKey>>,
}

#[derive(Default)]
struct ReferenceCapturedHomes {
    definite: BTreeSet<HomeSlotKey>,
    possible: BTreeSet<HomeSlotKey>,
}

struct ToBeClosedHomes<'a> {
    definite: BTreeSet<HomeSlotKey>,
    unresolved_slots: BTreeSet<usize>,
    promotion_facts: &'a ProtoPromotionFacts,
}

impl HirVisitor for ToBeClosedHomes<'_> {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        if let HirStmt::ToBeClosed(to_be_closed) = stmt {
            let (trusted, possible) = match &to_be_closed.value {
                HirExpr::ParamRef(param) => (
                    self.promotion_facts.trusted_param_home_slot(*param),
                    self.promotion_facts.possible_param_home_slots(*param),
                ),
                HirExpr::LocalRef(local) => (
                    self.promotion_facts.trusted_local_home_slot(*local),
                    self.promotion_facts.possible_local_home_slots(*local),
                ),
                HirExpr::TempRef(temp) => (
                    self.promotion_facts.trusted_temp_home_slot(*temp),
                    self.promotion_facts.possible_temp_home_slots(*temp),
                ),
                _ => (None, None),
            };
            let possible_home = possible.and_then(|homes| {
                let mut matching = homes
                    .into_iter()
                    .filter(|home| home.slot() == to_be_closed.reg_index);
                let home = matching.next()?;
                matching.next().is_none().then_some(home)
            });
            if let Some(home) = trusted
                .filter(|home| home.slot() == to_be_closed.reg_index)
                .or(possible_home)
            {
                self.definite.insert(home);
            } else {
                self.unresolved_slots.insert(to_be_closed.reg_index);
            }
        }
    }
}

impl HirVisitor for VisibleHomeUseCollector<'_> {
    fn visit_expr(&mut self, expr: &HirExpr) {
        let (definite, possible) = match expr {
            HirExpr::ParamRef(param) => (
                self.param_homes.get(param).copied(),
                self.possible_param_homes.get(param),
            ),
            HirExpr::LocalRef(local) => (
                self.local_homes.get(local).copied(),
                self.possible_local_homes.get(local),
            ),
            _ => return,
        };
        if let Some(home) = definite {
            *self.uses.definite_counts.entry(home).or_default() += 1;
            return;
        }
        let Some(homes) = possible else {
            unreachable!("visible binding home provenance must be completed during fact collection")
        };
        for home in homes {
            *self.uses.possible_counts.entry(*home).or_default() += 1;
        }
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
    possible_temp_homes: BTreeMap<TempId, BTreeSet<HomeSlotKey>>,
    param_homes: BTreeMap<ParamId, HomeSlotKey>,
    trusted_local_homes: BTreeMap<LocalId, HomeSlotKey>,
    possible_param_homes: BTreeMap<ParamId, BTreeSet<HomeSlotKey>>,
    possible_local_homes: BTreeMap<LocalId, BTreeSet<HomeSlotKey>>,
    visible_home_uses: VisibleHomeUseCounts,
    reference_captured_homes: ReferenceCapturedHomes,
    to_be_closed_homes: BTreeSet<HomeSlotKey>,
    unresolved_to_be_closed_slots: BTreeSet<usize>,
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
                CaptureRelation::None => {}
                CaptureRelation::Possible => {
                    possibly_reference_captured_locals.insert(*local);
                }
                CaptureRelation::Definite => {
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
        let possible_param_homes = proto
            .params
            .iter()
            .copied()
            .map(|param| {
                (
                    param,
                    complete_possible_home_slots(
                        promotion_facts.possible_param_home_slots(param),
                        promotion_facts,
                    ),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let possible_local_homes = proto
            .locals
            .iter()
            .copied()
            .map(|local| {
                (
                    local,
                    complete_possible_home_slots(
                        promotion_facts.possible_local_home_slots(local),
                        promotion_facts,
                    ),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let visible_home_uses = VisibleHomeUseCounts::collect_from_proto(
            proto,
            &param_homes,
            &trusted_local_homes,
            &possible_param_homes,
            &possible_local_homes,
        );
        let mut to_be_closed_homes = ToBeClosedHomes {
            definite: BTreeSet::new(),
            unresolved_slots: BTreeSet::new(),
            promotion_facts,
        };
        visit_proto(proto, &mut to_be_closed_homes);
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
            possible_temp_homes: proto
                .temps
                .iter()
                .copied()
                .map(|temp| {
                    (
                        temp,
                        complete_possible_home_slots(
                            promotion_facts.possible_temp_home_slots(temp),
                            promotion_facts,
                        ),
                    )
                })
                .collect(),
            param_homes,
            trusted_local_homes,
            possible_param_homes,
            possible_local_homes,
            visible_home_uses,
            reference_captured_homes: reference_capture_home_slots(
                &reference_captured,
                promotion_facts,
            ),
            to_be_closed_homes: to_be_closed_homes.definite,
            unresolved_to_be_closed_slots: to_be_closed_homes.unresolved_slots,
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
                // 候选拒绝[SemanticBarrier:DebugScope]：debug temp 是 IR 已保留的源码 binding；删除其分支写入会抹掉该 source identity。
                if self.debug_temps.contains(temp) {
                    return false;
                }
                if !written_value_is_gc_inert {
                    // 候选拒绝[SemanticBarrier:Lifetime]：把对象引用写入 raw home 会建立新的 VM root；删除死写可能让该对象在后续显式 GC 中提前终结。
                    return false;
                }
                let homes = self
                    .possible_temp_homes
                    .get(temp)
                    .expect("every proto temp must have a complete possible-home set");
                for home in homes {
                    if self.reference_captured_homes.definite.contains(home) {
                        // 候选拒绝[SemanticBarrier:Capture]：同 home 的 ByReference closure 会观察这次布尔写；删除后它继续读取旧值。
                        return false;
                    }
                    if self.reference_captured_homes.possible.contains(home) {
                        // 候选拒绝[SemanticBarrier:Capture]：possible-home 与 ByReference capture 相交时，closure 可能观察这次布尔写；`complete_possible_capture_homes_prove_only_disjointness` 覆盖相交/异槽边界。
                        return false;
                    }
                    if self.to_be_closed_homes.contains(home) {
                        // 候选拒绝[SemanticBarrier:Lifetime]：`TBC t0; shell-write t1; Close r0` 中 t0/t1 同 home 时，Close 读取 shell 新值；删除写入会改为关闭旧 resource（`tbc_protection_is_scoped_to_exact_home_epoch`）。
                        return false;
                    }
                    if self.unresolved_to_be_closed_slots.contains(&home.slot()) {
                        // 候选拒绝[SemanticBarrier:Lifetime]：未解析 TBC 与 candidate 共用 raw slot 时可能处于同一 close epoch，删除写入会让 Close 改关旧 resource；精确异 epoch 由 `tbc_protection_is_scoped_to_exact_home_epoch` 放行。
                        return false;
                    }
                    if !use_is_internal_only(
                        &self.visible_home_uses.definite_counts,
                        &internal_home_uses.definite_counts,
                        *home,
                    ) {
                        // 候选拒绝[SemanticBarrier:ValueFlow]：shell 外仍通过同一 trusted home 的 param/local 读取布尔写；仅检查 target TempId 会漏掉该观察者。
                        return false;
                    }
                    if !use_is_internal_only(
                        &self.visible_home_uses.possible_counts,
                        &internal_home_uses.possible_counts,
                        *home,
                    ) {
                        // 候选拒绝[SemanticBarrier:ValueFlow]：外部读取的 possible-home 与 candidate 相交时可能观察布尔写；`overlapping_merged_local_read_keeps_the_raw_home_write` 是最小反例。
                        return false;
                    }
                    match old_values.home(*home) {
                        OldValueClass::GcInert => {
                            // 候选接受：所有 reaching path 上该 raw home 的旧值均为 nil/primitive；布尔新值也不承载 GC root。
                        }
                        OldValueClass::Unknown => {
                            // 候选拒绝[SemanticBarrier:Lifetime]：`regress_342_boolean_shell_local_gc_lifetime` 命中该 raw-home 路径；删除覆盖写会让未分类的旧对象跨显式 GC 继续存活。
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
                // 候选拒绝[SemanticBarrier:DebugScope]：retain-debug local 是 IR 已保留的源码 binding；删除显式分支写入会抹掉该 source identity。
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
                    // 候选拒绝[SemanticBarrier:Capture]：candidate local 与 ByReference capture 的 possible-home 相交时，closure 可能观察这次布尔写；相邻 nil 只证明旧值，不能消除该观察者。
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
                    OldValueClass::Unknown => {
                        // 候选拒绝[SemanticBarrier:Lifetime]：未分类旧值可能是 `regress_342_boolean_shell_local_gc_lifetime` 同类可终结对象；删除覆盖写会延长其 root 生命周期。
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

#[derive(Clone, Copy)]
enum CaptureRelation {
    None,
    Possible,
    Definite,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum OldValueClass {
    GcInert,
    MayCarryResource,
    Unknown,
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
            .unwrap_or(OldValueClass::Unknown)
    }

    fn home(&self, home: HomeSlotKey) -> OldValueClass {
        self.homes
            .get(&home)
            .copied()
            .unwrap_or(OldValueClass::Unknown)
    }
}

fn reference_capture_home_slots(
    captured: &super::mention::ReferenceCapturedBindings,
    facts: &ProtoPromotionFacts,
) -> ReferenceCapturedHomes {
    let mut homes = ReferenceCapturedHomes::default();
    for param in &captured.params {
        record_reference_capture_homes(
            &mut homes,
            facts.trusted_param_home_slot(*param),
            complete_possible_home_slots(facts.possible_param_home_slots(*param), facts),
        );
    }
    for local in &captured.locals {
        record_reference_capture_homes(
            &mut homes,
            facts.trusted_local_home_slot(*local),
            complete_possible_home_slots(facts.possible_local_home_slots(*local), facts),
        );
    }
    for temp in &captured.temps {
        record_reference_capture_homes(
            &mut homes,
            facts.trusted_temp_home_slot(*temp),
            complete_possible_home_slots(facts.possible_temp_home_slots(*temp), facts),
        );
    }
    homes
}

fn record_reference_capture_homes(
    homes: &mut ReferenceCapturedHomes,
    trusted: Option<HomeSlotKey>,
    possible: BTreeSet<HomeSlotKey>,
) {
    if let Some(home) = trusted {
        homes.definite.insert(home);
    } else {
        homes.possible.extend(possible);
    }
}

fn local_reference_capture_relation(
    local: LocalId,
    captured: &super::mention::ReferenceCapturedBindings,
    facts: &ProtoPromotionFacts,
) -> CaptureRelation {
    let candidate_home = facts.trusted_local_home_slot(local);
    let candidate_homes =
        complete_possible_home_slots(facts.possible_local_home_slots(local), facts);
    let mut possible = false;
    for captured_local in &captured.locals {
        if *captured_local == local {
            return CaptureRelation::Definite;
        }
        match capture_home_relation(
            candidate_home,
            &candidate_homes,
            facts.trusted_local_home_slot(*captured_local),
            &complete_possible_home_slots(facts.possible_local_home_slots(*captured_local), facts),
        ) {
            CaptureRelation::None => {}
            CaptureRelation::Possible => possible = true,
            CaptureRelation::Definite => return CaptureRelation::Definite,
        }
    }
    for captured_param in &captured.params {
        match capture_home_relation(
            candidate_home,
            &candidate_homes,
            facts.trusted_param_home_slot(*captured_param),
            &complete_possible_home_slots(facts.possible_param_home_slots(*captured_param), facts),
        ) {
            CaptureRelation::None => {}
            CaptureRelation::Possible => possible = true,
            CaptureRelation::Definite => return CaptureRelation::Definite,
        }
    }
    for captured_temp in &captured.temps {
        match capture_home_relation(
            candidate_home,
            &candidate_homes,
            facts.trusted_temp_home_slot(*captured_temp),
            &complete_possible_home_slots(facts.possible_temp_home_slots(*captured_temp), facts),
        ) {
            CaptureRelation::None => {}
            CaptureRelation::Possible => possible = true,
            CaptureRelation::Definite => return CaptureRelation::Definite,
        }
    }
    if possible {
        CaptureRelation::Possible
    } else {
        CaptureRelation::None
    }
}

fn capture_home_relation(
    left: Option<HomeSlotKey>,
    left_possible: &BTreeSet<HomeSlotKey>,
    right: Option<HomeSlotKey>,
    right_possible: &BTreeSet<HomeSlotKey>,
) -> CaptureRelation {
    match (left, right) {
        (Some(left), Some(right)) => {
            return if left == right {
                CaptureRelation::Definite
            } else {
                CaptureRelation::None
            };
        }
        (Some(left), None) => {
            return if right_possible.contains(&left) {
                CaptureRelation::Possible
            } else {
                CaptureRelation::None
            };
        }
        (None, Some(right)) => {
            return if left_possible.contains(&right) {
                CaptureRelation::Possible
            } else {
                CaptureRelation::None
            };
        }
        (None, None) => {}
    }
    if left_possible.is_empty()
        || right_possible.is_empty()
        || left_possible.is_disjoint(right_possible)
    {
        CaptureRelation::None
    } else {
        CaptureRelation::Possible
    }
}

pub(super) fn complete_possible_home_slots(
    possible: Option<BTreeSet<HomeSlotKey>>,
    facts: &ProtoPromotionFacts,
) -> BTreeSet<HomeSlotKey> {
    // Unknown is still a physical binding, so the slot/epoch universe is its complete may-alias
    // set. An empty universe can only describe explicitly home-free HIR, which is represented by
    // `Some(empty)` before this helper is called.
    possible.unwrap_or_else(|| {
        assert!(
            !facts.physical_home_universe().is_empty(),
            "unknown physical binding requires a non-empty physical-home universe"
        );
        facts.physical_home_universe().clone()
    })
}

fn possible_home_relation(
    left: Option<HomeSlotKey>,
    left_possible: Option<&BTreeSet<HomeSlotKey>>,
    right: Option<HomeSlotKey>,
    right_possible: Option<&BTreeSet<HomeSlotKey>>,
) -> BindingRelation {
    let left_complete = left
        .map(|home| BTreeSet::from([home]))
        .or_else(|| left_possible.cloned());
    let right_complete = right
        .map(|home| BTreeSet::from([home]))
        .or_else(|| right_possible.cloned());
    if matches!(
        (&left_complete, &right_complete),
        (Some(left), Some(right)) if left.len() == 1 && left == right
    ) {
        return BindingRelation::Definite;
    }
    match (left, right) {
        (Some(_), Some(_)) => return home_relation(left, right),
        (Some(left), None) => {
            return match right_possible {
                Some(right) if !right.contains(&left) => BindingRelation::None,
                Some(_) | None => BindingRelation::Possible,
            };
        }
        (None, Some(right)) => {
            return match left_possible {
                Some(left) if !left.contains(&right) => BindingRelation::None,
                Some(_) | None => BindingRelation::Possible,
            };
        }
        (None, None) => {}
    }
    if left_possible.is_some_and(BTreeSet::is_empty)
        || right_possible.is_some_and(BTreeSet::is_empty)
        || matches!((left_possible, right_possible), (Some(left), Some(right)) if left.is_disjoint(right))
    {
        BindingRelation::None
    } else {
        BindingRelation::Possible
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
        // 分析停用[LayerBoundary]：需要 reaching old-value 的候选只由前置 DeadShellPlan
        // 事务提交；普通 rewrite 仅拥有相邻 nil local 与明确 home-free temp。
        if shell_requires_old_value_plan(stmt, facts, adjacent_nil_local) {
            return true;
        }
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

fn shell_requires_old_value_plan(
    stmt: &HirStmt,
    facts: &BooleanShellFacts,
    adjacent_nil_local: Option<LocalId>,
) -> bool {
    let HirStmt::If(if_stmt) = stmt else {
        return false;
    };
    let Some(else_block) = &if_stmt.else_block else {
        return false;
    };
    let Some((then_target, _)) = single_fixed_assign_pattern(&if_stmt.then_block) else {
        return false;
    };
    let Some((else_target, _)) = single_fixed_assign_pattern(else_block) else {
        return false;
    };

    [then_target, else_target]
        .into_iter()
        .any(|target| match target {
            HirLValue::Local(local) => adjacent_nil_local != Some(*local),
            HirLValue::Temp(temp) => facts
                .possible_temp_homes
                .get(temp)
                .is_none_or(|homes| !homes.is_empty()),
            HirLValue::Param(_)
            | HirLValue::Upvalue(_)
            | HirLValue::Global(_)
            | HirLValue::TableAccess(_) => false,
        })
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
        &facts.possible_param_homes,
        &facts.possible_local_homes,
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
    // 候选拒绝[PolicyBoundary]：项目在 permissive 输出中保留 Unresolved 诊断，不能随
    // 死布尔壳静默删除失败证据。
    if !safety.is_discard_safe_without_residual(&if_stmt.cond) {
        return false;
    }

    // 候选拒绝[SemanticBarrier:EvalCount]：死 binding 的 `t=f()` 仍必须调用一次 `f()`，不能随布尔壳一起丢弃。
    // 候选拒绝[PolicyBoundary]：任一 arm 的 Unresolved 都是 permissive 输出保留的失败证据。
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

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use crate::decompile::DecompileDialect;
    use crate::hir::common::{
        HirAssign, HirBlock, HirCapture, HirCaptureMode, HirClosureExpr, HirExpr, HirGoto, HirIf,
        HirLValue, HirLabel, HirLabelId, HirLocalDecl, HirProto, HirProtoRef, HirStmt,
        HirTableConstructor, HirToBeClosed, HirUnresolvedExpr, HirValuePack, LocalId, TempId,
    };
    use crate::hir::expr_safety::HirExprSafety;
    use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

    use super::{
        BindingUseCounts, BooleanShellFacts, CaptureRelation, DeadShellOldValueFacts,
        OldValueClass, ReferenceCapturedHomes, VisibleHomeUseCounts,
        local_reference_capture_relation, reference_capture_home_slots,
        remove_boolean_materialization_shells_in_proto, shell_requires_old_value_plan,
    };
    use crate::hir::simplify::mention::ReferenceCapturedBindings;
    use crate::transformer::InstrRef;

    #[test]
    fn unrelated_residual_does_not_disable_old_value_proof() {
        let candidate = LocalId(0);
        let mut proto = empty_test_proto();
        proto.locals = vec![candidate];
        proto.local_debug_hints = vec![None];
        proto.local_debug_scopes = vec![None];
        proto.body.stmts = vec![
            local_decl(candidate, HirExpr::Nil),
            HirStmt::If(Box::new(HirIf {
                cond: HirExpr::Unresolved(Box::new(HirUnresolvedExpr {
                    summary: "unrelated test residual".to_owned(),
                })),
                then_block: HirBlock::default(),
                else_block: None,
            })),
            boolean_shell(HirLValue::Local(candidate)),
        ];

        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_local(candidate);
        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(proto.body.stmts.len(), 2);
        assert!(matches!(proto.body.stmts[1], HirStmt::If(_)));
    }

    #[test]
    fn tbc_protection_is_scoped_to_exact_home_epoch() {
        let temp = TempId(0);
        let closed_home = HomeSlotKey::new(0, 0);
        let reused_home = HomeSlotKey::new(0, 1);
        let mut facts = BooleanShellFacts {
            uses: BindingUseCounts::default(),
            debug_temps: BTreeSet::new(),
            debug_locals: BTreeSet::new(),
            physical_root_locals: BTreeSet::new(),
            possible_temp_homes: BTreeMap::from([(temp, BTreeSet::from([reused_home]))]),
            param_homes: BTreeMap::new(),
            trusted_local_homes: BTreeMap::new(),
            possible_param_homes: BTreeMap::new(),
            possible_local_homes: BTreeMap::new(),
            visible_home_uses: VisibleHomeUseCounts {
                definite_counts: BTreeMap::new(),
                possible_counts: BTreeMap::new(),
            },
            reference_captured_homes: ReferenceCapturedHomes::default(),
            to_be_closed_homes: BTreeSet::from([closed_home]),
            unresolved_to_be_closed_slots: BTreeSet::new(),
            reference_captured_locals: BTreeSet::new(),
            possibly_reference_captured_locals: BTreeSet::new(),
        };
        let old_values = DeadShellOldValueFacts {
            locals: BTreeMap::new(),
            homes: BTreeMap::from([(reused_home, OldValueClass::GcInert)]),
        };
        let internal_uses = BindingUseCounts::default();
        let internal_home_uses = VisibleHomeUseCounts {
            definite_counts: BTreeMap::new(),
            possible_counts: BTreeMap::new(),
        };

        assert!(facts.target_write_is_unobservable(
            &HirLValue::Temp(temp),
            true,
            &internal_uses,
            &internal_home_uses,
            None,
            &old_values,
        ));

        facts.to_be_closed_homes.insert(reused_home);
        assert!(!facts.target_write_is_unobservable(
            &HirLValue::Temp(temp),
            true,
            &internal_uses,
            &internal_home_uses,
            None,
            &old_values,
        ));
    }

    #[test]
    fn complete_possible_tbc_homes_are_narrowed_by_the_instruction_slot() {
        let resource = LocalId(0);
        let old_home = HomeSlotKey::new(0, 0);
        let tbc_home = HomeSlotKey::new(1, 0);
        let mut proto = empty_test_proto();
        proto.locals = vec![resource];
        proto.local_debug_hints = vec![None];
        proto.local_debug_scopes = vec![None];
        proto.body.stmts = vec![HirStmt::ToBeClosed(Box::new(HirToBeClosed {
            origin: InstrRef(0),
            reg_index: tbc_home.slot(),
            value: HirExpr::LocalRef(resource),
        }))];
        let mut facts = ProtoPromotionFacts::default();
        facts.record_local_home_slot(resource, old_home);
        facts.record_local_home_merge(resource, Some(BTreeSet::from([tbc_home])));

        let shell_facts = BooleanShellFacts::collect(&proto, &facts);

        assert_eq!(shell_facts.to_be_closed_homes, BTreeSet::from([tbc_home]));
        assert!(shell_facts.unresolved_to_be_closed_slots.is_empty());
    }

    #[test]
    fn home_free_local_write_does_not_obscure_another_local_old_value() {
        let candidate = LocalId(0);
        let unrelated = LocalId(1);
        let mut proto = empty_test_proto();
        proto.locals = vec![candidate, unrelated];
        proto.local_debug_hints = vec![None, None];
        proto.local_debug_scopes = vec![None, None];
        proto.body.stmts = vec![
            local_decl(candidate, HirExpr::Nil),
            local_decl(
                unrelated,
                HirExpr::TableConstructor(Box::<HirTableConstructor>::default()),
            ),
            boolean_shell(HirLValue::Local(candidate)),
        ];
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_local(candidate);
        facts.record_home_free_local(unrelated);

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(proto.body.stmts.len(), 2);
    }

    #[test]
    fn complete_disjoint_merged_local_write_does_not_obscure_old_value() {
        let candidate = LocalId(0);
        let unrelated = LocalId(1);
        let candidate_home = HomeSlotKey::new(2, 0);
        let mut proto = empty_test_proto();
        proto.locals = vec![candidate, unrelated];
        proto.local_debug_hints = vec![None, None];
        proto.local_debug_scopes = vec![None, None];
        proto.body.stmts = vec![
            local_decl(candidate, HirExpr::Nil),
            local_decl(
                unrelated,
                HirExpr::TableConstructor(Box::<HirTableConstructor>::default()),
            ),
            boolean_shell(HirLValue::Local(candidate)),
        ];
        let mut facts = ProtoPromotionFacts::default();
        facts.record_local_home_slot(candidate, candidate_home);
        facts.record_local_home_slot(unrelated, HomeSlotKey::new(0, 0));
        facts.record_local_home_merge(unrelated, Some(BTreeSet::from([HomeSlotKey::new(1, 0)])));

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(proto.body.stmts.len(), 2);
    }

    #[test]
    fn home_free_local_read_does_not_obscure_a_raw_home() {
        let observer = LocalId(0);
        let target = TempId(0);
        let target_home = HomeSlotKey::new(0, 0);
        let mut proto = empty_test_proto();
        proto.locals = vec![observer];
        proto.local_debug_hints = vec![None];
        proto.local_debug_scopes = vec![None];
        proto.temps = vec![target];
        proto.temp_debug_locals = vec![None];
        proto.temp_debug_scopes = vec![None];
        proto.body.stmts = vec![
            assign_temp(target, HirExpr::Nil),
            local_decl(
                observer,
                HirExpr::TableConstructor(Box::<HirTableConstructor>::default()),
            ),
            HirStmt::If(Box::new(HirIf {
                cond: HirExpr::LocalRef(observer),
                then_block: HirBlock::default(),
                else_block: None,
            })),
            boolean_shell(HirLValue::Temp(target)),
        ];
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_local(observer);
        facts.record_temp_home_slot_for_test(target, target_home);

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(proto.body.stmts.len(), 3);
    }

    #[test]
    fn complete_disjoint_merged_local_read_does_not_obscure_a_raw_home() {
        let observer = LocalId(0);
        let target = TempId(0);
        let observer_home = HomeSlotKey::new(0, 0);
        let merged_observer_home = HomeSlotKey::new(1, 0);
        let target_home = HomeSlotKey::new(2, 0);
        let mut proto = raw_home_shell_with_external_local_read(observer, target);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_local_home_slot(observer, observer_home);
        facts.record_local_home_merge(observer, Some(BTreeSet::from([merged_observer_home])));
        facts.record_temp_home_slot_for_test(target, target_home);

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(proto.body.stmts.len(), 3);
    }

    #[test]
    fn merged_temp_shell_requires_gc_inert_old_values_in_every_possible_home() {
        let target = TempId(0);
        let first_seed = TempId(1);
        let second_seed = TempId(2);
        let first_home = HomeSlotKey::new(0, 0);
        let second_home = HomeSlotKey::new(1, 0);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(target, first_home);
        facts.record_temp_home_merge(target, Some(BTreeSet::from([second_home])));
        facts.record_temp_home_slot_for_test(first_seed, first_home);
        facts.record_temp_home_slot_for_test(second_seed, second_home);

        let mut safe_proto = merged_temp_shell_proto(target, first_seed, second_seed, HirExpr::Nil);
        assert!(remove_boolean_materialization_shells_in_proto(
            &mut safe_proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(safe_proto.body.stmts.len(), 2);

        let mut resource_proto = merged_temp_shell_proto(
            target,
            first_seed,
            second_seed,
            HirExpr::TableConstructor(Box::<HirTableConstructor>::default()),
        );
        assert!(remove_boolean_materialization_shells_in_proto(
            &mut resource_proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(resource_proto.body.stmts.len(), 3);
        assert!(matches!(resource_proto.body.stmts[2], HirStmt::Assign(_)));
    }

    #[test]
    fn unknown_temp_home_uses_the_single_home_universe() {
        let target = TempId(0);
        let universe_witness = TempId(1);
        let home = HomeSlotKey::new(0, 0);
        let mut proto = empty_test_proto();
        proto.temps = vec![target, universe_witness];
        proto.temp_debug_locals = vec![None, None];
        proto.temp_debug_scopes = vec![None, None];
        proto.body.stmts = vec![
            assign_temp(target, HirExpr::Nil),
            boolean_shell(HirLValue::Temp(target)),
        ];
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(universe_witness, home);

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(proto.body.stmts.len(), 1);
        assert!(matches!(proto.body.stmts[0], HirStmt::Assign(_)));
    }

    #[test]
    #[should_panic(
        expected = "unknown physical binding requires a non-empty physical-home universe"
    )]
    fn unknown_temp_without_a_physical_home_universe_is_an_invalid_fact_set() {
        let target = TempId(0);
        let mut proto = empty_test_proto();
        proto.temps = vec![target];
        proto.temp_debug_locals = vec![None];
        proto.temp_debug_scopes = vec![None];
        proto.body.stmts = vec![boolean_shell(HirLValue::Temp(target))];

        let _ = BooleanShellFacts::collect(&proto, &ProtoPromotionFacts::default());
    }

    #[test]
    fn ordinary_rewrite_only_owns_nil_adjacent_or_home_free_targets() {
        let local = LocalId(0);
        let unknown_temp = TempId(0);
        let home_free_temp = TempId(1);
        let local_shell = boolean_shell(HirLValue::Local(local));
        let unknown_temp_shell = boolean_shell(HirLValue::Temp(unknown_temp));
        let home_free_temp_shell = boolean_shell(HirLValue::Temp(home_free_temp));
        let mut proto = empty_test_proto();
        proto.locals = vec![local];
        proto.local_debug_hints = vec![None];
        proto.local_debug_scopes = vec![None];
        let universe_witness = TempId(2);
        proto.temps = vec![unknown_temp, home_free_temp, universe_witness];
        proto.temp_debug_locals = vec![None, None, None];
        proto.temp_debug_scopes = vec![None, None, None];
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_home_free_local(local);
        promotion_facts.record_home_free_temp(home_free_temp);
        promotion_facts.record_temp_home_slot_for_test(universe_witness, HomeSlotKey::new(0, 0));
        let facts = BooleanShellFacts::collect(&proto, &promotion_facts);

        assert!(shell_requires_old_value_plan(&local_shell, &facts, None));
        assert!(!shell_requires_old_value_plan(
            &local_shell,
            &facts,
            Some(local),
        ));
        assert!(shell_requires_old_value_plan(
            &unknown_temp_shell,
            &facts,
            None,
        ));
        assert!(!shell_requires_old_value_plan(
            &home_free_temp_shell,
            &facts,
            None,
        ));
    }

    #[test]
    fn overlapping_merged_local_read_keeps_the_raw_home_write() {
        let observer = LocalId(0);
        let target = TempId(0);
        let observer_home = HomeSlotKey::new(0, 0);
        let target_home = HomeSlotKey::new(1, 0);
        let mut proto = raw_home_shell_with_external_local_read(observer, target);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_local_home_slot(observer, observer_home);
        facts.record_local_home_merge(observer, Some(BTreeSet::from([target_home])));
        facts.record_temp_home_slot_for_test(target, target_home);

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(proto.body.stmts.len(), 4);
        assert!(matches!(proto.body.stmts[3], HirStmt::Assign(_)));
    }

    #[test]
    fn home_free_capture_is_exact_by_local_identity() {
        let candidate = LocalId(0);
        let unrelated = LocalId(1);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_local(candidate);
        facts.record_home_free_local(unrelated);
        let mut captured = ReferenceCapturedBindings::default();
        captured.locals.insert(unrelated);

        assert_eq!(
            reference_capture_home_slots(&captured, &facts).definite,
            BTreeSet::new()
        );
        assert!(matches!(
            local_reference_capture_relation(candidate, &captured, &facts),
            CaptureRelation::None
        ));

        captured.locals.insert(candidate);
        assert!(matches!(
            local_reference_capture_relation(candidate, &captured, &facts),
            CaptureRelation::Definite
        ));
    }

    #[test]
    fn complete_possible_capture_homes_prove_only_disjointness() {
        let disjoint_candidate = LocalId(0);
        let overlapping_candidate = LocalId(1);
        let captured_local = LocalId(2);
        let captured_home = HomeSlotKey::new(0, 0);
        let merged_home = HomeSlotKey::new(1, 0);
        let disjoint_home = HomeSlotKey::new(2, 0);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_local_home_slot(disjoint_candidate, disjoint_home);
        facts.record_local_home_slot(overlapping_candidate, merged_home);
        facts.record_local_home_slot(captured_local, captured_home);
        facts.record_local_home_merge(captured_local, Some(BTreeSet::from([merged_home])));
        let mut captured = ReferenceCapturedBindings::default();
        captured.locals.insert(captured_local);

        let captured_homes = reference_capture_home_slots(&captured, &facts);
        assert!(captured_homes.definite.is_empty());
        assert_eq!(
            captured_homes.possible,
            BTreeSet::from([captured_home, merged_home])
        );
        assert!(matches!(
            local_reference_capture_relation(disjoint_candidate, &captured, &facts),
            CaptureRelation::None
        ));
        assert!(matches!(
            local_reference_capture_relation(overlapping_candidate, &captured, &facts),
            CaptureRelation::Possible
        ));
    }

    #[test]
    fn unknown_capture_uses_the_universe_for_home_free_and_physical_candidates() {
        let home_free_candidate = LocalId(0);
        let physical_candidate = LocalId(1);
        let unknown_capture = LocalId(2);
        let first_home = HomeSlotKey::new(0, 0);
        let second_home = HomeSlotKey::new(1, 0);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_local(home_free_candidate);
        facts.record_local_home_slot(physical_candidate, first_home);
        facts.record_temp_home_slot_for_test(TempId(0), second_home);
        let mut captured = ReferenceCapturedBindings::default();
        captured.locals.insert(unknown_capture);

        assert_eq!(
            reference_capture_home_slots(&captured, &facts).possible,
            BTreeSet::from([first_home, second_home])
        );
        assert!(matches!(
            local_reference_capture_relation(home_free_candidate, &captured, &facts),
            CaptureRelation::None
        ));
        assert!(matches!(
            local_reference_capture_relation(physical_candidate, &captured, &facts),
            CaptureRelation::Possible
        ));
    }

    #[test]
    fn unknown_capture_allows_only_the_home_free_shell_removal() {
        let candidate = LocalId(0);
        let captured = LocalId(1);
        let closure_holder = LocalId(2);
        let universe_witness = TempId(0);
        let first_home = HomeSlotKey::new(0, 0);
        let second_home = HomeSlotKey::new(1, 0);
        let mut proto = empty_test_proto();
        proto.locals = vec![candidate, captured, closure_holder];
        proto.local_debug_hints = vec![None, None, None];
        proto.local_debug_scopes = vec![None, None, None];
        proto.temps = vec![universe_witness];
        proto.temp_debug_locals = vec![None];
        proto.temp_debug_scopes = vec![None];
        proto.body.stmts = vec![
            local_decl(candidate, HirExpr::Nil),
            local_decl(
                closure_holder,
                HirExpr::Closure(Box::new(HirClosureExpr {
                    proto: HirProtoRef(1),
                    captures: vec![HirCapture {
                        mode: HirCaptureMode::ByReference,
                        value: HirExpr::LocalRef(captured),
                    }],
                })),
            ),
            boolean_shell(HirLValue::Local(candidate)),
        ];
        let mut home_free_facts = ProtoPromotionFacts::default();
        home_free_facts.record_home_free_local(candidate);
        home_free_facts.record_home_free_local(closure_holder);
        home_free_facts.record_temp_home_slot_for_test(universe_witness, second_home);
        let mut home_free_proto = proto.clone();

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut home_free_proto,
            &home_free_facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(home_free_proto.body.stmts.len(), 2);

        let mut physical_facts = home_free_facts;
        physical_facts.record_local_home_slot(candidate, first_home);
        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &physical_facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(proto.body.stmts.len(), 3);
        assert!(matches!(proto.body.stmts[2], HirStmt::Assign(_)));
    }

    #[test]
    fn unknown_visible_read_uses_the_universe_and_keeps_the_raw_home_write() {
        let observer = LocalId(0);
        let target = TempId(0);
        let target_home = HomeSlotKey::new(0, 0);
        let mut proto = raw_home_shell_with_external_local_read(observer, target);
        proto.body.stmts[1] = local_decl(observer, HirExpr::Boolean(true));
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(target, target_home);

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(proto.body.stmts.len(), 4);
        assert!(matches!(proto.body.stmts[3], HirStmt::Assign(_)));
    }

    #[test]
    fn unknown_multi_home_temp_requires_every_old_home_to_be_gc_inert() {
        let target = TempId(0);
        let first_seed = TempId(1);
        let second_seed = TempId(2);
        let first_home = HomeSlotKey::new(0, 0);
        let second_home = HomeSlotKey::new(1, 0);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(first_seed, first_home);
        facts.record_temp_home_slot_for_test(second_seed, second_home);

        let mut safe_proto = merged_temp_shell_proto(target, first_seed, second_seed, HirExpr::Nil);
        assert!(remove_boolean_materialization_shells_in_proto(
            &mut safe_proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(safe_proto.body.stmts.len(), 2);

        let mut resource_proto = merged_temp_shell_proto(
            target,
            first_seed,
            second_seed,
            HirExpr::TableConstructor(Box::<HirTableConstructor>::default()),
        );
        assert!(remove_boolean_materialization_shells_in_proto(
            &mut resource_proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(resource_proto.body.stmts.len(), 3);
        assert!(matches!(resource_proto.body.stmts[2], HirStmt::Assign(_)));
    }

    #[test]
    fn old_value_plan_follows_a_local_forward_goto() {
        let candidate = LocalId(0);
        let join = HirLabelId(0);
        let mut proto = empty_test_proto();
        proto.locals = vec![candidate];
        proto.local_debug_hints = vec![None];
        proto.local_debug_scopes = vec![None];
        proto.body.stmts = vec![
            local_decl(candidate, HirExpr::Nil),
            goto(join),
            assign_local(
                candidate,
                HirExpr::TableConstructor(Box::<HirTableConstructor>::default()),
            ),
            label(join),
            boolean_shell(HirLValue::Local(candidate)),
        ];
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_home_free_local(candidate);
        let shell_facts = BooleanShellFacts::collect(&proto, &promotion_facts);
        let plan = super::old_values::DeadShellPlan::collect(
            &proto,
            &shell_facts,
            &promotion_facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        );

        assert!(plan.apply(&mut proto.body));
        assert_eq!(proto.body.stmts.len(), 4);
        assert!(matches!(proto.body.stmts[3], HirStmt::Label(_)));
    }

    #[test]
    fn unstructured_sibling_does_not_disable_a_closed_old_value_region() {
        let candidate = LocalId(0);
        let flag = LocalId(1);
        let join = HirLabelId(0);
        let mut proto = empty_test_proto();
        proto.locals = vec![candidate, flag];
        proto.local_debug_hints = vec![None, None];
        proto.local_debug_scopes = vec![None, None];
        proto.body.stmts = vec![
            HirStmt::If(Box::new(HirIf {
                cond: HirExpr::LocalRef(flag),
                then_block: HirBlock {
                    stmts: vec![goto(join)],
                },
                else_block: None,
            })),
            HirStmt::Block(Box::new(HirBlock {
                stmts: vec![
                    local_decl(candidate, HirExpr::Nil),
                    boolean_shell(HirLValue::Local(candidate)),
                ],
            })),
            label(join),
        ];
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_home_free_local(candidate);
        promotion_facts.record_home_free_local(flag);
        let shell_facts = BooleanShellFacts::collect(&proto, &promotion_facts);
        let plan = super::old_values::DeadShellPlan::collect(
            &proto,
            &shell_facts,
            &promotion_facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        );

        assert!(plan.apply(&mut proto.body));
        let HirStmt::Block(closed) = &proto.body.stmts[1] else {
            panic!("independent region must remain a block");
        };
        assert_eq!(closed.stmts.len(), 1);
        assert!(matches!(closed.stmts[0], HirStmt::LocalDecl(_)));
    }

    #[test]
    fn old_value_plan_keeps_resource_backedge_reentry() {
        let candidate = LocalId(0);
        let head = HirLabelId(0);
        let mut proto = empty_test_proto();
        proto.locals = vec![candidate];
        proto.local_debug_hints = vec![None];
        proto.local_debug_scopes = vec![None];
        proto.body.stmts = vec![
            local_decl(candidate, HirExpr::Nil),
            label(head),
            boolean_shell(HirLValue::Local(candidate)),
            assign_local(
                candidate,
                HirExpr::TableConstructor(Box::<HirTableConstructor>::default()),
            ),
            goto(head),
        ];
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_home_free_local(candidate);
        let shell_facts = BooleanShellFacts::collect(&proto, &promotion_facts);
        let plan = super::old_values::DeadShellPlan::collect(
            &proto,
            &shell_facts,
            &promotion_facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        );

        assert!(!plan.apply(&mut proto.body));
        assert_eq!(proto.body.stmts.len(), 5);
        assert!(matches!(proto.body.stmts[2], HirStmt::If(_)));
    }

    #[test]
    fn old_value_plan_keeps_a_physical_root_local_write() {
        let candidate = LocalId(0);
        let mut proto = empty_test_proto();
        proto.locals = vec![candidate];
        proto.local_debug_hints = vec![None];
        proto.local_debug_scopes = vec![None];
        proto.physical_root_locals.insert(candidate);
        proto.body.stmts = vec![
            local_decl(candidate, HirExpr::Nil),
            boolean_shell(HirLValue::Local(candidate)),
        ];
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_local_home_slot(candidate, HomeSlotKey::new(0, 0));
        let shell_facts = BooleanShellFacts::collect(&proto, &promotion_facts);
        let plan = super::old_values::DeadShellPlan::collect(
            &proto,
            &shell_facts,
            &promotion_facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        );

        assert!(!plan.apply(&mut proto.body));
        assert!(matches!(proto.body.stmts[1], HirStmt::If(_)));
    }

    fn local_decl(local: LocalId, value: HirExpr) -> HirStmt {
        HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: vec![local],
            values: HirValuePack::fixed(vec![value]),
        }))
    }

    fn assign_temp(temp: TempId, value: HirExpr) -> HirStmt {
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(temp)],
            values: HirValuePack::fixed(vec![value]),
        }))
    }

    fn assign_local(local: LocalId, value: HirExpr) -> HirStmt {
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Local(local)],
            values: HirValuePack::fixed(vec![value]),
        }))
    }

    fn raw_home_shell_with_external_local_read(observer: LocalId, target: TempId) -> HirProto {
        let mut proto = empty_test_proto();
        proto.locals = vec![observer];
        proto.local_debug_hints = vec![None];
        proto.local_debug_scopes = vec![None];
        proto.temps = vec![target];
        proto.temp_debug_locals = vec![None];
        proto.temp_debug_scopes = vec![None];
        proto.body.stmts = vec![
            assign_temp(target, HirExpr::Nil),
            local_decl(
                observer,
                HirExpr::TableConstructor(Box::<HirTableConstructor>::default()),
            ),
            HirStmt::If(Box::new(HirIf {
                cond: HirExpr::LocalRef(observer),
                then_block: HirBlock::default(),
                else_block: None,
            })),
            boolean_shell(HirLValue::Temp(target)),
        ];
        proto
    }

    fn merged_temp_shell_proto(
        target: TempId,
        first_seed: TempId,
        second_seed: TempId,
        second_value: HirExpr,
    ) -> HirProto {
        let mut proto = empty_test_proto();
        proto.temps = vec![target, first_seed, second_seed];
        proto.temp_debug_locals = vec![None, None, None];
        proto.temp_debug_scopes = vec![None, None, None];
        proto.body.stmts = vec![
            assign_temp(first_seed, HirExpr::Nil),
            assign_temp(second_seed, second_value),
            boolean_shell(HirLValue::Temp(target)),
        ];
        proto
    }

    fn goto(target: HirLabelId) -> HirStmt {
        HirStmt::Goto(Box::new(HirGoto { target }))
    }

    fn label(id: HirLabelId) -> HirStmt {
        HirStmt::Label(Box::new(HirLabel {
            id,
            tbc_barriers: Vec::new(),
        }))
    }

    fn boolean_shell(target: HirLValue) -> HirStmt {
        let arm = |value| HirBlock {
            stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                targets: vec![target.clone()],
                values: HirValuePack::fixed(vec![HirExpr::Boolean(value)]),
            }))],
        };
        HirStmt::If(Box::new(HirIf {
            cond: HirExpr::Boolean(true),
            then_block: arm(true),
            else_block: Some(arm(false)),
        }))
    }

    fn empty_test_proto() -> HirProto {
        HirProto {
            id: HirProtoRef(0),
            source: None,
            line_range: crate::parser::ProtoLineRange {
                defined_start: 0,
                defined_end: 0,
            },
            signature: crate::parser::ProtoSignature {
                num_params: 0,
                is_vararg: false,
                has_vararg_param_reg: false,
                named_vararg_table: false,
                legacy_arg_slot: false,
            },
            params: Vec::new(),
            param_debug_hints: Vec::new(),
            locals: Vec::new(),
            local_debug_hints: Vec::new(),
            local_debug_scopes: Vec::new(),
            debug_scopes: Vec::new(),
            physical_root_temps: BTreeSet::new(),
            physical_root_locals: BTreeSet::new(),
            upvalues: Vec::new(),
            mutable_upvalues: BTreeSet::new(),
            upvalue_debug_hints: Vec::new(),
            temps: Vec::new(),
            temp_debug_locals: Vec::new(),
            temp_debug_scopes: Vec::new(),
            body: HirBlock::default(),
            children: Vec::new(),
            failure: None,
            detached_children: Vec::new(),
        }
    }
}
