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
    HirUnaryExpr, HirUnaryOpKind, HirValuePack, LocalId, TempId,
};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

use super::expr_facts::{expr_is_boolean_valued, expr_truthiness};
use super::local_shapes::empty_single_local_decl_binding;
use super::mention::expr_mentions_local;
use super::walk::{HirRewritePass, rewrite_proto};

pub(super) fn remove_boolean_materialization_shells_in_proto(
    proto: &mut HirProto,
    promotion_facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
) -> bool {
    let facts = BooleanShellFacts::collect(proto, promotion_facts);
    let old_value_plan = old_values::DeadShellPlan::collect(proto, &facts, promotion_facts, safety);
    let old_value_changed = old_value_plan.apply(&mut proto.body);
    let mut pass = BooleanShellPass { facts: &facts };
    old_value_changed | rewrite_proto(proto, &mut pass)
}

struct BooleanShellPass<'a> {
    facts: &'a BooleanShellFacts,
}

impl HirRewritePass for BooleanShellPass<'_> {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        collapse_live_boolean_materialization_shells_in_block(block, self.facts)
    }
}

struct BooleanShellFacts {
    debug_temps: BTreeSet<TempId>,
    debug_locals: BTreeSet<LocalId>,
    physical_root_locals: BTreeSet<LocalId>,
    possible_temp_homes: BTreeMap<TempId, BTreeSet<HomeSlotKey>>,
    possible_local_homes: BTreeMap<LocalId, BTreeSet<HomeSlotKey>>,
}

struct DeadWriteProof<'a> {
    live_after: &'a old_values::LiveBindingState,
    adjacent_nil_local: Option<LocalId>,
    old_values: &'a DeadShellOldValueFacts,
}

impl BooleanShellFacts {
    fn collect(proto: &HirProto, promotion_facts: &ProtoPromotionFacts) -> Self {
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
        Self {
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
            possible_local_homes,
        }
    }

    fn target_write_is_unobservable(
        &self,
        target: &HirLValue,
        written_value_is_gc_inert: bool,
        proof: &DeadWriteProof<'_>,
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
                    if proof.live_after.homes.contains(home) {
                        // 候选拒绝[SemanticBarrier:ValueFlow]：shell 外仍通过同一 trusted home 的 param/local 读取布尔写；仅检查 target TempId 会漏掉该观察者。
                        return false;
                    }
                    match proof.old_values.home(*home) {
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
                // 候选拒绝[SemanticBarrier:ValueFlow]：shell 后仍有路径读取该 temp 时，删除写入会改变后续值；CFG live-out 会排除只发生在 shell 前的读取，并合流循环回边。
                !proof.live_after.temps.contains(temp)
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
                let homes = self
                    .possible_local_homes
                    .get(local)
                    .expect("every proto local must have a complete possible-home set");
                for home in homes {
                    if proof.live_after.homes.contains(home) {
                        // 候选拒绝[SemanticBarrier:ValueFlow]：candidate local 的 possible-home 与后续 param/local 读取相交时，raw cell 上的布尔写仍可见；只查 LocalId 会漏掉合流后的别名。
                        return false;
                    }
                }
                if proof.adjacent_nil_local == Some(*local) {
                    // 候选接受：紧邻空声明已把旧值确定为 nil；域外无读取/capture，删除布尔写不会改变值流或 GC root 生命周期。
                    return !proof.live_after.locals.contains(local);
                }
                match proof.old_values.local(*local) {
                    OldValueClass::GcInert => {
                        // 候选接受：所有 reaching path 都证明旧值为 nil/primitive；域外无读取/capture，删除布尔写不会改变值流或 GC root 生命周期。
                        !proof.live_after.locals.contains(local)
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
    live_after: &old_values::ShellArmLiveOut,
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
    let truthiness = expr_truthiness(&if_stmt.cond, safety);
    let then_write_is_unobservable = truthiness == Some(false)
        || facts.target_write_is_unobservable(
            then_target,
            safety.result_is_gc_inert(then_value),
            &DeadWriteProof {
                live_after: &live_after.then_arm,
                adjacent_nil_local,
                old_values,
            },
        );
    let else_write_is_unobservable = truthiness == Some(true)
        || facts.target_write_is_unobservable(
            else_target,
            safety.result_is_gc_inert(else_value),
            &DeadWriteProof {
                live_after: &live_after.else_arm,
                adjacent_nil_local,
                old_values,
            },
        );
    if !then_write_is_unobservable || !else_write_is_unobservable {
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
    (truthiness == Some(false) || safety.is_discard_safe_without_residual(then_value))
        && (truthiness == Some(true) || safety.is_discard_safe_without_residual(else_value))
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
    use std::collections::BTreeSet;

    use crate::decompile::DecompileDialect;
    use crate::hir::common::{
        HirAssign, HirBlock, HirCallExpr, HirCallStmt, HirCapture, HirCaptureMode, HirClose,
        HirClosureExpr, HirExpr, HirGlobalRef, HirGoto, HirIf, HirLValue, HirLabel, HirLabelId,
        HirLocalDecl, HirProto, HirProtoRef, HirReturn, HirStmt, HirTableConstructor,
        HirToBeClosed, HirUnresolvedExpr, HirValuePack, LocalId, ParamId, TempId, UpvalueId,
    };
    use crate::hir::expr_safety::HirExprSafety;
    use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

    use super::{BooleanShellFacts, remove_boolean_materialization_shells_in_proto};
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
    fn local_shell_keeps_a_same_home_tbc_write() {
        let candidate = LocalId(0);
        let resource = TempId(0);
        let home = HomeSlotKey::new(0, 0);
        let mut proto = empty_test_proto();
        proto.locals = vec![candidate];
        proto.local_debug_hints = vec![None];
        proto.local_debug_scopes = vec![None];
        proto.temps = vec![resource];
        proto.temp_debug_locals = vec![None];
        proto.temp_debug_scopes = vec![None];
        proto.body.stmts = vec![
            assign_temp(
                resource,
                HirExpr::TableConstructor(Box::<HirTableConstructor>::default()),
            ),
            HirStmt::ToBeClosed(Box::new(HirToBeClosed {
                origin: InstrRef(0),
                reg_index: home.slot(),
                value: HirExpr::TempRef(resource),
            })),
            local_decl(candidate, HirExpr::Nil),
            boolean_shell(HirLValue::Local(candidate)),
        ];
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(resource, home);
        facts.record_local_home_slot(candidate, home);

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(proto.body.stmts.len(), 4);
        assert!(matches!(proto.body.stmts[3], HirStmt::Assign(_)));
    }

    #[test]
    fn dead_shell_ignores_an_unreachable_arm_target() {
        let candidate = LocalId(0);
        let parameter = ParamId(0);
        let mut proto = empty_test_proto();
        proto.params = vec![parameter];
        proto.param_debug_hints = vec![None];
        proto.locals = vec![candidate];
        proto.local_debug_hints = vec![None];
        proto.local_debug_scopes = vec![None];
        proto.body.stmts = vec![
            local_decl(candidate, HirExpr::Nil),
            HirStmt::If(Box::new(HirIf {
                cond: HirExpr::Boolean(true),
                then_block: HirBlock {
                    stmts: vec![assign_local(candidate, HirExpr::Boolean(true))],
                },
                else_block: Some(HirBlock {
                    stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Param(parameter)],
                        values: HirValuePack::fixed(vec![HirExpr::Boolean(false)]),
                    }))],
                }),
            })),
        ];
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_local(candidate);

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(proto.body.stmts.len(), 1);
        assert!(matches!(proto.body.stmts[0], HirStmt::LocalDecl(_)));
    }

    #[test]
    fn dead_shell_ignores_a_read_that_only_precedes_the_write() {
        let candidate = LocalId(0);
        let mut proto = empty_test_proto();
        proto.locals = vec![candidate];
        proto.local_debug_hints = vec![None];
        proto.local_debug_scopes = vec![None];
        proto.body.stmts = vec![
            local_decl(candidate, HirExpr::Nil),
            HirStmt::If(Box::new(HirIf {
                cond: HirExpr::LocalRef(candidate),
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
    fn return_does_not_make_a_lexical_suffix_read_live() {
        let candidate = LocalId(0);
        let mut proto = empty_test_proto();
        proto.locals = vec![candidate];
        proto.local_debug_hints = vec![None];
        proto.local_debug_scopes = vec![None];
        proto.body.stmts = vec![
            local_decl(candidate, HirExpr::Nil),
            boolean_shell(HirLValue::Local(candidate)),
            HirStmt::Return(Box::new(HirReturn {
                values: HirValuePack::default(),
            })),
            HirStmt::If(Box::new(HirIf {
                cond: HirExpr::LocalRef(candidate),
                then_block: HirBlock::default(),
                else_block: None,
            })),
        ];
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_local(candidate);

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(proto.body.stmts.len(), 3);
        assert!(matches!(proto.body.stmts[1], HirStmt::Return(_)));
        assert!(matches!(proto.body.stmts[2], HirStmt::If(_)));
    }

    #[test]
    fn later_exact_write_kills_the_shell_before_a_read() {
        let candidate = LocalId(0);
        let mut proto = empty_test_proto();
        proto.locals = vec![candidate];
        proto.local_debug_hints = vec![None];
        proto.local_debug_scopes = vec![None];
        proto.body.stmts = vec![
            local_decl(candidate, HirExpr::Nil),
            boolean_shell(HirLValue::Local(candidate)),
            assign_local(candidate, HirExpr::Nil),
            HirStmt::If(Box::new(HirIf {
                cond: HirExpr::LocalRef(candidate),
                then_block: HirBlock::default(),
                else_block: None,
            })),
        ];
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_local(candidate);

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(proto.body.stmts.len(), 3);
        assert!(matches!(proto.body.stmts[1], HirStmt::Assign(_)));
        assert!(matches!(proto.body.stmts[2], HirStmt::If(_)));
    }

    #[test]
    fn loop_backedge_keeps_a_shell_observed_before_the_next_iteration() {
        let candidate = LocalId(0);
        let flag = LocalId(1);
        let mut proto = empty_test_proto();
        proto.locals = vec![candidate, flag];
        proto.local_debug_hints = vec![None, None];
        proto.local_debug_scopes = vec![None, None];
        proto.body.stmts = vec![
            local_decl(candidate, HirExpr::Nil),
            HirStmt::While(Box::new(crate::hir::common::HirWhile {
                cond: HirExpr::LocalRef(flag),
                body: HirBlock {
                    stmts: vec![
                        HirStmt::If(Box::new(HirIf {
                            cond: HirExpr::LocalRef(candidate),
                            then_block: HirBlock::default(),
                            else_block: None,
                        })),
                        boolean_shell(HirLValue::Local(candidate)),
                    ],
                },
            })),
        ];
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_local(candidate);
        facts.record_home_free_local(flag);

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        let HirStmt::While(while_stmt) = &proto.body.stmts[1] else {
            panic!("loop must remain");
        };
        assert!(matches!(while_stmt.body.stmts[1], HirStmt::Assign(_)));
    }

    #[test]
    fn external_goto_entry_keeps_a_shell_observed_after_reentry() {
        let candidate = LocalId(0);
        let reentry = HirLabelId(0);
        let mut proto = empty_test_proto();
        proto.locals = vec![candidate];
        proto.local_debug_hints = vec![None];
        proto.local_debug_scopes = vec![None];
        proto.body.stmts = vec![
            local_decl(candidate, HirExpr::Nil),
            HirStmt::Block(Box::new(HirBlock {
                stmts: vec![
                    label(reentry),
                    HirStmt::If(Box::new(HirIf {
                        cond: HirExpr::LocalRef(candidate),
                        then_block: HirBlock::default(),
                        else_block: None,
                    })),
                    boolean_shell(HirLValue::Local(candidate)),
                ],
            })),
            goto(reentry),
        ];
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_local(candidate);

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        let HirStmt::Block(block) = &proto.body.stmts[1] else {
            panic!("nested entry block must remain");
        };
        assert!(matches!(block.stmts[2], HirStmt::Assign(_)));
    }

    #[test]
    fn unresolved_goto_uses_the_unknown_observer_sink() {
        let candidate = LocalId(0);
        let mut proto = empty_test_proto();
        proto.locals = vec![candidate];
        proto.local_debug_hints = vec![None];
        proto.local_debug_scopes = vec![None];
        proto.body.stmts = vec![
            local_decl(candidate, HirExpr::Nil),
            boolean_shell(HirLValue::Local(candidate)),
            goto(HirLabelId(99)),
        ];
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_local(candidate);

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(proto.body.stmts.len(), 3);
        assert!(matches!(proto.body.stmts[1], HirStmt::Assign(_)));
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
        assert!(matches!(proto.body.stmts[2], HirStmt::Assign(_)));
    }

    #[test]
    fn home_free_temp_shell_keeps_a_prior_reference_capture() {
        let candidate = TempId(0);
        let closure = LocalId(0);
        let mut proto = empty_test_proto();
        proto.temps = vec![candidate];
        proto.temp_debug_locals = vec![None];
        proto.temp_debug_scopes = vec![None];
        proto.locals = vec![closure];
        proto.local_debug_hints = vec![None];
        proto.local_debug_scopes = vec![None];
        proto.body.stmts = vec![
            assign_temp(candidate, HirExpr::Nil),
            local_decl(
                closure,
                HirExpr::Closure(Box::new(HirClosureExpr {
                    proto: HirProtoRef(1),
                    captures: vec![HirCapture {
                        mode: HirCaptureMode::ByReference,
                        value: HirExpr::TempRef(candidate),
                    }],
                })),
            ),
            boolean_shell(HirLValue::Temp(candidate)),
            HirStmt::Return(Box::new(HirReturn {
                values: HirValuePack::fixed(vec![HirExpr::LocalRef(closure)]),
            })),
        ];
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_temp(candidate);
        facts.record_home_free_local(closure);

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(proto.body.stmts.len(), 4);
        assert!(matches!(proto.body.stmts[2], HirStmt::Assign(_)));
    }

    #[test]
    fn reference_capture_then_overwrite_kills_the_shell_before_exit() {
        let candidate = TempId(0);
        let closure = LocalId(0);
        let mut proto = empty_test_proto();
        proto.temps = vec![candidate];
        proto.temp_debug_locals = vec![None];
        proto.temp_debug_scopes = vec![None];
        proto.locals = vec![closure];
        proto.local_debug_hints = vec![None];
        proto.local_debug_scopes = vec![None];
        proto.body.stmts = vec![
            assign_temp(candidate, HirExpr::Nil),
            boolean_shell(HirLValue::Temp(candidate)),
            local_decl(
                closure,
                HirExpr::Closure(Box::new(HirClosureExpr {
                    proto: HirProtoRef(1),
                    captures: vec![HirCapture {
                        mode: HirCaptureMode::ByReference,
                        value: HirExpr::TempRef(candidate),
                    }],
                })),
            ),
            assign_temp(candidate, HirExpr::Nil),
            HirStmt::Return(Box::new(HirReturn {
                values: HirValuePack::fixed(vec![HirExpr::LocalRef(closure)]),
            })),
        ];
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_temp(candidate);
        facts.record_home_free_local(closure);

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(proto.body.stmts.len(), 4);
        assert!(matches!(proto.body.stmts[1], HirStmt::LocalDecl(_)));
        assert!(matches!(proto.body.stmts[2], HirStmt::Assign(_)));
    }

    #[test]
    fn unused_named_reference_closure_does_not_observe_the_shell() {
        let candidate = TempId(0);
        let closure = LocalId(0);
        let mut proto = empty_test_proto();
        proto.temps = vec![candidate];
        proto.temp_debug_locals = vec![None];
        proto.temp_debug_scopes = vec![None];
        proto.locals = vec![closure];
        proto.local_debug_hints = vec![None];
        proto.local_debug_scopes = vec![None];
        proto.body.stmts = vec![
            assign_temp(candidate, HirExpr::Nil),
            local_decl(
                closure,
                HirExpr::Closure(Box::new(HirClosureExpr {
                    proto: HirProtoRef(1),
                    captures: vec![HirCapture {
                        mode: HirCaptureMode::ByReference,
                        value: HirExpr::TempRef(candidate),
                    }],
                })),
            ),
            boolean_shell(HirLValue::Temp(candidate)),
            HirStmt::Return(Box::new(HirReturn {
                values: HirValuePack::default(),
            })),
        ];
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_temp(candidate);
        facts.record_home_free_local(closure);

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(proto.body.stmts.len(), 3);
        assert!(matches!(proto.body.stmts[2], HirStmt::Return(_)));
    }

    #[test]
    fn by_value_capture_reads_the_shell_at_creation() {
        let candidate = TempId(0);
        let closure = LocalId(0);
        let mut proto = empty_test_proto();
        proto.temps = vec![candidate];
        proto.temp_debug_locals = vec![None];
        proto.temp_debug_scopes = vec![None];
        proto.locals = vec![closure];
        proto.local_debug_hints = vec![None];
        proto.local_debug_scopes = vec![None];
        proto.body.stmts = vec![
            assign_temp(candidate, HirExpr::Nil),
            boolean_shell(HirLValue::Temp(candidate)),
            local_decl(
                closure,
                HirExpr::Closure(Box::new(HirClosureExpr {
                    proto: HirProtoRef(1),
                    captures: vec![HirCapture {
                        mode: HirCaptureMode::ByValue,
                        value: HirExpr::TempRef(candidate),
                    }],
                })),
            ),
        ];
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_temp(candidate);
        facts.record_home_free_local(closure);

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(proto.body.stmts.len(), 3);
        assert!(matches!(proto.body.stmts[1], HirStmt::Assign(_)));
    }

    #[test]
    fn overwritten_closure_holder_does_not_observe_a_later_shell() {
        let candidate = TempId(0);
        let closure = LocalId(0);
        let mut proto = empty_test_proto();
        proto.temps = vec![candidate];
        proto.temp_debug_locals = vec![None];
        proto.temp_debug_scopes = vec![None];
        proto.locals = vec![closure];
        proto.local_debug_hints = vec![None];
        proto.local_debug_scopes = vec![None];
        proto.body.stmts = vec![
            assign_temp(candidate, HirExpr::Nil),
            local_decl(closure, reference_closure(HirExpr::TempRef(candidate))),
            assign_local(closure, HirExpr::Nil),
            boolean_shell(HirLValue::Temp(candidate)),
            call_stmt(HirExpr::LocalRef(closure)),
        ];
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_temp(candidate);
        facts.record_home_free_local(closure);

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(proto.body.stmts.len(), 4);
        assert!(matches!(proto.body.stmts[2], HirStmt::Assign(_)));
        assert!(matches!(proto.body.stmts[3], HirStmt::CallStmt(_)));
    }

    #[test]
    fn call_before_closure_assignment_does_not_observe_a_later_shell() {
        let candidate = TempId(0);
        let closure = LocalId(0);
        let mut proto = empty_test_proto();
        proto.temps = vec![candidate];
        proto.temp_debug_locals = vec![None];
        proto.temp_debug_scopes = vec![None];
        proto.locals = vec![closure];
        proto.local_debug_hints = vec![None];
        proto.local_debug_scopes = vec![None];
        proto.body.stmts = vec![
            assign_temp(candidate, HirExpr::Nil),
            call_stmt(HirExpr::LocalRef(closure)),
            local_decl(closure, reference_closure(HirExpr::TempRef(candidate))),
            boolean_shell(HirLValue::Temp(candidate)),
            HirStmt::Return(Box::new(HirReturn {
                values: HirValuePack::default(),
            })),
        ];
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_temp(candidate);
        facts.record_home_free_local(closure);

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(proto.body.stmts.len(), 4);
        assert!(matches!(proto.body.stmts[2], HirStmt::LocalDecl(_)));
        assert!(matches!(proto.body.stmts[3], HirStmt::Return(_)));
    }

    #[test]
    fn reference_capture_after_definite_write_does_not_observe_the_old_shell() {
        let candidate = TempId(0);
        let closure = LocalId(0);
        let mut proto = empty_test_proto();
        proto.temps = vec![candidate];
        proto.temp_debug_locals = vec![None];
        proto.temp_debug_scopes = vec![None];
        proto.locals = vec![closure];
        proto.local_debug_hints = vec![None];
        proto.local_debug_scopes = vec![None];
        proto.body.stmts = vec![
            assign_temp(candidate, HirExpr::Nil),
            local_decl(closure, reference_closure(HirExpr::TempRef(candidate))),
            boolean_shell(HirLValue::Temp(candidate)),
            assign_temp(candidate, HirExpr::Nil),
            call_stmt(HirExpr::LocalRef(closure)),
        ];
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_temp(candidate);
        facts.record_home_free_local(closure);

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(proto.body.stmts.len(), 4);
        assert!(matches!(proto.body.stmts[2], HirStmt::Assign(_)));
        assert!(matches!(proto.body.stmts[3], HirStmt::CallStmt(_)));
    }

    #[test]
    fn called_named_reference_closure_keeps_the_shell() {
        let candidate = TempId(0);
        let closure = LocalId(0);
        let mut proto = empty_test_proto();
        proto.temps = vec![candidate];
        proto.temp_debug_locals = vec![None];
        proto.temp_debug_scopes = vec![None];
        proto.locals = vec![closure];
        proto.local_debug_hints = vec![None];
        proto.local_debug_scopes = vec![None];
        proto.body.stmts = vec![
            assign_temp(candidate, HirExpr::Nil),
            local_decl(closure, reference_closure(HirExpr::TempRef(candidate))),
            boolean_shell(HirLValue::Temp(candidate)),
            call_stmt(HirExpr::LocalRef(closure)),
        ];
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_temp(candidate);
        facts.record_home_free_local(closure);

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(proto.body.stmts.len(), 4);
        assert!(matches!(proto.body.stmts[2], HirStmt::Assign(_)));
    }

    #[test]
    fn loop_reaching_closure_holder_keeps_the_shell_before_next_call() {
        let candidate = TempId(0);
        let closure = LocalId(0);
        let flag = LocalId(1);
        let mut proto = empty_test_proto();
        proto.temps = vec![candidate];
        proto.temp_debug_locals = vec![None];
        proto.temp_debug_scopes = vec![None];
        proto.locals = vec![closure, flag];
        proto.local_debug_hints = vec![None, None];
        proto.local_debug_scopes = vec![None, None];
        proto.body.stmts = vec![
            assign_temp(candidate, HirExpr::Nil),
            local_decl(closure, HirExpr::Nil),
            HirStmt::While(Box::new(crate::hir::common::HirWhile {
                cond: HirExpr::LocalRef(flag),
                body: HirBlock {
                    stmts: vec![
                        call_stmt(HirExpr::LocalRef(closure)),
                        assign_local(closure, reference_closure(HirExpr::TempRef(candidate))),
                        boolean_shell(HirLValue::Temp(candidate)),
                    ],
                },
            })),
        ];
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_temp(candidate);
        facts.record_home_free_local(closure);
        facts.record_home_free_local(flag);

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        let HirStmt::While(while_stmt) = &proto.body.stmts[2] else {
            panic!("loop must remain");
        };
        assert!(matches!(while_stmt.body.stmts[2], HirStmt::Assign(_)));
    }

    #[test]
    fn parameter_holder_return_keeps_the_captured_shell() {
        let candidate = TempId(0);
        let closure = ParamId(0);
        let mut proto = empty_test_proto();
        proto.params = vec![closure];
        proto.param_debug_hints = vec![None];
        proto.temps = vec![candidate];
        proto.temp_debug_locals = vec![None];
        proto.temp_debug_scopes = vec![None];
        proto.body.stmts = vec![
            assign_temp(candidate, HirExpr::Nil),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Param(closure)],
                values: HirValuePack::fixed(vec![reference_closure(HirExpr::TempRef(candidate))]),
            })),
            boolean_shell(HirLValue::Temp(candidate)),
            HirStmt::Return(Box::new(HirReturn {
                values: HirValuePack::fixed(vec![HirExpr::ParamRef(closure)]),
            })),
        ];
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_temp(candidate);
        facts.record_param_home_merge(closure, Some(BTreeSet::from([HomeSlotKey::new(0, 0)])));

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(proto.body.stmts.len(), 4);
        assert!(matches!(proto.body.stmts[2], HirStmt::Assign(_)));
    }

    #[test]
    fn upvalue_store_keeps_the_captured_shell() {
        let candidate = TempId(0);
        let upvalue = UpvalueId(0);
        let mut proto = empty_test_proto();
        proto.upvalues = vec![upvalue];
        proto.upvalue_debug_hints = vec![None];
        proto.temps = vec![candidate];
        proto.temp_debug_locals = vec![None];
        proto.temp_debug_scopes = vec![None];
        proto.body.stmts = vec![
            assign_temp(candidate, HirExpr::Nil),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Upvalue(upvalue)],
                values: HirValuePack::fixed(vec![reference_closure(HirExpr::TempRef(candidate))]),
            })),
            boolean_shell(HirLValue::Temp(candidate)),
        ];
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_temp(candidate);

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(proto.body.stmts.len(), 3);
        assert!(matches!(proto.body.stmts[2], HirStmt::Assign(_)));
    }

    #[test]
    fn external_parallel_target_does_not_escape_a_local_sibling_value() {
        let candidate = TempId(0);
        let closure = LocalId(0);
        let mut proto = empty_test_proto();
        proto.temps = vec![candidate];
        proto.temp_debug_locals = vec![None];
        proto.temp_debug_scopes = vec![None];
        proto.locals = vec![closure];
        proto.local_debug_hints = vec![None];
        proto.local_debug_scopes = vec![None];
        proto.body.stmts = vec![
            assign_temp(candidate, HirExpr::Nil),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![
                    HirLValue::Global(HirGlobalRef {
                        name: "external".to_owned(),
                    }),
                    HirLValue::Local(closure),
                ],
                values: HirValuePack::fixed(vec![
                    HirExpr::Nil,
                    reference_closure(HirExpr::TempRef(candidate)),
                ]),
            })),
            boolean_shell(HirLValue::Temp(candidate)),
        ];
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_temp(candidate);
        facts.record_home_free_local(closure);

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(proto.body.stmts.len(), 2);
        assert!(matches!(proto.body.stmts[1], HirStmt::Assign(_)));
    }

    #[test]
    fn later_overwrite_kills_the_shell_before_tbc_activation() {
        let candidate = TempId(0);
        let home = HomeSlotKey::new(0, 0);
        let mut proto = empty_test_proto();
        proto.temps = vec![candidate];
        proto.temp_debug_locals = vec![None];
        proto.temp_debug_scopes = vec![None];
        proto.body.stmts = vec![
            assign_temp(candidate, HirExpr::Nil),
            boolean_shell(HirLValue::Temp(candidate)),
            assign_temp(candidate, HirExpr::Nil),
            HirStmt::ToBeClosed(Box::new(HirToBeClosed {
                origin: InstrRef(0),
                reg_index: home.slot(),
                value: HirExpr::TempRef(candidate),
            })),
            HirStmt::Close(Box::new(HirClose {
                from_reg: home.slot(),
            })),
        ];
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(candidate, home);

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(proto.body.stmts.len(), 4);
        assert!(matches!(proto.body.stmts[1], HirStmt::Assign(_)));
    }

    #[test]
    fn local_shell_keeps_a_later_same_home_visible_read() {
        let candidate = LocalId(0);
        let observer = LocalId(1);
        let home = HomeSlotKey::new(0, 0);
        let mut proto = empty_test_proto();
        proto.locals = vec![candidate, observer];
        proto.local_debug_hints = vec![None, None];
        proto.local_debug_scopes = vec![None, None];
        proto.body.stmts = vec![
            local_decl(candidate, HirExpr::Nil),
            local_decl(observer, HirExpr::Nil),
            boolean_shell(HirLValue::Local(candidate)),
            HirStmt::If(Box::new(HirIf {
                cond: HirExpr::LocalRef(observer),
                then_block: HirBlock::default(),
                else_block: None,
            })),
        ];
        let mut facts = ProtoPromotionFacts::default();
        facts.record_local_home_slot(candidate, home);
        facts.record_local_home_slot(observer, home);

        assert!(remove_boolean_materialization_shells_in_proto(
            &mut proto,
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));
        assert_eq!(proto.body.stmts.len(), 4);
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
        assert!(matches!(proto.body.stmts[2], HirStmt::Assign(_)));
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
            boolean_shell(HirLValue::Temp(target)),
            HirStmt::If(Box::new(HirIf {
                cond: HirExpr::LocalRef(observer),
                then_block: HirBlock::default(),
                else_block: None,
            })),
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

    fn reference_closure(value: HirExpr) -> HirExpr {
        HirExpr::Closure(Box::new(HirClosureExpr {
            proto: HirProtoRef(1),
            captures: vec![HirCapture {
                mode: HirCaptureMode::ByReference,
                value,
            }],
        }))
    }

    fn call_stmt(callee: HirExpr) -> HirStmt {
        HirStmt::CallStmt(Box::new(HirCallStmt {
            call: HirCallExpr {
                callee,
                args: HirValuePack::default(),
                method: false,
                fastcall: None,
                method_name: None,
            },
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
