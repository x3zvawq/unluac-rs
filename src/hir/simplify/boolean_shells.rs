//! 这个文件负责清理已经失去职责的值物化分支壳。
//!
//! 它依赖更前面的 HIR 决策已经把“真正承载语义的 merge 值”恢复成直接表达式；
//! 走到这里时，某些 `if cond then t=true else t=false end` 只剩下机械性的值物化。
//! 这里专门删除这一类纯值壳，或者把它们折回单条赋值，避免把真正承担控制语义的
//! `if/else` 结构误删掉。删除死写前还要证明目标没有外部读取、capture、debug identity
//! 或物理根职责；把相邻空声明吸收到初始化器时，则必须保留条件求值期间的词法作用域。
//!
//! 它不会越权去重新判断 branch/loop 是否应该结构化，也不会替前层补决策。
//! 这里唯一关心的是：当前 `if` 是否已经退化成“无副作用的布尔值搬运壳”。table
//! 左值的地址在分支条件之后已经确定，不能把它挪到合并后赋值的 RHS 之前重新求值。
//!
//! 例子：
//! - 输入：`if cond then t = true else t = false end`
//! - 输出：`t = cond or false`
//! - 如果 `t` 后面已经没人再读，且 `cond/true/false` 都无副作用，则整段壳会被删除

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirAssign, HirBlock, HirExpr, HirLValue, HirLocalDecl, HirLogicalExpr, HirProto, HirStmt,
    HirUnaryExpr, HirUnaryOpKind, HirValuePack, LocalId, TempId,
};
use crate::hir::expr_safety::expr_is_discard_safe;
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

use super::expr_facts::expr_is_boolean_valued;
use super::local_shapes::empty_single_local_decl_binding;
use super::mention::expr_mentions_local;
use super::visit::{HirVisitor, visit_proto, visit_stmts};
use super::walk::{HirRewritePass, rewrite_proto};

pub(super) fn remove_boolean_materialization_shells_in_proto(
    proto: &mut HirProto,
    promotion_facts: &ProtoPromotionFacts,
) -> bool {
    let facts = BooleanShellFacts::collect(proto, promotion_facts);
    let mut pass = BooleanShellPass { facts: &facts };
    rewrite_proto(proto, &mut pass)
}

struct BooleanShellPass<'a> {
    facts: &'a BooleanShellFacts,
}

impl HirRewritePass for BooleanShellPass<'_> {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        let dead_changed = remove_dead_materialization_shells_from_block(block, self.facts);
        let collapse_changed =
            collapse_live_boolean_materialization_shells_in_block(block, self.facts);
        dead_changed || collapse_changed
    }
}

#[derive(Default)]
struct BindingUseCounts {
    temps: BTreeMap<TempId, usize>,
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
        if let HirExpr::TempRef(temp) = expr {
            *self.temps.entry(*temp).or_default() += 1;
        }
    }
}

struct BooleanShellFacts {
    uses: BindingUseCounts,
    debug_temps: BTreeSet<TempId>,
    debug_locals: BTreeSet<LocalId>,
    physical_root_locals: BTreeSet<LocalId>,
    parameters_by_home: BTreeMap<HomeSlotKey, crate::hir::common::ParamId>,
    temp_homes: BTreeMap<TempId, HomeSlotKey>,
    local_homes: BTreeMap<LocalId, HomeSlotKey>,
}

impl BooleanShellFacts {
    fn collect(proto: &HirProto, promotion_facts: &ProtoPromotionFacts) -> Self {
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
            parameters_by_home: proto
                .params
                .iter()
                .map(|param| (HomeSlotKey::new(param.index(), 0), *param))
                .collect(),
            temp_homes: proto
                .temps
                .iter()
                .filter_map(|temp| promotion_facts.home_slot(*temp).map(|home| (*temp, home)))
                .collect(),
            local_homes: proto
                .locals
                .iter()
                .filter_map(|local| {
                    promotion_facts
                        .local_home_slot(*local)
                        .map(|home| (*local, home))
                })
                .collect(),
        }
    }

    fn target_write_is_unobservable(
        &self,
        target: &HirLValue,
        internal_uses: &BindingUseCounts,
    ) -> bool {
        match target {
            HirLValue::Temp(temp) => {
                // 候选拒绝[SemanticBarrier:Lifetime]：regress_342 中 dead boolean temp 覆盖参数 home；删除该写入会让旧参数对象继续作为 GC root 存活。
                if self
                    .temp_homes
                    .get(temp)
                    .is_some_and(|home| self.parameters_by_home.contains_key(home))
                {
                    return false;
                }
                // 候选拒绝[PolicyBoundary]：debug temp 是源码 binding；删除其分支写入会抹掉保留的 source identity。
                if self.debug_temps.contains(temp) {
                    return false;
                }
                if self.temp_homes.contains_key(temp) {
                    // 候选拒绝[ProofIncomplete]：raw home temp 的死写可能释放旧槽位中的 GC root；需接入 reaching resource-value 事实后才能放行已知非资源前值。
                    return false;
                }
                // 候选拒绝[SemanticBarrier:ValueFlow]：shell 外仍读取或 capture 该 temp 时，删除写入会改变后续值。
                use_is_internal_only(&self.uses.temps, &internal_uses.temps, *temp)
            }
            HirLValue::Local(local) => {
                // 候选拒绝[SemanticBarrier:Lifetime]：映射到参数 home 的 local 写入会释放旧参数对象；regress_342 证明删除它会推迟可观察的 GC。
                if self
                    .local_homes
                    .get(local)
                    .is_some_and(|home| self.parameters_by_home.contains_key(home))
                {
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
                // 候选拒绝[ProofIncomplete]：普通 local 的旧值也可能是可回收对象；需接入 reaching resource-value 事实后才能证明这次死写不改变 GC 时点。
                false
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

    fn canonical_shared_target(
        &self,
        then_target: &HirLValue,
        else_target: &HirLValue,
    ) -> Option<HirLValue> {
        if then_target == else_target {
            return Some(then_target.clone());
        }
        let then_home = self.target_home(then_target)?;
        let else_home = self.target_home(else_target)?;
        if then_home != else_home {
            return None;
        }
        self.parameters_by_home
            .get(&then_home)
            .copied()
            .map(HirLValue::Param)
    }

    fn target_home(&self, target: &HirLValue) -> Option<HomeSlotKey> {
        match target {
            HirLValue::Param(param) => Some(HomeSlotKey::new(param.index(), 0)),
            HirLValue::Temp(temp) => self.temp_homes.get(temp).copied(),
            HirLValue::Local(local) => self.local_homes.get(local).copied(),
            HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_) => None,
        }
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
) -> bool {
    let old_len = block.stmts.len();
    block
        .stmts
        .retain(|stmt| !removable_dead_materialization_shell(stmt, facts));
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
            collapsible_live_boolean_materialization_shell(&block.stmts[index], facts)
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

fn collapsible_live_boolean_materialization_shell(
    stmt: &HirStmt,
    facts: &BooleanShellFacts,
) -> Option<(HirLValue, HirExpr)> {
    let HirStmt::If(if_stmt) = stmt else {
        return None;
    };
    let Some(else_block) = &if_stmt.else_block else {
        return None;
    };

    let (then_target, then_value) = single_fixed_assign_pattern(&if_stmt.then_block)?;
    let (else_target, else_value) = single_fixed_assign_pattern(else_block)?;
    let target = facts.canonical_shared_target(then_target, else_target)?;
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

fn removable_dead_materialization_shell(stmt: &HirStmt, facts: &BooleanShellFacts) -> bool {
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
    if !facts.target_write_is_unobservable(then_target, &internal_uses)
        || !facts.target_write_is_unobservable(else_target, &internal_uses)
    {
        return false;
    }
    // 候选拒绝[SemanticBarrier:EvalCount]：删除 `if f() then t=true else t=false end` 会漏掉仍需执行一次的 `f()`。
    if !expr_is_discard_safe(&if_stmt.cond) {
        return false;
    }

    // 候选拒绝[SemanticBarrier:EvalCount]：死 binding 的 `t=f()` 仍必须调用一次 `f()`，不能随布尔壳一起丢弃。
    expr_is_discard_safe(then_value) && expr_is_discard_safe(else_value)
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
