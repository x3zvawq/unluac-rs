//! 这个文件负责清理已经失去职责的值物化分支壳。
//!
//! 它依赖更前面的 HIR 决策已经把“真正承载语义的 merge 值”恢复成直接表达式；
//! 走到这里时，某些 `if cond then t=true else t=false end` 只剩下机械性的值物化。
//! 这里专门删除这一类纯值壳，或者把它们折回单条赋值，避免把真正承担控制语义的
//! `if/else` 结构误删掉。删除死写前还要证明目标没有外部读取、capture、debug identity
//! 或物理根职责；把相邻空声明吸收到初始化器时，则必须保留条件求值期间的词法作用域。
//! 条件是否可删除、arm 结果是否承载 GC root 统一消费入口按目标方言构造的表达式安全上下文。
//! debug 映射按 canonical binding 下标查询；两个改写阶段共享借用的 proto 元数据，
//! 不重建 debug 身份集合，promotion 与物理根事实也由同一只读视图提供。
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

use old_values::OldValueFacts;

use std::collections::BTreeSet;

use crate::hir::common::{
    HirAssign, HirBinaryOpKind, HirBlock, HirDebugScope, HirExpr, HirIf, HirLValue, HirLocalDecl,
    HirLogicalExpr, HirProto, HirSourceSite, HirStmt, HirUnaryExpr, HirUnaryOpKind, HirValuePack,
    LocalId,
};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::ProtoPromotionFacts;

use super::expr_facts::{expr_is_boolean_valued, expr_truthiness};
use super::local_shapes::empty_single_local_decl_binding;
use super::mention::expr_mentions_local;
use super::walk::{HirRewritePass, rewrite_block};

pub(super) fn remove_boolean_materialization_shells_in_proto(
    proto: &mut HirProto,
    promotion_facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
) -> bool {
    let facts = BooleanShellFacts {
        temp_debug_hints: &proto.temp_debug_locals,
        local_debug_hints: &proto.local_debug_hints,
        local_debug_scopes: &proto.local_debug_scopes,
        debug_scopes: &proto.debug_scopes,
        physical_root_locals: &proto.physical_root_locals,
        promotion_facts,
    };
    let old_value_plan = old_values::DeadShellPlan::collect(proto, &facts, safety);
    let old_value_changed = old_value_plan.apply(&mut proto.body);
    let mut pass = BooleanShellPass { facts: &facts };
    old_value_changed | rewrite_block(&mut proto.body, &mut pass)
}

struct BooleanShellPass<'a> {
    facts: &'a BooleanShellFacts<'a>,
}

impl HirRewritePass for BooleanShellPass<'_> {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        collapse_live_boolean_materialization_shells_in_block(block, self.facts)
    }
}

struct BooleanShellFacts<'a> {
    temp_debug_hints: &'a [Option<String>],
    local_debug_hints: &'a [Option<String>],
    local_debug_scopes: &'a [Option<usize>],
    debug_scopes: &'a [Option<HirDebugScope>],
    physical_root_locals: &'a BTreeSet<LocalId>,
    promotion_facts: &'a ProtoPromotionFacts,
}

struct DeadWriteProof<'a> {
    live_after: &'a old_values::LiveBindingState,
    adjacent_nil_local: Option<LocalId>,
    old_values: &'a OldValueFacts,
}

impl BooleanShellFacts<'_> {
    fn target_write_is_unobservable(
        &self,
        target: &HirLValue,
        written_value_is_gc_inert: bool,
        proof: &DeadWriteProof<'_>,
    ) -> bool {
        match target {
            HirLValue::Temp(temp) => {
                // 候选拒绝[SemanticBarrier:DebugScope]：debug temp 是 IR 已保留的源码 binding；删除其分支写入会抹掉该 source identity。
                if matches!(self.temp_debug_hints.get(temp.index()), Some(Some(_))) {
                    return false;
                }
                if !written_value_is_gc_inert {
                    // 候选拒绝[SemanticBarrier:Lifetime]：把对象引用写入 raw home 会建立新的 VM root；删除死写可能让该对象在后续显式 GC 中提前终结。
                    return false;
                }
                let homes = self.promotion_facts.complete_temp_home_slots(*temp);
                for home in homes.iter() {
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
                if matches!(self.local_debug_hints.get(local.index()), Some(Some(_))) {
                    return false;
                }
                // 候选拒绝[SemanticBarrier:Lifetime]：物理根 local 的写入决定可观察的 GC 存活区间，不能按普通死值删除。
                if self.physical_root_locals.contains(local) {
                    return false;
                }
                let homes = self.promotion_facts.complete_local_home_slots(*local);
                for home in homes.iter() {
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum OldValueClass {
    GcInert,
    MayCarryResource,
    Unknown,
}

fn collapse_live_boolean_materialization_shells_in_block(
    block: &mut HirBlock,
    facts: &BooleanShellFacts,
) -> bool {
    let mut retained = 0;
    let mut changed = false;
    for index in 0..block.stmts.len() {
        if let Some((target, value)) =
            collapse_live_boolean_materialization_shell(&mut block.stmts[index])
        {
            changed = true;
            if retained > 0
                && let HirLValue::Local(local) = &target
                && empty_single_local_decl_binding(&block.stmts[retained - 1]) == Some(*local)
                && declaration_can_absorb_boolean_shell(*local, &value, facts)
            {
                block.stmts[retained - 1] = HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![*local],
                    values: HirValuePack::fixed(vec![value]),
                    initializer_merge_transaction: None,
                }));
                // 输出仍是声明，不会成为新的分支候选；不必回退或逐次搬移整个尾部。
                continue;
            }

            block.stmts[index] = HirStmt::Assign(Box::new(HirAssign {
                targets: vec![target],
                values: HirValuePack::fixed(vec![value]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                generic_for_dispatch_release: None,
                method_rewrite_transaction: None,
            }));
        }
        // 只与已读位置交换，未处理的后缀及上一条保留语句的邻接关系不变。
        if retained != index {
            block.stmts.swap(retained, index);
        }
        retained += 1;
    }
    block.stmts.truncate(retained);

    changed
}

fn declaration_can_absorb_boolean_shell(
    local: LocalId,
    value: &HirExpr,
    facts: &BooleanShellFacts,
) -> bool {
    // 候选拒绝[SemanticBarrier:Scope]：regress_342 retain-debug 证明条件中的调用能观察到原声明；合并会把 debug 作用域起点后移。
    if matches!(facts.local_debug_hints.get(local.index()), Some(Some(_)))
        && !debug_branch_initializer_matches(local, value, facts)
    {
        return false;
    }
    // 候选拒绝[SemanticBarrier:Scope]：regress_342 stripped 证明初始化器中的同名引用会改绑到外层 local，而不是读取已经声明的当前 local。
    !expr_mentions_local(value, local)
}

fn debug_branch_initializer_matches(
    local: LocalId,
    value: &HirExpr,
    facts: &BooleanShellFacts,
) -> bool {
    let matched = || {
        let scope = facts
            .local_debug_scopes
            .get(local.index())
            .copied()
            .flatten()?;
        let initializer = facts
            .debug_scopes
            .get(scope)
            .copied()
            .flatten()?
            .branch_initializer?;
        // Phi 的 promoted binding 与原 predicate 必须同时吻合；后续同 local 的另一次
        // 布尔赋值不能领取这个初始化边界，也不把缺 home 的合流当成原槽声明。
        let home = facts
            .promotion_facts
            .trusted_temp_home_slot(initializer.result)?;
        (facts
            .promotion_facts
            .promoted_local_for_temp(initializer.result)
            == Some(local)
            && facts.promotion_facts.trusted_local_home_slot(local) == Some(home)
            && boolean_predicate_source(value) == Some(initializer.condition))
        .then_some(())
    };
    matched().is_some()
}

fn boolean_predicate_source(value: &HirExpr) -> Option<HirSourceSite> {
    match value {
        HirExpr::Binary(binary)
            if matches!(
                binary.op,
                HirBinaryOpKind::Eq | HirBinaryOpKind::Lt | HirBinaryOpKind::Le
            ) =>
        {
            binary.source_site
        }
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not && unary.source_site.is_none() => {
            boolean_predicate_source(&unary.expr)
        }
        _ => None,
    }
}

fn collapse_live_boolean_materialization_shell(stmt: &mut HirStmt) -> Option<(HirLValue, HirExpr)> {
    let HirStmt::If(if_stmt) = stmt else {
        return None;
    };
    let [(then_target, then_value), (else_target, else_value)] = fixed_assign_arms(if_stmt)?;
    if then_target != else_target {
        // 候选拒绝[SemanticBarrier:ValueFlow]：same-home 不代表可见 binding 等价；统一 local/param 写入会改变分支结果。
        return None;
    }
    // 候选拒绝[SemanticBarrier:EvalOrder]：regress_249 中 table 左值会把地址求值移出已选分支，条件改写的 holder 因而指向不同 table。
    if !target_address_can_follow_condition_eval(then_target) {
        return None;
    }

    let positive = match (then_value, else_value) {
        (HirExpr::Boolean(true), HirExpr::Boolean(false)) => true,
        (HirExpr::Boolean(false), HirExpr::Boolean(true)) => false,
        _ => return None,
    };
    let target = then_target.clone();
    // 所有分支转换 guard 已通过；声明吸收即使被拒绝，也会提交为独立赋值。
    let cond = std::mem::replace(&mut if_stmt.cond, HirExpr::Nil);
    let value = if positive {
        booleanized_truthiness_expr(cond)
    } else {
        HirExpr::Unary(Box::new(HirUnaryExpr {
            source_site: None,
            op: HirUnaryOpKind::Not,
            expr: cond,
        }))
    };
    Some((target, value))
}

fn removable_dead_materialization_shell(
    stmt: &HirStmt,
    facts: &BooleanShellFacts,
    adjacent_nil_local: Option<LocalId>,
    old_values: &OldValueFacts,
    live_after: &old_values::ShellArmLiveOut,
    safety: HirExprSafety,
) -> bool {
    let HirStmt::If(if_stmt) = stmt else {
        return false;
    };
    let Some([(then_target, then_value), (else_target, else_value)]) = fixed_assign_arms(if_stmt)
    else {
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

fn fixed_assign_arms(if_stmt: &HirIf) -> Option<[(&HirLValue, &HirExpr); 2]> {
    Some([
        single_fixed_assign_pattern(&if_stmt.then_block)?,
        single_fixed_assign_pattern(if_stmt.else_block.as_ref()?)?,
    ])
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
