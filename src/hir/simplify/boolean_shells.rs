//! 将布尔物化分支收回赋值，同时保留原条件检查和目标写入。
//!
//! 消费现有 HIR 决策、debug 初始化区间与物理帧约束；即使结果无后续读取，
//! 也不能整段删除原分支。高槽 CALL 的布尔写回仍交给完整调用帧 owner。

use crate::hir::common::{
    HirAssign, HirBinaryOpKind, HirBlock, HirDebugScope, HirExpr, HirIf, HirLValue, HirLocalDecl,
    HirLogicalExpr, HirProto, HirSourceSite, HirStmt, HirUnaryExpr, HirUnaryOpKind, HirValuePack,
    LocalId,
};
use crate::hir::promotion::ProtoPromotionFacts;

use super::expr_facts::expr_is_boolean_valued;
use super::local_shapes::empty_single_local_decl_binding;
use super::mention::expr_mentions_local;
use super::walk::{HirRewritePass, rewrite_block};

pub(super) fn remove_boolean_materialization_shells_in_proto(
    proto: &mut HirProto,
    promotion_facts: &ProtoPromotionFacts,
) -> bool {
    let facts = BooleanShellFacts {
        local_debug_hints: &proto.local_debug_hints,
        local_debug_scopes: &proto.local_debug_scopes,
        debug_scopes: &proto.debug_scopes,
        inline_dispositions: &proto.inline_dispositions,
        promotion_facts,
    };
    let mut pass = BooleanShellPass { facts: &facts };
    rewrite_block(&mut proto.body, &mut pass)
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
    local_debug_hints: &'a [Option<String>],
    local_debug_scopes: &'a [Option<usize>],
    debug_scopes: &'a [Option<HirDebugScope>],
    inline_dispositions: &'a crate::hir::HirInlineDispositions,
    promotion_facts: &'a ProtoPromotionFacts,
}

fn collapse_live_boolean_materialization_shells_in_block(
    block: &mut HirBlock,
    facts: &BooleanShellFacts,
) -> bool {
    let mut retained: usize = 0;
    let mut changed = false;
    for index in 0..block.stmts.len() {
        let needs_call_frame = boolean_shell_has_high_call_result(
            &block.stmts[index],
            retained
                .checked_sub(1)
                .map(|previous| &block.stmts[previous]),
            facts.promotion_facts,
        );
        if !needs_call_frame
            && let Some((target, value)) =
                collapse_live_boolean_materialization_shell(&mut block.stmts[index], facts)
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
                luau_function_declaration: false,
                luau_compound_global: false,
                upvalue_write_source: None,
                is_phi_transfer: false,
                parallel_nil_frame: None,
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

fn boolean_shell_has_high_call_result(
    stmt: &HirStmt,
    previous: Option<&HirStmt>,
    facts: &ProtoPromotionFacts,
) -> bool {
    let HirStmt::If(if_) = stmt else {
        return false;
    };
    let Some([(target, HirExpr::Boolean(_)), (other, HirExpr::Boolean(_))]) =
        fixed_assign_arms(if_)
    else {
        return false;
    };
    if target != other {
        return false;
    }
    let home = match target {
        HirLValue::Local(local) => facts.trusted_local_home_slot(*local),
        HirLValue::Param(param) => facts.trusted_param_home_slot(*param),
        _ => None,
    };
    let Some(home) = home else {
        return false;
    };
    let mut subject = &if_.cond;
    while let HirExpr::Unary(unary) = subject
        && unary.op == HirUnaryOpKind::Not
        && unary.source_site.is_none()
    {
        subject = &unary.expr;
    }
    let value = match (subject, previous) {
        (HirExpr::Call(_), _) => subject,
        (HirExpr::TempRef(temp), Some(previous)) => {
            let Some((producer, value)) = previous.scalar_temp_assignment() else {
                return false;
            };
            if producer != *temp {
                return false;
            }
            value
        }
        (HirExpr::LocalRef(local), Some(HirStmt::LocalDecl(decl)))
            if decl.bindings.as_slice() == [*local]
                && decl.values.tail.is_none()
                && decl.values.fixed.len() == 1 =>
        {
            &decl.values.fixed[0]
        }
        (HirExpr::LocalRef(local), Some(HirStmt::Assign(assign)))
            if assign.targets.as_slice() == [HirLValue::Local(*local)]
                && assign.values.tail.is_none()
                && assign.values.fixed.len() == 1 =>
        {
            &assign.values.fixed[0]
        }
        _ => return false,
    };
    let HirExpr::Call(call) = value else {
        return false;
    };
    // 候选拒绝[LayerBoundary]：低槽 Boolean 写回与高槽 CALL 是同一 TEST 帧。
    // 保留控制头供 native-call-frames 原位消费准备，不能先改成会覆盖结果的双 NOT。
    facts
        .native_call_frame(call)
        .is_some_and(|frame| home.slot() < frame.home.slot())
}

fn declaration_can_absorb_boolean_shell(
    local: LocalId,
    value: &HirExpr,
    facts: &BooleanShellFacts,
) -> bool {
    if facts.inline_dispositions.local(local).must_preserve() {
        // 候选拒绝[LayerBoundary]：原 TEST 的低槽目标可能承担高槽 CALL 的前缀；
        // 原位 Boolean 写回不授权把声明移到调用之后或改变 CALL 的结果槽。
        return false;
    }
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
                HirBinaryOpKind::Eq
                    | HirBinaryOpKind::Lt
                    | HirBinaryOpKind::Le
                    | HirBinaryOpKind::Gt
                    | HirBinaryOpKind::Ge
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

fn collapse_live_boolean_materialization_shell(
    stmt: &mut HirStmt,
    facts: &BooleanShellFacts,
) -> Option<(HirLValue, HirExpr)> {
    let HirStmt::If(if_stmt) = stmt else {
        return None;
    };
    let [(then_target, then_value), (else_target, else_value)] = fixed_assign_arms(if_stmt)?;
    if then_target != else_target {
        // 候选拒绝[SemanticBarrier:ValueFlow]：same-home 不代表可见 binding 等价；统一 local/param 写入会改变分支结果。
        return None;
    }
    if let HirLValue::Local(local) = then_target
        && matches!(facts.inline_dispositions.local(*local), crate::hir::HirInlineDisposition::Preserve(reasons)
            if reasons.contains(&crate::hir::HirInlineRetentionReason::PhysicalFramePrefix))
    {
        // 候选拒绝[ProofIncomplete:RootLifetime]：低目标与高 scratch 的 TEST 写回需要
        // 完整帧 owner；单独改成值表达式会改变下一轮编译的 CALL 结果槽和根退休点。
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
            preserves_boolean_prewrite: false,
            lhs: HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
                preserves_boolean_prewrite: false,
                lhs: cond,
                rhs: HirExpr::Boolean(true),
            })),
            rhs: HirExpr::Boolean(false),
        }))
    }
}
