//! 将 singleton seed 交接合并为 global 声明。
//!
//! 消费当前使用、提及与 rewrite authority，保留原声明来源。

use std::collections::BTreeMap;

use super::super::binding_flow::{BindingUseIndex, last_binding_mentions};
use super::super::stmt_plan::{PlannedStmt, materialize_stmt_plan};
use crate::ast::common::{
    AstBindingRef, AstBlock, AstExpr, AstGlobalBinding, AstGlobalDecl, AstLocalAttr,
    AstLocalOrigin, AstStmt,
};

pub(super) fn merge_seed_global_runs(block: &mut AstBlock) -> bool {
    if !block
        .stmts
        .windows(2)
        .any(|pair| matches!(pair, [AstStmt::LocalDecl(_), AstStmt::GlobalDecl(_)]))
    {
        return false;
    }
    let old_stmts = std::mem::take(&mut block.stmts);
    let use_index = BindingUseIndex::for_stmts(&old_stmts);
    let last_mentions = last_binding_mentions(&old_stmts);
    let mut stmt_plan = Vec::with_capacity(old_stmts.len());
    let mut index = 0usize;
    let mut changed = false;

    while index < old_stmts.len() {
        if let Some((stmt, consumed)) =
            try_merge_seed_global_run(&old_stmts, &use_index, &last_mentions, index)
        {
            stmt_plan.push(PlannedStmt::Rewritten(stmt));
            index += consumed;
            changed = true;
            continue;
        }
        stmt_plan.push(PlannedStmt::Original(index));
        index += 1;
    }

    block.stmts = materialize_stmt_plan(old_stmts, stmt_plan);
    changed
}

fn try_merge_seed_global_run(
    stmts: &[AstStmt],
    use_index: &BindingUseIndex,
    last_mentions: &BTreeMap<AstBindingRef, usize>,
    start: usize,
) -> Option<(AstStmt, usize)> {
    let [AstStmt::LocalDecl(local_decl), next, ..] = stmts.get(start..)? else {
        return None;
    };
    let ([seed], [value]) = (local_decl.bindings.as_slice(), local_decl.values.as_slice()) else {
        return None;
    };
    if seed.attr != AstLocalAttr::None {
        return None;
    }
    let (global_source, global_binding) = singleton_global_handoff(next)?;
    if seed.id != global_source {
        return None;
    }
    if stmts
        .get(start + 2)
        .and_then(singleton_global_handoff)
        .is_some_and(|(_, following)| following.attr == global_binding.attr)
    {
        // 候选拒绝[SemanticBarrier:EvalOrder]：原扫描会继续认领同属性 handoff，不能
        // 把被拒绝的多目标 run 拆成首个 pair；全局写入顺序见 regress_335/regress_409。
        return None;
    }
    if !seed.rewrite_authority.may_remove_binding() {
        // 候选拒绝[LayerBoundary]：global decl sugar 会删除 seed local；HIR 已发布的
        // binding 生命周期结论不能由 AST 的一对一 global 形状覆盖。
        return None;
    }
    match seed.origin {
        AstLocalOrigin::Recovered => {}
        AstLocalOrigin::DebugHinted | AstLocalOrigin::DebugHintedPhysicalRoot => {
            // 候选拒绝[SemanticBarrier:DebugScope]：DebugHinted seed 是显式源码 local 身份；regress335 通过 debug.getlocal 观察该名字，声明合并不得抹掉它。
            return None;
        }
        AstLocalOrigin::PhysicalRoot => {
            // 候选拒绝[SemanticBarrier:Lifetime]：global 随后被覆盖时，PhysicalRoot seed 仍须把旧值保活到原 block 末端；regress335 用弱表/GC 观察提前消失。
            return None;
        }
    }
    if use_index.count_uses_in_suffix(start, seed.id) != 1 {
        // 候选拒绝[SemanticBarrier:Scope]：唯一允许的 seed use 是对应 global
        // handoff；如 `global out=seed; return function() return seed end`，删除声明会
        // 让后续 direct/captured use 失去 local owner。
        return None;
    }
    if last_mentions
        .get(&seed.id)
        .is_some_and(|&last| last >= start + 2)
    {
        // 候选拒绝[SemanticBarrier:Scope]：global handoff 后的 direct write 或
        // `function seed.field()` 仍依赖该 local owner；删除声明会把它改成未声明/global
        // binding。regress335 的 function-name seed 可直接观察生成源码失去 owner。
        return None;
    }

    Some((
        AstStmt::GlobalDecl(Box::new(AstGlobalDecl {
            bindings: vec![global_binding.clone()],
            values: vec![value.clone()],
        })),
        2,
    ))
}

fn singleton_global_handoff(stmt: &AstStmt) -> Option<(AstBindingRef, &AstGlobalBinding)> {
    let AstStmt::GlobalDecl(global_decl) = stmt else {
        return None;
    };
    let ([binding], [AstExpr::Var(name)]) = (
        global_decl.bindings.as_slice(),
        global_decl.values.as_slice(),
    ) else {
        return None;
    };
    Some((AstBindingRef::from_name_ref(name)?, binding))
}
