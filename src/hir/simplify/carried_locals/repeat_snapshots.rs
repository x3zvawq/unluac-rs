//! 收回 repeat 尾部只为承接最终状态而生成的临时快照。
//!
//! 只处理一条可证明的局部形状：body 末尾先计算 `temp = repeatable(local)`，紧接着
//! `local = temp`，循环后的唯一消费者是 `return temp`。中间没有 break/continue/goto，
//! 因而把第一条赋值直接改成 `local = repeatable(local)` 不会改变任何可观察求值点；
//! 捕获、`<close>` 和 debug temp 也会阻断该规则。

use std::collections::{BTreeMap, BTreeSet};

use super::super::mention::{
    collect_temp_use_counts, collect_temp_write_counts, stmts_protected_locals,
    stmts_reference_captured_bindings, stmts_to_be_closed_temps, stmts_value_captured_bindings,
};
use super::super::walk::for_each_nested_block_mut;
use crate::hir::common::{
    HirAssign, HirBlock, HirExpr, HirLValue, HirProto, HirStmt, LocalId, TempId,
};
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};
use crate::hir::visit::{HirVisitor, visit_block};

use super::CarryBinding;

pub(super) fn coalesce_repeat_terminal_snapshots(
    proto: &mut HirProto,
    promotion_facts: &mut ProtoPromotionFacts,
    preserved_bindings: &BTreeSet<CarryBinding>,
) -> bool {
    let use_counts = collect_temp_use_counts(proto);
    let reference_captured = stmts_reference_captured_bindings(&proto.body.stmts);
    let value_captured = stmts_value_captured_bindings(&proto.body.stmts);
    let mut captured_locals = reference_captured.locals;
    captured_locals.extend(value_captured.locals);
    let mut captured_temps = reference_captured.temps;
    captured_temps.extend(value_captured.temps);
    let closed_temps = stmts_to_be_closed_temps(&proto.body.stmts);
    let protected_locals = stmts_protected_locals(&proto.body.stmts);
    let write_counts = collect_temp_write_counts(proto);
    let facts = RepeatSnapshotFacts {
        use_counts: &use_counts,
        captured_locals: &captured_locals,
        protected_locals: &protected_locals,
        captured_temps: &captured_temps,
        closed_temps: &closed_temps,
        write_counts: &write_counts,
        debug_temps: &proto.temp_debug_locals,
        preserved_bindings,
    };
    rewrite_block(
        &mut proto.body,
        &facts,
        promotion_facts,
        &proto.physical_root_temps,
        &mut proto.physical_root_locals,
    )
}

struct RepeatSnapshotFacts<'a> {
    use_counts: &'a BTreeMap<TempId, usize>,
    captured_locals: &'a BTreeSet<LocalId>,
    protected_locals: &'a BTreeSet<LocalId>,
    captured_temps: &'a BTreeSet<TempId>,
    closed_temps: &'a BTreeSet<TempId>,
    write_counts: &'a BTreeMap<TempId, usize>,
    debug_temps: &'a [Option<String>],
    preserved_bindings: &'a BTreeSet<CarryBinding>,
}

fn rewrite_block(
    block: &mut HirBlock,
    facts: &RepeatSnapshotFacts<'_>,
    promotion_facts: &mut ProtoPromotionFacts,
    physical_root_temps: &BTreeSet<TempId>,
    physical_root_locals: &mut BTreeSet<LocalId>,
) -> bool {
    let mut changed = false;
    for stmt in &mut block.stmts {
        for_each_nested_block_mut(stmt, &mut |nested| {
            changed |= rewrite_block(
                nested,
                facts,
                promotion_facts,
                physical_root_temps,
                physical_root_locals,
            );
        });
    }

    let mut index = 0;
    while index + 1 < block.stmts.len() {
        let Some(return_temp) = immediate_return_temp(&block.stmts[index + 1]) else {
            index += 1;
            continue;
        };
        let HirStmt::Repeat(repeat) = &mut block.stmts[index] else {
            index += 1;
            continue;
        };
        let Some(local) = try_rewrite_repeat(repeat, return_temp, facts, promotion_facts) else {
            index += 1;
            continue;
        };
        if let HirStmt::Return(ret) = &mut block.stmts[index + 1] {
            ret.values.fixed[0] = HirExpr::LocalRef(local);
            changed = true;
        }
        if physical_root_temps.contains(&return_temp) {
            // 尾 copy 已证明 local 在所有可观察点持有同一值；若旧 temp 带保活身份，
            // 把身份交给仍存活的 local，避免 AST 后续把最后一个可见 root 当普通 alias 删除。
            physical_root_locals.insert(local);
        }
        index += 1;
    }
    changed
}

fn immediate_return_temp(stmt: &HirStmt) -> Option<TempId> {
    let HirStmt::Return(ret) = stmt else {
        return None;
    };
    if ret.values.tail.is_some() || ret.values.fixed.len() != 1 {
        return None;
    }
    match &ret.values.fixed[0] {
        HirExpr::TempRef(temp) => Some(*temp),
        _ => None,
    }
}

fn try_rewrite_repeat(
    repeat: &mut crate::hir::common::HirRepeat,
    return_temp: TempId,
    facts: &RepeatSnapshotFacts<'_>,
    promotion_facts: &mut ProtoPromotionFacts,
) -> Option<LocalId> {
    // 候选拒绝[SemanticBarrier:ControlFlow]：当前 repeat 的 break/continue/return/goto 可绕过尾 copy；删除 temp 会改变对应出口的 live-out。
    // 内层 loop 的 break/continue 只消费内层控制边，不会绕过外层尾 copy；depth-aware helper
    // 仅在内层没有 goto/label/cleanup 时放行，避免把非结构化跳转误当作局部 transfer。
    // 候选拒绝[SemanticBarrier:Lifetime]：Close/TBC 跨越异槽或未知槽 snapshot 时，
    // 另一 HIR binding 仍可能在 return temp 的 raw home 上持有 resource identity。
    // 候选拒绝[SemanticBarrier:Capture]：捕获 return temp 时，删除其唯一写会让 closure 观察旧值。
    // 候选拒绝[SemanticBarrier:Lifetime]：TBC temp 或非唯一 use/write 仍有额外 epoch/close 观察者。
    // 候选拒绝[PolicyBoundary]：debug temp 是项目选择保留的源码身份。
    if repeat.body.stmts.len() < 2
        || facts.captured_temps.contains(&return_temp)
        || facts.closed_temps.contains(&return_temp)
        || facts
            .debug_temps
            .get(return_temp.index())
            .is_some_and(Option::is_some)
        || facts
            .preserved_bindings
            .contains(&CarryBinding::Temp(return_temp))
        || facts.use_counts.get(&return_temp).copied() != Some(2)
        || facts.write_counts.get(&return_temp).copied() != Some(1)
    {
        return None;
    }
    let copy_index = repeat.body.stmts.len() - 1;
    let producer_index = copy_index - 1;
    let (temp, value) = match &repeat.body.stmts[producer_index] {
        HirStmt::Assign(assign) => match assign_shape(assign) {
            Some((HirLValue::Temp(temp), value)) => (*temp, value.clone()),
            _ => return None,
        },
        _ => return None,
    };
    if temp != return_temp
        || !matches!(
            &repeat.body.stmts[copy_index],
            HirStmt::Assign(assign)
                if matches!(assign_shape(assign), Some((HirLValue::Local(_), HirExpr::TempRef(t))) if *t == temp)
        )
    {
        return None;
    }
    let local = match &repeat.body.stmts[copy_index] {
        HirStmt::Assign(assign) => match assign_shape(assign) {
            Some((HirLValue::Local(local), HirExpr::TempRef(_))) => *local,
            _ => return None,
        },
        _ => return None,
    };
    // 候选拒绝[SemanticBarrier:Scope]：repeat body 内声明的 local 在循环外不可见；把外层 Return 改写到它会生成越界引用。
    if repeat_body_declares_local(&repeat.body, local) {
        return None;
    }
    // 候选拒绝[SemanticBarrier:Capture]：captured local 的 cell 被 closure 观察，合并
    // producer 会改变 closure 可见的写入 epoch。
    // 候选拒绝[PolicyBoundary]：for binding 的迭代 identity 由 loop owner 保留；候选拒绝
    // [SemanticBarrier:Lifetime]：TBC local 的 resource/close identity 不可并入普通 snapshot。
    if facts.captured_locals.contains(&local) || facts.protected_locals.contains(&local) {
        return None;
    }
    if facts
        .preserved_bindings
        .contains(&CarryBinding::Local(local))
    {
        // 候选拒绝[LayerBoundary]：上游 HIR 已证明该 local definition 必须保留；
        // repeat snapshot 不能通过把 temp producer 改写到 local 来改变其写入 epoch。
        return None;
    }
    let cleanup_preserves_raw_home = trusted_same_raw_home_merge(
        promotion_facts.compacts_home_slots(),
        promotion_facts.trusted_temp_home_slot(temp),
        promotion_facts.trusted_local_home_slot(local),
    );
    if stmt_contains_loop_exit(&repeat.body, cleanup_preserves_raw_home) {
        return None;
    }
    let HirStmt::Assign(producer) = &mut repeat.body.stmts[producer_index] else {
        return None;
    };
    producer.targets[0] = HirLValue::Local(local);
    producer.values.fixed[0] = value;
    repeat.body.stmts.remove(copy_index);
    // 目标 local 现在吸收了 temp definition；异槽或未知槽必须立即失效旧 provenance，
    // 后续 carried-local owner 不能继续把它当作原 raw home 的可信身份。
    promotion_facts.record_temp_to_local_merge(temp, local);
    Some(local)
}

fn trusted_same_raw_home_merge(
    compacts_home_slots: bool,
    temp_home: Option<HomeSlotKey>,
    local_home: Option<HomeSlotKey>,
) -> bool {
    !compacts_home_slots && temp_home.is_some() && temp_home == local_home
}

fn assign_shape(assign: &HirAssign) -> Option<(&HirLValue, &HirExpr)> {
    (assign.targets.len() == 1 && assign.values.tail.is_none() && assign.values.fixed.len() == 1)
        .then(|| (&assign.targets[0], &assign.values.fixed[0]))
}

fn repeat_body_declares_local(body: &HirBlock, local: LocalId) -> bool {
    struct LocalDeclarationFinder {
        local: LocalId,
        found: bool,
    }

    impl HirVisitor for LocalDeclarationFinder {
        fn visit_stmt(&mut self, stmt: &HirStmt) {
            self.found |=
                matches!(stmt, HirStmt::LocalDecl(decl) if decl.bindings.contains(&self.local));
        }
    }

    let mut finder = LocalDeclarationFinder {
        local,
        found: false,
    };
    visit_block(body, &mut finder);
    finder.found
}

fn stmt_contains_loop_exit(block: &HirBlock, cleanup_preserves_raw_home: bool) -> bool {
    block
        .stmts
        .iter()
        .any(|stmt| stmt_contains_unsafe_control(stmt, 0, cleanup_preserves_raw_home))
}

/// `break`/`continue` are scoped to the innermost loop.  A nested loop therefore cannot bypass
/// the outer repeat's tail copy; only non-local control and cleanup remain barriers here.
fn stmt_contains_unsafe_control(
    stmt: &HirStmt,
    loop_depth: usize,
    cleanup_preserves_raw_home: bool,
) -> bool {
    match stmt {
        HirStmt::Break | HirStmt::Continue if loop_depth == 0 => true,
        HirStmt::Return(_) | HirStmt::Goto(_) | HirStmt::Label(_) | HirStmt::GlobalDecl(_) => true,
        HirStmt::Close(_) | HirStmt::ToBeClosed(_) => !cleanup_preserves_raw_home,
        HirStmt::Break | HirStmt::Continue => false,
        HirStmt::While(while_stmt) => while_stmt.body.stmts.iter().any(|stmt| {
            stmt_contains_unsafe_control(stmt, loop_depth + 1, cleanup_preserves_raw_home)
        }),
        HirStmt::Repeat(repeat_stmt) => repeat_stmt.body.stmts.iter().any(|stmt| {
            stmt_contains_unsafe_control(stmt, loop_depth + 1, cleanup_preserves_raw_home)
        }),
        HirStmt::NumericFor(numeric_for) => numeric_for.body.stmts.iter().any(|stmt| {
            stmt_contains_unsafe_control(stmt, loop_depth + 1, cleanup_preserves_raw_home)
        }),
        HirStmt::GenericFor(generic_for) => generic_for.body.stmts.iter().any(|stmt| {
            stmt_contains_unsafe_control(stmt, loop_depth + 1, cleanup_preserves_raw_home)
        }),
        HirStmt::If(if_stmt) => {
            if_stmt.then_block.stmts.iter().any(|stmt| {
                stmt_contains_unsafe_control(stmt, loop_depth, cleanup_preserves_raw_home)
            }) || if_stmt.else_block.as_ref().is_some_and(|block| {
                block.stmts.iter().any(|stmt| {
                    stmt_contains_unsafe_control(stmt, loop_depth, cleanup_preserves_raw_home)
                })
            })
        }
        HirStmt::Block(block) => block
            .stmts
            .iter()
            .any(|stmt| stmt_contains_unsafe_control(stmt, loop_depth, cleanup_preserves_raw_home)),
        HirStmt::LocalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::CallStmt(_) => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::common::{HirClose, HirLocalDecl, HirRepeat, HirReturn, HirValuePack};

    fn assign(target: HirLValue, value: HirExpr) -> HirStmt {
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![target],
            values: HirValuePack::fixed(vec![value]),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        }))
    }

    fn repeat_snapshot_body(local: LocalId, declare_local: bool) -> HirBlock {
        let temp = TempId(0);
        let mut stmts = Vec::new();
        if declare_local {
            stmts.push(HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: vec![local],
                values: HirValuePack::fixed(vec![HirExpr::Nil]),
                initializer_merge_transaction: None,
            })));
        }
        stmts.push(assign(HirLValue::Temp(temp), HirExpr::Integer(7)));
        stmts.push(assign(HirLValue::Local(local), HirExpr::TempRef(temp)));
        HirBlock { stmts }
    }

    fn repeat_snapshot_stmt(local: LocalId, declare_local: bool) -> HirStmt {
        HirStmt::Repeat(Box::new(HirRepeat {
            body: repeat_snapshot_body(local, declare_local),
            cond: HirExpr::Boolean(true),
            lifetime: Default::default(),
        }))
    }

    fn return_temp(temp: TempId) -> HirStmt {
        HirStmt::Return(Box::new(HirReturn {
            values: HirValuePack::fixed(vec![HirExpr::TempRef(temp)]),
        }))
    }

    fn with_snapshot_facts(test: impl FnOnce(&RepeatSnapshotFacts<'_>)) {
        let use_counts = BTreeMap::from([(TempId(0), 2)]);
        let write_counts = BTreeMap::from([(TempId(0), 1)]);
        let empty_locals = BTreeSet::new();
        let empty_temps = BTreeSet::new();
        let preserved_bindings = BTreeSet::new();
        let facts = RepeatSnapshotFacts {
            use_counts: &use_counts,
            captured_locals: &empty_locals,
            protected_locals: &empty_locals,
            captured_temps: &empty_temps,
            closed_temps: &empty_temps,
            write_counts: &write_counts,
            debug_temps: &[],
            preserved_bindings: &preserved_bindings,
        };
        test(&facts);
    }

    #[test]
    fn repeat_snapshot_rejects_local_declared_inside_repeat() {
        let local = LocalId(0);
        let mut block = HirBlock {
            stmts: vec![repeat_snapshot_stmt(local, true), return_temp(TempId(0))],
        };
        let before = block.clone();
        let mut promotion_facts = ProtoPromotionFacts::default();
        let physical_root_temps = BTreeSet::new();
        let mut physical_root_locals = BTreeSet::new();

        with_snapshot_facts(|facts| {
            assert!(!rewrite_block(
                &mut block,
                facts,
                &mut promotion_facts,
                &physical_root_temps,
                &mut physical_root_locals,
            ));
        });

        assert_eq!(block, before);
    }

    #[test]
    fn repeat_snapshot_rewrites_local_visible_before_repeat() {
        let local = LocalId(0);
        let mut block = HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![local],
                    values: HirValuePack::fixed(vec![HirExpr::Nil]),
                    initializer_merge_transaction: None,
                })),
                repeat_snapshot_stmt(local, false),
                return_temp(TempId(0)),
            ],
        };
        let mut promotion_facts = ProtoPromotionFacts::default();
        promotion_facts.record_local_home_slot(local, HomeSlotKey::new(1, 0));
        let physical_root_temps = BTreeSet::from([TempId(0)]);
        let mut physical_root_locals = BTreeSet::new();

        with_snapshot_facts(|facts| {
            assert!(rewrite_block(
                &mut block,
                facts,
                &mut promotion_facts,
                &physical_root_temps,
                &mut physical_root_locals,
            ));
        });

        let HirStmt::Repeat(repeat) = &block.stmts[1] else {
            panic!("expected repeat statement");
        };
        assert_eq!(
            repeat.body.stmts,
            vec![assign(HirLValue::Local(local), HirExpr::Integer(7))]
        );
        let HirStmt::Return(ret) = &block.stmts[2] else {
            panic!("expected return statement");
        };
        assert_eq!(ret.values.fixed, vec![HirExpr::LocalRef(local)]);
        assert!(promotion_facts.local_home_was_invalidated(local));
        assert!(physical_root_locals.contains(&local));
    }

    #[test]
    fn cleanup_requires_an_exact_uncompacted_home_match() {
        let home = HomeSlotKey::new(2, 3);
        assert!(trusted_same_raw_home_merge(false, Some(home), Some(home)));
        assert!(!trusted_same_raw_home_merge(true, Some(home), Some(home)));
        assert!(!trusted_same_raw_home_merge(
            false,
            Some(home),
            Some(HomeSlotKey::new(2, 4))
        ));
        assert!(!trusted_same_raw_home_merge(false, Some(home), None));

        let cleanup = HirBlock {
            stmts: vec![HirStmt::Close(Box::new(HirClose { from_reg: 2 }))],
        };
        assert!(stmt_contains_loop_exit(&cleanup, false));
        assert!(!stmt_contains_loop_exit(&cleanup, true));
    }
}
