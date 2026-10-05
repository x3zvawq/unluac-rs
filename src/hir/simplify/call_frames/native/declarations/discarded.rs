//! 恢复保留标量结果、继续求值丢弃表开放尾的完整声明帧。
//! 原 home 与 FrameBuilder 证明连续准备和求值事件；未使用身份退休仍由整批前缀事务验证。

use super::*;

fn scalar(stmt: &HirStmt) -> Option<(LocalId, &HirExpr)> {
    let HirStmt::LocalDecl(decl) = stmt else {
        return None;
    };
    if decl.initializer_merge_transaction.is_some()
        || decl.generic_for_initializer_producer.is_some()
    {
        return None;
    }
    scalar_local(stmt)
}

pub(in crate::hir::simplify::call_frames::native) fn collect(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    flat: &[Option<FlatStmt<'_>>],
) -> Vec<Plan> {
    let mut reads = BTreeSet::new();
    let mut writes = BTreeMap::new();
    visit_stmts(
        &context.proto.body.stmts,
        &mut (
            BindingReadCollector(|binding| {
                reads.insert(binding);
            }),
            BindingWriteCollector(|binding| {
                *writes.entry(binding).or_insert(0usize) += 1;
            }),
        ),
    );
    // 候选拒绝[ProofIncomplete:Binding]：debug 身份、捕获或其它保留原因不能作为匿名 RHS 退休。
    let eligible = |local: LocalId| {
        let home = facts.trusted_local_home_slot(local)?;
        (writes.get(&HirBinding::Local(local)) == Some(&1)
            && context.proto.local_debug_hints[local.index()].is_none()
            && context.proto.local_debug_scopes[local.index()].is_none()
            && !context.closed.contains(&home) && !context.barred.contains(&home)
            && facts.local_definitions_reference_unaliased(local)
            && !matches!(context.proto.inline_dispositions.local(local),
                crate::hir::common::HirInlineDisposition::Preserve(reasons)
                if reasons.iter().any(|reason| *reason != HirInlineRetentionReason::PhysicalFramePrefix)))
        .then_some(home)
    };
    let mut plans = Vec::new();
    let mut cursor = 0;
    while cursor < flat.len() {
        let start = cursor;
        cursor += 1;
        let Some(entry) = flat[start] else {
            continue;
        };
        let Some((result, HirExpr::LocalRef(input))) = scalar(entry.stmt) else {
            continue;
        };
        let Some(base) = eligible(result) else {
            continue;
        };
        if !reads.contains(&HirBinding::Local(result))
            || facts
                .trusted_local_home_slot(*input)
                .is_none_or(|home| home.slot() >= base.slot())
        {
            continue;
        }
        let mut last = None;
        while let Some(Some(next)) = flat.get(cursor) {
            let Some((local, value)) = scalar(next.stmt) else {
                break;
            };
            // 候选拒绝[SemanticBarrier:Scope]：结果声明后移时，RHS 不能读取尚未进入作用域的结果。
            if reads.contains(&HirBinding::Local(local))
                || eligible(local).is_none_or(|home| home.slot() != base.slot() + cursor - start)
                || crate::hir::visit::any_expr(value, &mut |expr| {
                    *expr == HirExpr::LocalRef(result)
                })
            {
                break;
            }
            last = Some(value);
            cursor += 1;
        }
        if !matches!(last, Some(HirExpr::TableConstructor(table)) if table.trailing_multivalue.is_some())
        {
            continue;
        }
        // 每个窗口只建一次 Def 索引；拒绝后不从内部逐项重试增长的前缀。
        let run = flat[start..cursor]
            .iter()
            .map(|entry| entry.unwrap().stmt)
            .collect::<Vec<_>>();
        let candidate = (|| {
            // 候选拒绝[ProofIncomplete:Frame]：仅有相邻声明和连续 home 不够，原 Def 与全部事件也须匹配。
            let mut builder = frame_builder(context, &run, facts, dialect, base.slot())?;
            let mut values = Vec::with_capacity(run.len());
            for (offset, stmt) in run.iter().enumerate() {
                let (_, value) = scalar(stmt)?;
                values.push(builder.expr(
                    value,
                    offset,
                    base.slot() + offset,
                    None,
                    false,
                    true,
                    None,
                )?);
                builder.finish_event(offset)?;
            }
            if builder.first_event != Some(0) || builder.next_event != run.len() {
                return None;
            }
            Some(Plan {
                prefix_at_sink: false,
                luau_function_declaration: false,
                start: entry.id,
                sink: flat[cursor - 1]?.id,
                base,
                values: values.into(),
                result_locals: vec![result],
                assignment_targets: Vec::new(),
                luau_compound_global: false,
                indexed_target: None,
                continuing_root: None,
                retained_copies: Vec::new(),
                replayed_effects: Vec::new(),
                removed: flat[start..cursor - 1]
                    .iter()
                    .map(|entry| entry.unwrap().id)
                    .collect(),
            })
        })();
        plans.extend(candidate);
    }
    plans
}
