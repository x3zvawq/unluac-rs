//! 恢复带 Boolean 预写及 TESTSET 的短路赋值，保留旧目标的覆盖时点。
//! 从当前控制树、唯一 label 入口和原 home 证明完整赋值帧；不按常量真值删除第二次检查。

use super::*;
use crate::hir::common::{HirBinding, HirInlineRetentionReason, HirLogicalExpr};
use crate::hir::promotion::HomeSlotKey;
use crate::hir::simplify::mention::{BindingReadCollector, BindingWriteCollector};
use crate::hir::simplify::source_frames::{self, PrefixRequest, coordinates};
use crate::hir::visit::visit_stmts;

struct Plan {
    start: usize,
    end: usize,
    home: HomeSlotKey,
    target: LocalId,
    replacement: HirStmt,
}

pub(super) fn restore(
    proto: &mut HirProto,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
) -> bool {
    // 当前帧合同对应 PUC 的 TESTSET：Boolean 在 freereg 预写，成功后才 COPY 到旧目标。
    if matches!(dialect, DecompileDialect::Luau | DecompileDialect::Luajit) {
        return false;
    }
    let labels = count_label_references(&proto.body.stmts);
    let mut reads = BTreeMap::new();
    let mut writes = BTreeMap::new();
    visit_stmts(
        &proto.body.stmts,
        &mut (
            BindingReadCollector(|binding| {
                *reads.entry(binding).or_insert(0usize) += 1;
            }),
            BindingWriteCollector(|binding| {
                *writes.entry(binding).or_insert(0usize) += 1;
            }),
        ),
    );
    let mut plans = Vec::new();
    let mut count = 0;
    collect(
        &proto.body,
        proto,
        facts,
        &labels,
        &reads,
        &writes,
        &mut count,
        &mut plans,
    );
    if plans.is_empty() {
        return false;
    }
    let requests = plans
        .iter()
        .map(|plan| {
            (
                plan.start,
                PrefixRequest {
                    home: plan.home,
                    required: BTreeSet::from([plan.target]),
                },
            )
        })
        .collect();
    let Ok(preserved) = source_frames::validate_prefixes(
        proto,
        facts,
        dialect,
        proto.id.index() == 0,
        &vec![false; count],
        &requests,
        false,
    ) else {
        // 候选拒绝[ProofIncomplete:FramePrefix]：trusted home 不替代当前源码声明前缀。
        return false;
    };
    let mut removed = vec![false; count];
    let mut replacements = BTreeMap::new();
    for plan in plans {
        removed[plan.start + 1..plan.end].fill(true);
        replacements.insert(plan.start, plan.replacement);
    }
    apply(&mut proto.body, &mut 0, &removed, &mut replacements);
    for local in preserved {
        proto
            .inline_dispositions
            .preserve_local(local, HirInlineRetentionReason::PhysicalFramePrefix);
    }
    true
}

fn apply(
    block: &mut HirBlock,
    cursor: &mut usize,
    removed: &[bool],
    replacements: &mut BTreeMap<usize, HirStmt>,
) {
    block.stmts.retain_mut(|stmt| {
        let index = *cursor;
        *cursor += 1;
        // 子树先消费原坐标，再替换父语句；删除一段控制树不能改变后缀的事务索引。
        super::super::walk::for_each_nested_block_mut(stmt, &mut |child| {
            apply(child, cursor, removed, replacements)
        });
        if matches!(stmt, HirStmt::Repeat(_)) {
            *cursor += 1;
        }
        if let Some(value) = replacements.remove(&index) {
            *stmt = value;
        }
        !removed[index]
    });
}

#[expect(
    clippy::too_many_arguments,
    reason = "候选共用本轮 binding、label 和源码坐标索引"
)]
fn collect(
    block: &HirBlock,
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    labels: &BTreeMap<HirLabelId, usize>,
    reads: &BTreeMap<HirBinding, usize>,
    writes: &BTreeMap<HirBinding, usize>,
    cursor: &mut usize,
    plans: &mut Vec<Plan>,
) {
    let mut consumed = 0;
    for (index, stmt) in block.stmts.iter().enumerate() {
        let start = *cursor;
        if index >= consumed
            && let Some((home, target, replacement)) =
                candidate(&block.stmts[index..], proto, facts, labels, reads, writes)
        {
            let mut end = start;
            for value in &block.stmts[index..index + 3] {
                end += 1;
                crate::hir::visit::for_each_nested_block(value, &mut |child| {
                    coordinates::visit(child, &mut end, &mut |_, _, _| {});
                });
            }
            plans.push(Plan {
                start,
                end,
                home,
                target,
                replacement,
            });
            consumed = index + 3;
        }
        *cursor += 1;
        crate::hir::visit::for_each_nested_block(stmt, &mut |child| {
            if index < consumed {
                coordinates::visit(child, cursor, &mut |_, _, _| {});
            } else {
                collect(child, proto, facts, labels, reads, writes, cursor, plans);
            }
        });
        if matches!(stmt, HirStmt::Repeat(_)) {
            *cursor += 1;
        }
    }
}

fn candidate(
    stmts: &[HirStmt],
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    labels: &BTreeMap<HirLabelId, usize>,
    reads: &BTreeMap<HirBinding, usize>,
    writes: &BTreeMap<HirBinding, usize>,
) -> Option<(HomeSlotKey, LocalId, HirStmt)> {
    let [
        HirStmt::If(outer),
        HirStmt::Assign(fallback),
        HirStmt::Label(label),
        ..,
    ] = stmts
    else {
        return None;
    };
    let [HirStmt::LocalDecl(decl), HirStmt::If(inner)] = outer.then_block.stmts.as_slice() else {
        return None;
    };
    let [HirStmt::Assign(success), HirStmt::Goto(join)] = inner.then_block.stmts.as_slice() else {
        return None;
    };
    let ([guard], [HirExpr::Boolean(true)], None) = (
        decl.bindings.as_slice(),
        decl.values.fixed.as_slice(),
        &decl.values.tail,
    ) else {
        return None;
    };
    let ([HirLValue::Local(target)], [HirExpr::Boolean(false)], None) = (
        fallback.targets.as_slice(),
        fallback.values.fixed.as_slice(),
        &fallback.values.tail,
    ) else {
        return None;
    };
    if has_non_empty_else(outer)
        || has_non_empty_else(inner)
        || outer.preserves_empty_test
        || inner.preserves_empty_test
        || !matches!(inner.cond, HirExpr::LocalRef(local) if local == *guard)
        || join.target != label.id
        || labels.get(&label.id) != Some(&1)
        || !label.tbc_barriers.is_empty()
        || !label.entry_cleanup.is_empty()
        || proto.local_debug_hints[guard.index()].is_some()
        || proto.local_debug_scopes[guard.index()].is_some()
        || decl.initializer_merge_transaction.is_some()
        || reads.get(&HirBinding::Local(*guard)) != Some(&1)
        || writes.get(&HirBinding::Local(*guard)) != Some(&1)
        || success.targets != fallback.targets
        || success.values.tail.is_some()
        || success.values.fixed.as_slice() != [HirExpr::Boolean(true)]
        || success.initializer_merge_transaction.is_some()
        || fallback.initializer_merge_transaction.is_some()
        || [success, fallback].iter().any(|assign| {
            assign.luau_compound_global
                || assign.upvalue_write_source.is_some()
                || assign.is_phi_transfer
                || assign.preserves_parallel_nil()
                || assign.generic_for_initializer_producer.is_some()
                || assign.generic_for_dispatch_release.is_some()
                || assign.method_rewrite_transaction.is_some()
        })
    {
        return None;
    }
    let home = facts.trusted_local_home_slot(*guard)?;
    let target_home = facts.trusted_local_home_slot(*target)?;
    let input_home = match outer.cond {
        HirExpr::ParamRef(param) => facts.trusted_param_home_slot(param)?,
        HirExpr::LocalRef(local) => facts.trusted_local_home_slot(local)?,
        _ => return None,
    };
    if input_home.slot() >= home.slot() || target_home.slot() >= home.slot() {
        return None;
    }
    let value = HirExpr::LogicalOr(Box::new(HirLogicalExpr {
        preserves_boolean_prewrite: true,
        lhs: HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
            preserves_boolean_prewrite: true,
            lhs: outer.cond.clone(),
            rhs: HirExpr::Boolean(true),
        })),
        rhs: HirExpr::Boolean(false),
    }));
    let mut replacement = fallback.as_ref().clone();
    replacement.values = HirValuePack::fixed(vec![value]);
    Some((home, *target, HirStmt::Assign(Box::new(replacement))))
}
