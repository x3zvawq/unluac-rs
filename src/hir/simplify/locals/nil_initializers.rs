//! 把连续 nil 初始化接回同槽的合流声明，保留原写入位置与物理根。
//! 只合并无观察者的匿名 seed；debug/capture 身份和有实际求值的间隔不参与。

use super::*;
use crate::hir::common::{HirInlineDisposition, HirInlineRetentionReason};
use crate::hir::simplify::mention::stmts_mentioned_locals;
use crate::hir::simplify::walk::{HirRewritePass, rewrite_proto};

pub(super) fn restore(proto: &mut HirProto, facts: &mut ProtoPromotionFacts) -> bool {
    let mut mentioned = stmts_mentioned_locals(&proto.body.stmts);
    mentioned.extend((0..proto.local_count).map(LocalId).filter(|local| {
        matches!(proto.inline_dispositions.local(*local), HirInlineDisposition::Preserve(reasons)
            if reasons.iter().any(|reason| *reason != HirInlineRetentionReason::PhysicalFramePrefix))
    }));
    let debug = proto
        .local_debug_hints
        .iter()
        .enumerate()
        .filter_map(|(index, hint)| hint.is_some().then_some(LocalId(index)))
        .chain(
            proto
                .local_debug_scopes
                .iter()
                .enumerate()
                .filter_map(|(index, scope)| scope.is_some().then_some(LocalId(index))),
        )
        .collect();
    let mut pass = Restore {
        facts,
        mentioned,
        debug,
        merges: Vec::new(),
    };
    let changed = rewrite_proto(proto, &mut pass);
    for (seed, target) in pass.merges {
        // 声明仍在原 NIL 写点，保活约束随同一个 home 的身份一起转移。
        if proto.physical_root_locals.remove(&seed) {
            proto.physical_root_locals.insert(target);
        }
        if let HirInlineDisposition::Preserve(reasons) =
            proto.inline_dispositions.local(seed).clone()
        {
            for reason in reasons {
                proto.inline_dispositions.preserve_local(target, reason);
            }
        }
        let homes = facts
            .supplemental_local_definition_write_homes(seed)
            .into_owned();
        facts.merge_local_definition_write_homes(target, homes);
    }
    changed
}

struct Restore<'a> {
    facts: &'a ProtoPromotionFacts,
    mentioned: BTreeSet<LocalId>,
    debug: BTreeSet<LocalId>,
    merges: Vec<(LocalId, LocalId)>,
}

impl HirRewritePass for Restore<'_> {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        let mut seeds = BTreeMap::new();
        let mut replacements = Vec::new();
        let mut removed = BTreeSet::new();
        for (index, stmt) in block.stmts.iter().enumerate() {
            let HirStmt::LocalDecl(decl) = stmt else {
                seeds.clear();
                continue;
            };
            let [local] = decl.bindings.as_slice() else {
                seeds.clear();
                continue;
            };
            let Some(home) = self.facts.trusted_local_home_slot(*local) else {
                seeds.clear();
                continue;
            };
            if decl.initializer_merge_transaction.is_some() || self.debug.contains(local) {
                seeds.clear();
                continue;
            }
            if decl.values.tail.is_none() && decl.values.fixed == [HirExpr::Nil] {
                seeds.remove(&home);
                if !self.mentioned.contains(local) {
                    seeds.insert(home, (index, *local));
                }
            } else if decl.values.is_empty() {
                if let Some((seed_index, seed)) = seeds.remove(&home) {
                    replacements.push((seed_index, *local));
                    removed.insert(index);
                    self.merges.push((seed, *local));
                }
            } else {
                // 候选拒绝[SemanticBarrier:EvaluationOrder]：只跨过无读取的 nil 声明。
                seeds.clear();
            }
        }
        for (index, target) in replacements {
            let HirStmt::LocalDecl(decl) = &mut block.stmts[index] else {
                unreachable!()
            };
            decl.bindings[0] = target;
        }
        let mut index = 0;
        block.stmts.retain(|_| {
            let keep = !removed.contains(&index);
            index += 1;
            keep
        });
        !removed.is_empty()
    }
}
