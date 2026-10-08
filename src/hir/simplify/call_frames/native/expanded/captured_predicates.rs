//! 恢复捕获更新后、由原字面量定义驱动的条件调用。
//!
//! 消费原 TEST 身份和唯一输入 Def；原更新、字面量及声明前缀作为同一事务提交。

use super::*;
use crate::hir::luau_inlining::{increment_identity_template, small_integer};
use crate::hir::simplify::mention::{BindingReadCollector, BindingWriteCollector};
use crate::hir::simplify::walk::HirRewritePass;

#[derive(Clone, Copy)]
struct Template {
    local: LocalId,
    child: crate::hir::HirProtoRef,
    root: usize,
    creation: crate::hir::HirSourceSite,
}

struct Candidate {
    start: usize,
    condition: HirExpr,
    template: Template,
    capture: LocalId,
    increment: i64,
    source: crate::hir::HirSourceSite,
    home: HomeSlotKey,
}

struct Rewriter<'a> {
    proto: &'a HirProto,
    facts: &'a ProtoPromotionFacts,
    templates: &'a BTreeMap<(LocalId, i64), Option<Template>>,
    reads: &'a BTreeMap<HirBinding, usize>,
    writes: &'a BTreeMap<HirBinding, usize>,
    root: usize,
    certificates: BTreeMap<LocalId, HirRequiredLuauInlining>,
    frames: BTreeMap<crate::hir::HirSourceSite, HomeSlotKey>,
}

impl Rewriter<'_> {
    fn candidate(&self, stmts: &[HirStmt], index: usize) -> Option<Candidate> {
        let HirStmt::If(branch) = &stmts[index] else {
            return None;
        };
        let predicate = branch.predicate_source?;
        let literal = self.facts.literal_predicate(predicate)?;
        // 候选拒绝[ProofIncomplete:BindingIdentity]：只退休该 TEST 唯一读取的匿名定义，不借同槽局部猜输入。
        let (literal_start, value, inverted) = match &branch.cond {
            HirExpr::Boolean(value) => (index, literal.value, *value != literal.value),
            HirExpr::LocalRef(local) => {
                let prior = index.checked_sub(1)?;
                if scalar_local(&stmts[prior]) != Some((*local, &HirExpr::Boolean(literal.value)))
                    || self.facts.promoted_local_for_temp(literal.input) != Some(*local)
                    || self.facts.trusted_local_home_slot(*local) != Some(literal.home)
                    || self.reads.get(&HirBinding::Local(*local)) != Some(&1)
                    || self.writes.get(&HirBinding::Local(*local)) != Some(&1)
                    || self.proto.local_debug_hints[local.index()].is_some()
                    || self.proto.local_debug_scopes[local.index()].is_some()
                {
                    return None;
                }
                (prior, literal.value, false)
            }
            _ => return None,
        };
        if self.proto.temp_debug_locals[literal.input.index()].is_some()
            || self.proto.temp_debug_scopes[literal.input.index()].is_some()
        {
            return None;
        }
        let update = literal_start.checked_sub(1)?;
        let (capture, HirExpr::Binary(add)) = scalar_local(&stmts[update])? else {
            return None;
        };
        let source = add.source_site?;
        let increment = small_integer(&add.rhs)?;
        let template = (*self.templates.get(&(capture, increment))?)?;
        let home = self.facts.trusted_local_home_slot(capture)?;
        // 候选拒绝[ProofIncomplete:Frame]：更新、字面量 Def 和 TEST 须保留原连续事件及各自 home。
        if template.root >= self.root
            || template.creation.proto != source.proto
            || template.creation.instr.index() >= source.instr.index()
            || source.proto != predicate.proto
            || source.instr.index() + 1 != literal.definition.index()
            || literal.definition.index() + 1 != predicate.instr.index()
            || !matches!(&stmts[update], HirStmt::Assign(assign) if !assign.is_phi_transfer && assign.initializer_merge_transaction.is_none())
            || add.op != crate::hir::HirBinaryOpKind::Add
            || add.lhs != HirExpr::LocalRef(capture)
            || self.facts.operation_result_home(source) != Some(home)
            || !self
                .facts
                .native_binary_layout(add)
                .is_some_and(|layout| layout.lhs == Some(home) && layout.rhs.is_none())
            || home.slot() >= literal.home.slot()
        {
            return None;
        }
        let call = factories::factory_call(
            template.local,
            Some(source),
            vec![HirExpr::Boolean(value)].into(),
        );
        let cond = if inverted { call.negate() } else { call };
        Some(Candidate {
            start: update,
            condition: cond,
            template,
            capture,
            increment,
            source,
            home: literal.home,
        })
    }
}

impl HirRewritePass for Rewriter<'_> {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        let mut removed = BTreeSet::new();
        for index in 0..block.stmts.len() {
            let Some(Candidate {
                start,
                condition: cond,
                template,
                capture,
                increment,
                source,
                home,
            }) = self.candidate(&block.stmts, index)
            else {
                continue;
            };
            if (start..index).any(|index| removed.contains(&index)) {
                continue;
            }
            let HirStmt::If(branch) = &mut block.stmts[index] else {
                unreachable!()
            };
            branch.cond = cond;
            removed.extend(start..index);
            let certificate = self.certificates.entry(template.local).or_insert_with(|| {
                HirRequiredLuauInlining {
                    owner: self.proto.id,
                    callee: template.local,
                    child: template.child,
                    field: "".into(),
                    body: HirLuauInliningBody::CapturedIncrementIdentity { increment },
                    capture: Some(capture),
                    occurrences: Vec::new(),
                    result_frames: BTreeMap::new(),
                    callable_arguments: Default::default(),
                    nil_guards: Default::default(),
                }
            });
            certificate.occurrences.push(source);
            certificate.result_frames.insert(
                source,
                crate::hir::HirLuauResultFrame {
                    base: home.slot(),
                    width: 1,
                },
            );
            self.frames.insert(source, home);
        }
        if removed.is_empty() {
            return false;
        }
        let mut index = 0;
        block.stmts.retain(|_| {
            let keep = !removed.contains(&index);
            index += 1;
            keep
        });
        true
    }
}

pub(super) fn restore(module: &mut HirModule, promotion: &mut [ProtoPromotionFacts]) {
    let bodies = module
        .protos
        .iter()
        .map(increment_identity_template)
        .collect::<Vec<_>>();
    if bodies.iter().all(Option::is_none) {
        return;
    }
    for original in &mut module.protos {
        let facts = &promotion[original.id.index()];
        let mut reads = BTreeMap::new();
        let mut writes = BTreeMap::new();
        visit_stmts(
            &original.body.stmts,
            &mut (
                BindingReadCollector(|binding| *reads.entry(binding).or_insert(0) += 1),
                BindingWriteCollector(|binding| *writes.entry(binding).or_insert(0) += 1),
            ),
        );
        let mut templates = BTreeMap::new();
        for (root, stmt) in original.body.stmts.iter().enumerate() {
            let Some((local, HirExpr::Closure(closure))) = scalar_local(stmt) else {
                continue;
            };
            let Some(increment) = bodies[closure.proto.index()] else {
                continue;
            };
            let [capture] = closure.captures.as_slice() else {
                continue;
            };
            let HirBinding::Local(captured) = capture.binding else {
                continue;
            };
            let Some(creation) = closure.source_site else {
                continue;
            };
            if capture.mode != HirCaptureMode::ByReference
                || writes.get(&HirBinding::Local(local)) != Some(&1)
                || reads.contains_key(&HirBinding::Local(local))
            {
                continue;
            }
            templates
                .entry((captured, increment))
                .and_modify(|known| *known = None)
                .or_insert(Some(Template {
                    local,
                    child: closure.proto,
                    root,
                    creation,
                }));
        }
        if templates.is_empty() {
            continue;
        }
        let mut proto = original.clone();
        let mut rewrite = Rewriter {
            proto: original,
            facts,
            templates: &templates,
            reads: &reads,
            writes: &writes,
            root: 0,
            certificates: BTreeMap::new(),
            frames: BTreeMap::new(),
        };
        // 根声明支配其后语句内的全部嵌套块；不从原指令序号推断词法支配。
        for (index, stmt) in proto.body.stmts.iter_mut().enumerate() {
            rewrite.root = index;
            crate::hir::simplify::walk::rewrite_stmts(std::slice::from_mut(stmt), &mut rewrite);
        }
        if rewrite.certificates.is_empty() {
            continue;
        }
        let certificates = rewrite.certificates;
        let sites = rewrite.frames;
        let mut requests = BTreeMap::new();
        let mut count = 0;
        let mut seen = BTreeSet::new();
        prefix::coordinates::visit(&proto.body, &mut count, &mut |index, kind, stmt| {
            if kind != PointKind::Statement {
                return;
            }
            if let HirStmt::If(branch) = stmt {
                crate::hir::visit::any_expr(&branch.cond, &mut |expr| {
                    if let HirExpr::Call(call) = expr
                        && let Some(site) = call.required_luau_inlining
                        && let Some(&home) = sites.get(&site)
                        && seen.insert(site)
                    {
                        requests.insert(
                            index,
                            prefix::PrefixRequest {
                                home,
                                required: BTreeSet::new(),
                            },
                        );
                    }
                    false
                });
            }
        });
        if seen.len() != sites.len() {
            continue;
        }
        // 候选拒绝[ProofIncomplete:Prefix]：恢复调用的条件槽仍须匹配整个当前词法前缀。
        let Ok(preserved) = prefix::validate_prefixes(
            &proto,
            facts,
            DecompileDialect::Luau,
            proto.id == module.entry,
            &vec![false; count],
            &requests,
            false,
        ) else {
            continue;
        };
        for local in preserved.into_iter().chain(certificates.keys().copied()) {
            proto
                .inline_dispositions
                .preserve_local(local, HirInlineRetentionReason::PhysicalFramePrefix);
        }
        *original = proto;
        module
            .required_luau_inlining
            .extend(certificates.into_values());
    }
}
