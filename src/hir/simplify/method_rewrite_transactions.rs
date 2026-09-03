//! 在 HIR fixed point 之后签发 method lookup/call 的双端原子改写事务。
//!
//! low IR/SSA 只提供 method setup 的原始协议和 canonical callee definition；本模块在
//! 最终 HIR 上再次证明 producer/call occurrence、旧 target 根与稳定 alias-chain co-holder。AST 只会
//! 收到不透明 token，不接触 temp、home 或 reaching-def 事实。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirAssign, HirBlock, HirCallExpr, HirExpr, HirLValue, HirMethodRewriteTransactionId, HirProto,
    HirStmt, LocalId,
};
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

use super::mention::{
    stmts_mention_local, stmts_protected_locals, stmts_reference_captured_bindings,
    stmts_tbc_protected_home_slots, stmts_value_captured_bindings, stmts_write_local,
};

#[derive(Clone, Copy)]
struct Candidate {
    assign: usize,
    call: usize,
    transaction: HirMethodRewriteTransactionId,
}

#[derive(Clone, Copy)]
struct DirectAlias {
    source: LocalId,
    stmt_index: usize,
}

pub(super) fn finalize_method_rewrite_transactions(
    proto: &mut HirProto,
    facts: &ProtoPromotionFacts,
) {
    clear_transactions(&mut proto.body);

    let reference_captured = stmts_reference_captured_bindings(&proto.body.stmts);
    let value_captured = stmts_value_captured_bindings(&proto.body.stmts);
    let protected = stmts_protected_locals(&proto.body.stmts);
    let mut barred_homes = captured_binding_homes(&reference_captured, facts);
    barred_homes.extend(captured_binding_homes(&value_captured, facts));
    for local in &protected {
        barred_homes.extend(facts.complete_local_home_slots(*local));
    }
    barred_homes.extend(stmts_tbc_protected_home_slots(&proto.body.stmts, facts));
    let mut candidates = Vec::new();
    collect_candidates(
        &proto.body,
        proto,
        facts,
        &reference_captured.locals,
        &value_captured.locals,
        &protected,
        &barred_homes,
        &mut candidates,
    );

    let mut counts = BTreeMap::new();
    for candidate in &candidates {
        *counts.entry(candidate.transaction).or_insert(0usize) += 1;
    }
    candidates.retain(|candidate| counts.get(&candidate.transaction) == Some(&1));
    install_transactions(&mut proto.body, &candidates);
}

#[allow(clippy::too_many_arguments)]
fn collect_candidates(
    block: &HirBlock,
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    reference_captured: &BTreeSet<LocalId>,
    value_captured: &BTreeSet<LocalId>,
    protected: &BTreeSet<LocalId>,
    barred_homes: &BTreeSet<HomeSlotKey>,
    candidates: &mut Vec<Candidate>,
) {
    let mut aliases = BTreeMap::<LocalId, DirectAlias>::new();
    for (index, stmt) in block.stmts.iter().enumerate() {
        for_each_child_block(stmt, &mut |child| {
            collect_candidates(
                child,
                proto,
                facts,
                reference_captured,
                value_captured,
                protected,
                barred_homes,
                candidates,
            );
        });

        if let Some(candidate) = candidate_at(
            block,
            index,
            &aliases,
            proto,
            facts,
            reference_captured,
            value_captured,
            protected,
            barred_homes,
        ) {
            candidates.push(candidate);
        }

        aliases.retain(|target, source| {
            !super::mention::stmt_writes_local(stmt, *target)
                && !super::mention::stmt_writes_local(stmt, source.source)
        });
        if is_control_boundary(stmt) {
            aliases.clear();
        } else if let Some((target, source)) = direct_local_alias(stmt) {
            aliases.insert(
                target,
                DirectAlias {
                    source,
                    stmt_index: index,
                },
            );
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn candidate_at(
    block: &HirBlock,
    index: usize,
    aliases: &BTreeMap<LocalId, DirectAlias>,
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    reference_captured: &BTreeSet<LocalId>,
    value_captured: &BTreeSet<LocalId>,
    protected: &BTreeSet<LocalId>,
    barred_homes: &BTreeSet<HomeSlotKey>,
) -> Option<Candidate> {
    let [producer, sink] = block.stmts.get(index..index.checked_add(2)?)? else {
        return None;
    };
    let HirStmt::Assign(assign) = producer else {
        return None;
    };
    let [crate::hir::common::HirLValue::Local(target)] = assign.targets.as_slice() else {
        return None;
    };
    let [HirExpr::TableAccess(access)] = assign.values.fixed.as_slice() else {
        return None;
    };
    if assign.values.tail.is_some() || assign.method_rewrite_transaction.is_some() {
        return None;
    }
    let HirExpr::String(method_key) = &access.key else {
        return None;
    };
    let HirStmt::CallStmt(call_stmt) = sink else {
        return None;
    };
    let call = &call_stmt.call;
    let [receiver, ..] = call.args.fixed.as_slice() else {
        return None;
    };
    if call.args.tail.is_some() && call.args.fixed.is_empty() {
        return None;
    }
    let protocol_id =
        super::method_protocol::match_method_setup_pair(access, &HirExpr::LocalRef(*target), call)?;
    if call.method_rewrite_transaction.is_some()
        || call
            .args
            .fixed
            .iter()
            .skip(1)
            .any(|arg| super::mention::expr_mentions_local(arg, *target))
        || call
            .args
            .tail
            .as_ref()
            .is_some_and(|tail| super::mention::expr_mentions_local(tail.as_expr(), *target))
    {
        return None;
    }
    if !matches!(receiver, HirExpr::LocalRef(_) | HirExpr::ParamRef(_)) {
        return None;
    }

    let protocol = facts.method_setup_protocol(protocol_id)?;
    if access.method_setup_protocol != Some(protocol_id)
        || protocol.method_key != *method_key
        || !facts.is_pure_scope_end_copy_root_temp(protocol.prior_callee_root_temp)
    {
        return None;
    }
    let root_homes = facts.complete_temp_home_slots(protocol.prior_callee_root_temp);
    let alias = alias_root_for_homes(*target, aliases, &root_homes, facts)?;
    let source = alias.source;
    if source == *target
        || matches!(receiver, HirExpr::LocalRef(receiver) if receiver == target)
        || reference_captured.contains(target)
        || reference_captured.contains(&source)
        || value_captured.contains(target)
        || value_captured.contains(&source)
        || protected.contains(target)
        || protected.contains(&source)
        || proto.inline_dispositions.local(*target).must_preserve()
        || proto.inline_dispositions.local(source).must_preserve()
        || proto
            .local_debug_hints
            .get(target.index())
            .is_some_and(Option::is_some)
        || proto
            .local_debug_scopes
            .get(target.index())
            .is_some_and(Option::is_some)
        || proto
            .local_debug_hints
            .get(source.index())
            .is_some_and(Option::is_some)
        || proto
            .local_debug_scopes
            .get(source.index())
            .is_some_and(Option::is_some)
    {
        return None;
    }

    let target_homes = facts.complete_local_home_slots(*target);
    let source_homes = facts.complete_local_home_slots(source);
    let (&target_home, &source_home) = (target_homes.iter().next()?, source_homes.iter().next()?);
    let watched_homes = target_homes.union(&source_homes).copied().collect();
    if target_homes.len() != 1
        || source_homes.len() != 1
        || target_home == source_home
        || source_home.slot() >= target_home.slot()
        || !target_homes.is_disjoint(barred_homes)
        || !source_homes.is_disjoint(barred_homes)
        || stmts_may_write_homes(
            &block.stmts[alias.stmt_index + 1..index],
            &watched_homes,
            facts,
        )
        || stmts_mention_local(&block.stmts[index + 2..], *target)
        || stmts_write_local(&block.stmts[index + 2..], source)
    {
        return None;
    }

    if facts.complete_temp_home_slots(protocol.callee_temp) != target_homes
        || root_homes != source_homes
    {
        return None;
    }

    Some(Candidate {
        assign: assign.as_ref() as *const HirAssign as usize,
        call: call as *const HirCallExpr as usize,
        transaction: HirMethodRewriteTransactionId::new(proto.id, protocol_id.index()),
    })
}

fn alias_root_for_homes(
    target: LocalId,
    aliases: &BTreeMap<LocalId, DirectAlias>,
    root_homes: &BTreeSet<HomeSlotKey>,
    facts: &ProtoPromotionFacts,
) -> Option<DirectAlias> {
    let direct = *aliases.get(&target)?;
    let mut current = direct.source;
    let mut visited = BTreeSet::from([target]);

    loop {
        if !visited.insert(current) {
            return None;
        }
        if facts.complete_local_home_slots(current) == *root_homes {
            return Some(DirectAlias {
                source: current,
                stmt_index: direct.stmt_index,
            });
        }
        current = aliases.get(&current)?.source;
    }
}

fn direct_local_alias(stmt: &HirStmt) -> Option<(LocalId, LocalId)> {
    match stmt {
        HirStmt::LocalDecl(decl) => {
            let ([target], [HirExpr::LocalRef(source)]) =
                (decl.bindings.as_slice(), decl.values.fixed.as_slice())
            else {
                return None;
            };
            decl.values.tail.is_none().then_some((*target, *source))
        }
        HirStmt::Assign(assign) => {
            let ([HirLValue::Local(target)], [HirExpr::LocalRef(source)]) =
                (assign.targets.as_slice(), assign.values.fixed.as_slice())
            else {
                return None;
            };
            (assign.values.tail.is_none()
                && assign.initializer_merge_transaction.is_none()
                && assign.generic_for_initializer_producer.is_none()
                && assign.method_rewrite_transaction.is_none())
            .then_some((*target, *source))
        }
        _ => None,
    }
}

fn is_control_boundary(stmt: &HirStmt) -> bool {
    matches!(
        stmt,
        HirStmt::If(_)
            | HirStmt::While(_)
            | HirStmt::Repeat(_)
            | HirStmt::NumericFor(_)
            | HirStmt::GenericFor(_)
            | HirStmt::Break
            | HirStmt::Continue
            | HirStmt::Goto(_)
            | HirStmt::Label(_)
            | HirStmt::Block(_)
    )
}

fn for_each_child_block(stmt: &HirStmt, visit: &mut impl FnMut(&HirBlock)) {
    match stmt {
        HirStmt::If(if_stmt) => {
            visit(&if_stmt.then_block);
            if let Some(else_block) = &if_stmt.else_block {
                visit(else_block);
            }
        }
        HirStmt::While(while_stmt) => visit(&while_stmt.body),
        // repeat condition shares the body's lexical scope. The first conservative transaction
        // version does not certify candidates under that trailing-use boundary.
        HirStmt::Repeat(_) => {}
        HirStmt::NumericFor(for_stmt) => visit(&for_stmt.body),
        HirStmt::GenericFor(for_stmt) => visit(&for_stmt.body),
        HirStmt::Block(block) => visit(block),
        _ => {}
    }
}

fn captured_binding_homes(
    captured: &super::mention::ReferenceCapturedBindings,
    facts: &ProtoPromotionFacts,
) -> BTreeSet<HomeSlotKey> {
    let mut homes = BTreeSet::new();
    for local in &captured.locals {
        homes.extend(facts.complete_local_home_slots(*local));
    }
    for param in &captured.params {
        homes.extend(facts.complete_param_home_slots(*param));
    }
    for temp in &captured.temps {
        homes.extend(facts.complete_temp_home_slots(*temp));
    }
    homes
}

fn stmts_may_write_homes(
    stmts: &[HirStmt],
    watched: &BTreeSet<HomeSlotKey>,
    facts: &ProtoPromotionFacts,
) -> bool {
    let mut collector = WatchedHomeWriteCollector {
        facts,
        watched,
        may_write: false,
    };
    crate::hir::visit::visit_stmts(stmts, &mut collector);
    collector.may_write
}

struct WatchedHomeWriteCollector<'a> {
    facts: &'a ProtoPromotionFacts,
    watched: &'a BTreeSet<HomeSlotKey>,
    may_write: bool,
}

impl WatchedHomeWriteCollector<'_> {
    fn note_homes(&mut self, homes: BTreeSet<HomeSlotKey>) {
        self.may_write |= !homes.is_disjoint(self.watched);
    }
}

impl crate::hir::visit::HirVisitor for WatchedHomeWriteCollector<'_> {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        if let HirStmt::LocalDecl(decl) = stmt {
            for local in &decl.bindings {
                self.note_homes(self.facts.complete_local_definition_write_homes(*local));
            }
        }
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        match lvalue {
            HirLValue::Param(param) => {
                self.note_homes(self.facts.complete_param_definition_write_homes(*param));
            }
            HirLValue::Local(local) => {
                self.note_homes(self.facts.complete_local_definition_write_homes(*local));
            }
            HirLValue::Temp(temp) => {
                self.note_homes(self.facts.complete_temp_definition_write_homes(*temp));
            }
            HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_) => {}
        }
    }
}

fn clear_transactions(block: &mut HirBlock) {
    for stmt in &mut block.stmts {
        match stmt {
            HirStmt::Assign(assign) => assign.method_rewrite_transaction = None,
            HirStmt::CallStmt(call) => call.call.method_rewrite_transaction = None,
            _ => {}
        }
        super::walk::for_each_nested_block_mut(stmt, &mut clear_transactions);
    }
}

fn install_transactions(block: &mut HirBlock, candidates: &[Candidate]) {
    for stmt in &mut block.stmts {
        match stmt {
            HirStmt::Assign(assign) => {
                let address = assign.as_ref() as *const HirAssign as usize;
                if let Some(candidate) = candidates.iter().find(|item| item.assign == address) {
                    assign.method_rewrite_transaction = Some(candidate.transaction);
                }
            }
            HirStmt::CallStmt(call_stmt) => {
                let address = &call_stmt.call as *const HirCallExpr as usize;
                if let Some(candidate) = candidates.iter().find(|item| item.call == address) {
                    call_stmt.call.method_rewrite_transaction = Some(candidate.transaction);
                }
            }
            _ => {}
        }
        super::walk::for_each_nested_block_mut(stmt, &mut |child| {
            install_transactions(child, candidates);
        });
    }
}
