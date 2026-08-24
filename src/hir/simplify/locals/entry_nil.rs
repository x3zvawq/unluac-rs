//! 裁剪 Structure 为同槽 `Entry(nil)` region-result phi 物化出的冗余 nil 边写入。
//!
//! 依赖 promotion facts 保留 direct canonical phi provenance，并在 temp 提升为空 local 后
//! 执行；不推断普通源码赋值，也不跨循环、退出、goto、cleanup 或残留 Decision。输入例如
//! `local x; if a then x = 1 else x = nil end`，只有 else 入口仍确定为 nil 时才删除写入。

use crate::hir::common::{
    HirAssign, HirBlock, HirExpr, HirIf, HirLValue, HirProto, HirStmt, LocalId,
};
use crate::hir::promotion::ProtoPromotionFacts;

use super::super::mention::{
    ReferenceCapturedBindings, stmts_reference_captured_bindings, stmts_value_captured_bindings,
};
use super::super::visit::{HirVisitor, visit_block, visit_expr, visit_stmts};

#[derive(Clone, Copy, Eq, PartialEq)]
enum NilState {
    KnownNil,
    Unknown,
}

pub(super) fn prune_redundant_entry_nil_writes(
    proto: &mut HirProto,
    facts: &mut ProtoPromotionFacts,
) -> bool {
    if facts.compacts_home_slots() || proto.body.stmts.len() < 2 {
        return false;
    }

    let reference_captured = stmts_reference_captured_bindings(&proto.body.stmts);
    let value_captured = stmts_value_captured_bindings(&proto.body.stmts);
    let to_be_closed = to_be_closed_bindings(&proto.body.stmts);
    let debug_identity = debug_identity_bindings(proto);
    let mut changed = false;

    for index in 0..proto.body.stmts.len() - 1 {
        let Some(local) = empty_local(&proto.body.stmts[index]) else {
            continue;
        };
        if !facts.is_entry_nil_phi_local(local)
            || facts.trusted_local_home_slot(local).is_none()
            || bindings_may_alias_local(&reference_captured, local, facts)
            || bindings_may_alias_local(&value_captured, local, facts)
            || bindings_may_alias_local(&to_be_closed, local, facts)
            || bindings_may_alias_local(&debug_identity, local, facts)
            || proto
                .local_debug_hints
                .get(local.index())
                .is_some_and(Option::is_some)
        {
            continue;
        }
        let HirStmt::If(if_stmt) = &proto.body.stmts[index + 1] else {
            continue;
        };
        if !if_region_is_supported(if_stmt, local) {
            continue;
        }

        let mut rewritten = (**if_stmt).clone();
        let Some((_, candidate_changed)) = prune_if(&mut rewritten, local, NilState::KnownNil)
        else {
            continue;
        };
        if candidate_changed {
            proto.body.stmts[index + 1] = HirStmt::If(Box::new(rewritten));
            facts.mark_entry_nil_writes_pruned(local);
            changed = true;
        }
    }
    changed
}

fn empty_local(stmt: &HirStmt) -> Option<LocalId> {
    let HirStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    let [local] = local_decl.bindings.as_slice() else {
        return None;
    };
    local_decl.values.is_empty().then_some(*local)
}

fn prune_if(if_stmt: &mut HirIf, local: LocalId, incoming: NilState) -> Option<(NilState, bool)> {
    let (then_state, then_changed) = prune_block(&mut if_stmt.then_block, local, incoming)?;
    let (else_state, else_changed) = if let Some(else_block) = &mut if_stmt.else_block {
        prune_block(else_block, local, incoming)?
    } else {
        (incoming, false)
    };
    Some((
        if then_state == NilState::KnownNil && else_state == NilState::KnownNil {
            NilState::KnownNil
        } else {
            NilState::Unknown
        },
        then_changed || else_changed,
    ))
}

fn prune_block(
    block: &mut HirBlock,
    local: LocalId,
    mut state: NilState,
) -> Option<(NilState, bool)> {
    let mut changed = false;
    let mut rewritten = Vec::with_capacity(block.stmts.len());
    for mut stmt in std::mem::take(&mut block.stmts) {
        match &mut stmt {
            HirStmt::Assign(assign) => match local_assignment(assign, local) {
                LocalAssignment::None => {}
                LocalAssignment::Nil if state == NilState::KnownNil => {
                    changed = true;
                    continue;
                }
                LocalAssignment::Nil => state = NilState::KnownNil,
                LocalAssignment::Unknown => state = NilState::Unknown,
            },
            HirStmt::If(if_stmt) => {
                let (next, nested_changed) = prune_if(if_stmt, local, state)?;
                state = next;
                changed |= nested_changed;
            }
            HirStmt::Block(nested) => {
                let (next, nested_changed) = prune_block(nested, local, state)?;
                state = next;
                changed |= nested_changed;
            }
            HirStmt::LocalDecl(local_decl) if local_decl.bindings.contains(&local) => return None,
            HirStmt::LocalDecl(_)
            | HirStmt::TableSetList(_)
            | HirStmt::ErrNil(_)
            | HirStmt::CallStmt(_) => {}
            HirStmt::ToBeClosed(_)
            | HirStmt::Close(_)
            | HirStmt::Return(_)
            | HirStmt::While(_)
            | HirStmt::Repeat(_)
            | HirStmt::NumericFor(_)
            | HirStmt::GenericFor(_)
            | HirStmt::Break
            | HirStmt::Continue
            | HirStmt::Goto(_)
            | HirStmt::Label(_) => return None,
        }
        rewritten.push(stmt);
    }
    block.stmts = rewritten;
    Some((state, changed))
}

enum LocalAssignment {
    None,
    Nil,
    Unknown,
}

fn local_assignment(assign: &HirAssign, local: LocalId) -> LocalAssignment {
    if !assign
        .targets
        .iter()
        .any(|target| target == &HirLValue::Local(local))
    {
        return LocalAssignment::None;
    }
    if matches!(assign.targets.as_slice(), [HirLValue::Local(target)] if *target == local)
        && matches!(assign.values.fixed.as_slice(), [HirExpr::Nil])
        && assign.values.tail.is_none()
    {
        LocalAssignment::Nil
    } else {
        LocalAssignment::Unknown
    }
}

fn if_region_is_supported(if_stmt: &HirIf, local: LocalId) -> bool {
    let mut collector = UnsupportedRegionCollector {
        local,
        unsupported: false,
    };
    visit_expr(&if_stmt.cond, &mut collector);
    visit_block(&if_stmt.then_block, &mut collector);
    if let Some(else_block) = &if_stmt.else_block {
        visit_block(else_block, &mut collector);
    }
    !collector.unsupported
}

struct UnsupportedRegionCollector {
    local: LocalId,
    unsupported: bool,
}

impl HirVisitor for UnsupportedRegionCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        self.unsupported |= match stmt {
            HirStmt::LocalDecl(local_decl) => local_decl.bindings.contains(&self.local),
            HirStmt::ToBeClosed(_)
            | HirStmt::Close(_)
            | HirStmt::Return(_)
            | HirStmt::While(_)
            | HirStmt::Repeat(_)
            | HirStmt::NumericFor(_)
            | HirStmt::GenericFor(_)
            | HirStmt::Break
            | HirStmt::Continue
            | HirStmt::Goto(_)
            | HirStmt::Label(_) => true,
            HirStmt::Assign(_)
            | HirStmt::TableSetList(_)
            | HirStmt::ErrNil(_)
            | HirStmt::CallStmt(_)
            | HirStmt::If(_)
            | HirStmt::Block(_) => false,
        };
    }

    fn visit_expr(&mut self, expr: &HirExpr) {
        self.unsupported |= matches!(expr, HirExpr::Decision(_) | HirExpr::Unresolved(_));
    }
}

fn to_be_closed_bindings(stmts: &[HirStmt]) -> ReferenceCapturedBindings {
    struct Collector {
        bindings: ReferenceCapturedBindings,
    }

    impl HirVisitor for Collector {
        fn visit_stmt(&mut self, stmt: &HirStmt) {
            let HirStmt::ToBeClosed(to_be_closed) = stmt else {
                return;
            };
            visit_expr(
                &to_be_closed.value,
                &mut BindingCollector {
                    bindings: &mut self.bindings,
                },
            );
        }
    }

    let mut collector = Collector {
        bindings: ReferenceCapturedBindings::default(),
    };
    visit_stmts(stmts, &mut collector);
    collector.bindings
}

struct BindingCollector<'a> {
    bindings: &'a mut ReferenceCapturedBindings,
}

impl HirVisitor for BindingCollector<'_> {
    fn visit_expr(&mut self, expr: &HirExpr) {
        match expr {
            HirExpr::LocalRef(local) => {
                self.bindings.locals.insert(*local);
            }
            HirExpr::ParamRef(param) => {
                self.bindings.params.insert(*param);
            }
            HirExpr::TempRef(temp) => {
                self.bindings.temps.insert(*temp);
            }
            HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::Int64(_)
            | HirExpr::UInt64(_)
            | HirExpr::Complex { .. }
            | HirExpr::Vector(_)
            | HirExpr::UpvalueRef(_)
            | HirExpr::GlobalRef(_)
            | HirExpr::TableAccess(_)
            | HirExpr::Unary(_)
            | HirExpr::Binary(_)
            | HirExpr::LogicalAnd(_)
            | HirExpr::LogicalOr(_)
            | HirExpr::Decision(_)
            | HirExpr::Call(_)
            | HirExpr::VarArg
            | HirExpr::TableConstructor(_)
            | HirExpr::Closure(_)
            | HirExpr::Unresolved(_) => {}
        }
    }
}

fn debug_identity_bindings(proto: &HirProto) -> ReferenceCapturedBindings {
    let mut bindings = ReferenceCapturedBindings::default();
    bindings.locals.extend(
        proto
            .locals
            .iter()
            .copied()
            .zip(&proto.local_debug_hints)
            .filter_map(|(local, hint)| hint.is_some().then_some(local)),
    );
    bindings.params.extend(
        proto
            .params
            .iter()
            .copied()
            .zip(&proto.param_debug_hints)
            .filter_map(|(param, hint)| hint.is_some().then_some(param)),
    );
    bindings.temps.extend(
        proto
            .temps
            .iter()
            .copied()
            .zip(&proto.temp_debug_locals)
            .filter_map(|(temp, hint)| hint.is_some().then_some(temp)),
    );
    bindings
}

fn bindings_may_alias_local(
    bindings: &ReferenceCapturedBindings,
    local: LocalId,
    facts: &ProtoPromotionFacts,
) -> bool {
    let Some(candidate) = facts.trusted_local_home_slot(local) else {
        return true;
    };
    bindings.locals.iter().any(|binding| {
        facts.local_home_was_invalidated(*binding)
            || facts
                .local_home_slot(*binding)
                .is_none_or(|home| home == candidate)
    }) || bindings.params.iter().any(|binding| {
        facts.param_home_was_invalidated(*binding)
            || facts
                .trusted_param_home_slot(*binding)
                .is_none_or(|home| home == candidate)
    }) || bindings.temps.iter().any(|binding| {
        facts.temp_home_was_invalidated(*binding)
            || facts
                .home_slot(*binding)
                .is_none_or(|home| home == candidate)
    })
}
