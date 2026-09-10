//! repeat 条件端点的生命周期事实发布器。
//!
//! 消费 object_flow 的 binding/aggregate/closure 正向状态以及 Promotion 的物理 home，
//! 不独立解释对象流或 VM 槽。例如 body 中已逃逸 table 仍被 local 持有，且 until 可执行
//! 用户代码时，保留该 root；未逃逸 aggregate 可以获得当前端点的缩短许可。
//! 同时发布 proto-wide physical-root 集合和 repeat-specific may_end_before_condition，
//! AST 只消费这些事实并证明自身候选的词法/控制合法性。

use crate::hir::HirBinding;

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirBlock, HirModule, HirProto, HirRepeatBinding, HirRepeatConditionLifetimeFacts, HirStmt,
    LocalId, TempId,
};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::ProtoPromotionFacts;
use crate::hir::visit::any_stmt_structure;

use super::lexical_cfg::{FlowRefinement, HirFlowGraph, HirFlowNodeKind};

use super::object_flow::{
    ProtoEffects, RootAnalysisContext, RootState, binding_from_lvalue, closure_captures_in_block,
    join_state, transfer_root_node,
};

/// Deferred 阶段补齐 repeat 条件仍可观察的物理 root。
///
/// 新 root 身份会唤醒 locals，令无显式读取的 aggregate 也在 body 内得到词法 owner；
/// 直到身份与形状共同收敛，再把最终 endpoint certificate 交给 AST。
pub(super) fn mark_repeat_trailing_condition_roots(
    module: &mut HirModule,
    promotion_facts: &[ProtoPromotionFacts],
    context: RootAnalysisContext<'_>,
) -> bool {
    let RootAnalysisContext { safety, effects } = context;
    let relevant = module
        .protos
        .iter()
        .map(|proto| {
            proto.body.stmts.iter().any(|stmt| {
                any_stmt_structure(stmt, &mut |stmt| matches!(stmt, HirStmt::Repeat(_)))
            })
        })
        .collect::<Vec<_>>();
    if !relevant.iter().any(|present| *present) {
        return false;
    }
    let mut roots = Vec::with_capacity(module.protos.len());
    for (proto, relevant) in module.protos.iter().zip(relevant) {
        if !relevant {
            roots.push(RepeatRoots::default());
            continue;
        }
        let facts = promotion_facts.get(proto.id.index());
        roots.push(collect_proto_repeat_roots(proto, facts, effects, safety));
    }

    let mut changed = false;
    for (proto, roots) in module.protos.iter_mut().zip(roots) {
        let old_local_count = proto.physical_root_locals.len();
        let old_temp_count = proto.physical_root_temps.len();
        proto.physical_root_locals.extend(roots.locals);
        proto.physical_root_temps.extend(roots.temps);
        changed |= old_local_count != proto.physical_root_locals.len()
            || old_temp_count != proto.physical_root_temps.len();
        changed |= install_repeat_condition_lifetime_facts(&mut proto.body, &roots.repeat_facts);
    }
    changed
}

#[derive(Default)]
struct RepeatRoots {
    locals: BTreeSet<LocalId>,
    temps: BTreeSet<TempId>,
    repeat_facts: BTreeMap<usize, HirRepeatConditionLifetimeFacts>,
}

fn collect_proto_repeat_roots(
    proto: &HirProto,
    facts: Option<&ProtoPromotionFacts>,
    effects: &[ProtoEffects],
    safety: HirExprSafety,
) -> RepeatRoots {
    let captures = closure_captures_in_block(&proto.body);
    let graph = HirFlowGraph::for_block(&proto.body, safety)
        .expect("HIR labels must be unique before repeat root finalization");
    let mut initial = RootState::default();
    initial
        .unknown_collectable
        .extend(proto.params.iter().copied().map(HirBinding::Param));
    initial
        .unknown_collectable
        .extend(proto.upvalues.iter().copied().map(HirBinding::Upvalue));
    let mut roots = RepeatRoots::default();
    graph.solve_forward(
        initial,
        join_state,
        |_, kind, output| {
            if let HirFlowNodeKind::RepeatCondition(repeat) = kind {
                note_repeat_condition_lifetimes(repeat, output, facts, &mut roots, safety);
            }
            transfer_root_node(kind, output, &captures, effects, safety);
        },
        |_expr, _truthy, _state| FlowRefinement::Unchanged,
    );
    roots
}

fn note_repeat_condition_lifetimes(
    repeat: &crate::hir::common::HirRepeat,
    state: &RootState,
    facts: Option<&ProtoPromotionFacts>,
    roots: &mut RepeatRoots,
    safety: HirExprSafety,
) {
    let scoped_bindings = repeat_scoped_bindings(&repeat.body);
    let repeat_key = std::ptr::from_ref(repeat).addr();
    roots
        .repeat_facts
        .entry(repeat_key)
        .or_insert_with(|| HirRepeatConditionLifetimeFacts {
            may_end_before_condition: scoped_bindings
                .iter()
                .filter_map(|binding| repeat_binding(*binding))
                .collect(),
        });

    let eventful =
        !scoped_bindings.is_empty() && !safety.is_discard_safe_without_residual(&repeat.cond);
    for binding in scoped_bindings {
        let observable = eventful && state.binding_may_hold_observable_root(binding);
        let has_physical_home = match binding {
            HirBinding::Local(local) => {
                !facts.is_some_and(|facts| facts.local_has_no_physical_home(local))
            }
            HirBinding::Temp(temp) => !facts.is_some_and(|facts| {
                facts
                    .possible_temp_home_slots(temp)
                    .is_some_and(|homes| homes.is_empty())
            }),
            HirBinding::Param(_) | HirBinding::Upvalue(_) => false,
        };
        if observable && has_physical_home {
            if let Some(binding) = repeat_binding(binding) {
                roots
                    .repeat_facts
                    .get_mut(&repeat_key)
                    .expect("reachable repeat must have endpoint facts")
                    .may_end_before_condition
                    .remove(&binding);
            }
            match binding {
                HirBinding::Local(local) => {
                    roots.locals.insert(local);
                }
                HirBinding::Temp(temp) => {
                    roots.temps.insert(temp);
                }
                HirBinding::Param(_) | HirBinding::Upvalue(_) => {}
            }
        }
    }
}

fn repeat_binding(binding: HirBinding) -> Option<HirRepeatBinding> {
    match binding {
        HirBinding::Local(local) => Some(HirRepeatBinding::Local(local)),
        HirBinding::Temp(temp) => Some(HirRepeatBinding::Temp(temp)),
        HirBinding::Param(_) | HirBinding::Upvalue(_) => None,
    }
}

fn install_repeat_condition_lifetime_facts(
    block: &mut HirBlock,
    facts: &BTreeMap<usize, HirRepeatConditionLifetimeFacts>,
) -> bool {
    let mut changed = false;
    for stmt in &mut block.stmts {
        match stmt {
            HirStmt::LocalRootRelease(_) => {}
            HirStmt::If(if_stmt) => {
                changed |= install_repeat_condition_lifetime_facts(&mut if_stmt.then_block, facts);
                if let Some(else_block) = &mut if_stmt.else_block {
                    changed |= install_repeat_condition_lifetime_facts(else_block, facts);
                }
            }
            HirStmt::While(while_stmt) => {
                changed |= install_repeat_condition_lifetime_facts(&mut while_stmt.body, facts);
            }
            HirStmt::Repeat(repeat) => {
                let repeat_key = std::ptr::from_ref(repeat.as_ref()).addr();
                let replacement = facts.get(&repeat_key).cloned().unwrap_or_default();
                if repeat.lifetime != replacement {
                    repeat.lifetime = replacement;
                    changed = true;
                }
                changed |= install_repeat_condition_lifetime_facts(&mut repeat.body, facts);
            }
            HirStmt::NumericFor(for_) => {
                changed |= install_repeat_condition_lifetime_facts(&mut for_.body, facts);
            }
            HirStmt::GenericFor(for_) => {
                changed |= install_repeat_condition_lifetime_facts(&mut for_.body, facts);
            }
            HirStmt::Block(block) => {
                changed |= install_repeat_condition_lifetime_facts(block, facts);
            }
            HirStmt::LocalDecl(_)
            | HirStmt::GlobalDecl(_)
            | HirStmt::Assign(_)
            | HirStmt::TableSetList(_)
            | HirStmt::ErrNil(_)
            | HirStmt::ToBeClosed(_)
            | HirStmt::Close(_)
            | HirStmt::CallStmt(_)
            | HirStmt::Return(_)
            | HirStmt::Break
            | HirStmt::Continue
            | HirStmt::Goto(_)
            | HirStmt::Label(_) => {}
        }
    }
    changed
}

/// 收集当前 repeat 正文内、词法作用域会在其 condition 之前或之后结束的 HIR binding。
///
/// 直属 binding 支持 AST collective 把 suffix 包进新 `do`；嵌套 block binding 支持
/// cleanup 删除前层已经存在或 AST 早先生成的尾部 `do`。这里只收集稳定 HIR identity，
/// 是否真的移动某个 block 仍由 AST 对具体候选证明。
fn repeat_scoped_bindings(block: &HirBlock) -> BTreeSet<HirBinding> {
    let mut bindings = BTreeSet::new();
    for stmt in &block.stmts {
        match stmt {
            HirStmt::LocalRootRelease(_) => {}
            HirStmt::LocalDecl(decl) => {
                bindings.extend(decl.bindings.iter().copied().map(HirBinding::Local))
            }
            HirStmt::Assign(assign) => bindings.extend(
                assign
                    .targets
                    .iter()
                    .filter_map(binding_from_lvalue)
                    .filter(|binding| matches!(binding, HirBinding::Temp(_))),
            ),
            HirStmt::If(if_stmt) => {
                bindings.extend(repeat_scoped_bindings(&if_stmt.then_block));
                if let Some(else_block) = &if_stmt.else_block {
                    bindings.extend(repeat_scoped_bindings(else_block));
                }
            }
            HirStmt::While(while_stmt) => {
                bindings.extend(repeat_scoped_bindings(&while_stmt.body));
            }
            HirStmt::Repeat(repeat_stmt) => {
                bindings.extend(repeat_scoped_bindings(&repeat_stmt.body));
            }
            HirStmt::NumericFor(for_stmt) => {
                bindings.insert(HirBinding::Local(for_stmt.binding));
                bindings.extend(repeat_scoped_bindings(&for_stmt.body));
            }
            HirStmt::GenericFor(for_stmt) => {
                bindings.extend(for_stmt.bindings.iter().copied().map(HirBinding::Local));
                bindings.extend(repeat_scoped_bindings(&for_stmt.body));
            }
            HirStmt::Block(block) => bindings.extend(repeat_scoped_bindings(block)),
            HirStmt::GlobalDecl(_)
            | HirStmt::TableSetList(_)
            | HirStmt::ErrNil(_)
            | HirStmt::ToBeClosed(_)
            | HirStmt::Close(_)
            | HirStmt::CallStmt(_)
            | HirStmt::Return(_)
            | HirStmt::Break
            | HirStmt::Continue
            | HirStmt::Goto(_)
            | HirStmt::Label(_) => {}
        }
    }
    bindings
}
