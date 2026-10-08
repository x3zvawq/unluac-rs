//! 发布 repeat 条件端点的生命周期事实。
//!
//! 消费 object_flow 与 Promotion，向 AST 提供当前快照的物理根及条件前缩短许可；
//! AST 继续证明自身改写的词法和控制合法性。

use crate::hir::HirBinding;

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirBlock, HirModule, HirProto, HirRepeatBinding, HirRepeatConditionLifetimeFacts, HirStmt,
    LocalId, TempId,
};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::ProtoPromotionFacts;
use crate::hir::visit::{any_stmt_structure, visit_stmt_structure};

use super::lexical_cfg::{HirFlowGraph, HirFlowNodeKind};
use super::stmt_plan::{StmtPath, retain_stmts_with_paths};

use super::object_flow::{
    ModuleEffects, RootAnalysisContext, RootState, closure_captures_in_block, join_state,
    transfer_root_node,
};

/// 在请求模块效果前收集 repeat owner，空候选不触发分析。
pub(super) fn candidate_protos(module: &HirModule) -> Vec<usize> {
    module
        .protos
        .iter()
        .enumerate()
        .filter_map(|(index, proto)| {
            proto
                .body
                .stmts
                .iter()
                .any(|stmt| {
                    any_stmt_structure(stmt, &mut |stmt| matches!(stmt, HirStmt::Repeat(_)))
                })
                .then_some(index)
        })
        .collect()
}

/// 候选来自当前树；仅更新保留要求，不移动节点或改变控制、值和 capture。
/// 新 root 身份仍需唤醒 locals 安排词法 owner，稳定后将 endpoint certificate 交给 AST。
pub(super) fn mark_repeat_trailing_condition_roots(
    module: &mut HirModule,
    candidates: &[usize],
    promotion_facts: &[ProtoPromotionFacts],
    context: RootAnalysisContext<'_>,
) -> bool {
    let RootAnalysisContext { safety, effects } = context;
    let mut roots = Vec::with_capacity(candidates.len());
    for &index in candidates {
        let proto = &module.protos[index];
        let facts = promotion_facts.get(proto.id.index());
        roots.push(collect_proto_repeat_roots(proto, facts, effects, safety));
    }

    let mut changed = false;
    for (&index, roots) in candidates.iter().zip(roots) {
        let proto = &mut module.protos[index];
        let old_local_count = proto.physical_root_locals.len();
        let old_temp_count = proto.physical_root_temps.len();
        proto.physical_root_locals.extend(roots.locals);
        proto.physical_root_temps.extend(roots.temps);
        changed |= old_local_count != proto.physical_root_locals.len()
            || old_temp_count != proto.physical_root_temps.len();
        changed |= install_repeat_condition_lifetime_facts(&mut proto.body, roots.repeat_facts);
    }
    changed
}

#[derive(Default)]
struct RepeatRoots {
    locals: BTreeSet<LocalId>,
    temps: BTreeSet<TempId>,
    repeat_facts: BTreeMap<StmtPath, HirRepeatConditionLifetimeFacts>,
}

fn collect_proto_repeat_roots(
    proto: &HirProto,
    facts: Option<&ProtoPromotionFacts>,
    effects: &ModuleEffects,
    safety: HirExprSafety,
) -> RepeatRoots {
    let captures = closure_captures_in_block(&proto.body);
    let mut sites = BTreeMap::new();
    let graph = HirFlowGraph::for_stmts_with_locations(
        &proto.body.stmts,
        safety,
        |id, kind, block, index| {
            if let HirFlowNodeKind::RepeatCondition(_) = kind {
                sites.insert(
                    id,
                    RepeatSite {
                        path: block.to_stmt_path(index),
                        observable_bindings: None,
                        lifetime: HirRepeatConditionLifetimeFacts::default(),
                    },
                );
            }
        },
    )
    .expect("HIR labels must be unique before repeat root finalization");
    let mut initial = RootState::default();
    initial
        .unknown_collectable
        .extend(proto.params.iter().copied().map(HirBinding::Param));
    initial
        .unknown_collectable
        .extend(proto.upvalues.iter().copied().map(HirBinding::Upvalue));
    let mut roots = RepeatRoots::default();
    graph.solve_forward(initial, join_state, |id, kind, output| {
        if let HirFlowNodeKind::RepeatCondition(repeat) = kind {
            let site = sites
                .get_mut(&id)
                .expect("repeat condition has a published site");
            let bindings = site.observable_bindings.get_or_insert_with(|| {
                site.lifetime.may_end_before_condition = repeat_scoped_bindings(&repeat.body);
                let scoped = &site.lifetime.may_end_before_condition;
                if scoped.is_empty() || !safety.may_observe_gc_roots(&repeat.cond) {
                    return Vec::new();
                }
                scoped
                    .iter()
                    .copied()
                    .filter(|binding| match binding {
                        HirRepeatBinding::Local(local) => {
                            !facts.is_some_and(|facts| facts.local_has_no_physical_home(*local))
                        }
                        HirRepeatBinding::Temp(temp) => !facts.is_some_and(|facts| {
                            facts
                                .possible_temp_home_slots(*temp)
                                .is_some_and(|homes| homes.is_empty())
                        }),
                    })
                    .collect()
            });
            for &binding in bindings.iter() {
                let hir_binding = match binding {
                    HirRepeatBinding::Local(local) => HirBinding::Local(local),
                    HirRepeatBinding::Temp(temp) => HirBinding::Temp(temp),
                };
                if output.binding_may_hold_observable_root(hir_binding) {
                    site.lifetime.may_end_before_condition.remove(&binding);
                    match binding {
                        HirRepeatBinding::Local(local) => {
                            roots.locals.insert(local);
                        }
                        HirRepeatBinding::Temp(temp) => {
                            roots.temps.insert(temp);
                        }
                    }
                }
            }
        }
        transfer_root_node(kind, output, &captures, effects, safety);
    });
    roots.repeat_facts = sites
        .into_values()
        .map(|site| (site.path, site.lifetime))
        .collect();
    roots
}

struct RepeatSite {
    path: StmtPath,
    observable_bindings: Option<Vec<HirRepeatBinding>>,
    lifetime: HirRepeatConditionLifetimeFacts,
}

fn install_repeat_condition_lifetime_facts(
    block: &mut HirBlock,
    mut facts: BTreeMap<StmtPath, HirRepeatConditionLifetimeFacts>,
) -> bool {
    let mut changed = false;
    retain_stmts_with_paths(block, &mut Vec::new(), &mut |stmt, path| {
        if let HirStmt::Repeat(repeat) = stmt {
            let replacement = facts
                .remove(path)
                .expect("repeat has a published endpoint record");
            if repeat.lifetime != replacement {
                repeat.lifetime = replacement;
                changed = true;
            }
        }
        true
    });
    changed
}

/// 收集当前 repeat 正文内、词法作用域会在其 condition 之前或之后结束的 HIR binding。
///
/// 直属 binding 支持 AST collective 把 suffix 包进新 `do`；嵌套 block binding 支持
/// cleanup 删除前层已经存在或 AST 早先生成的尾部 `do`。这里只收集稳定 HIR identity，
/// 是否真的移动某个 block 仍由 AST 对具体候选证明。
fn repeat_scoped_bindings(block: &HirBlock) -> BTreeSet<HirRepeatBinding> {
    let mut bindings = BTreeSet::new();
    for stmt in &block.stmts {
        visit_stmt_structure(stmt, &mut |stmt| match stmt {
            HirStmt::LocalDecl(decl) => {
                bindings.extend(decl.bindings.iter().copied().map(HirRepeatBinding::Local));
            }
            HirStmt::Assign(assign) => {
                bindings.extend(assign.targets.iter().filter_map(|target| {
                    match HirBinding::from_lvalue(target) {
                        Some(HirBinding::Temp(temp)) => Some(HirRepeatBinding::Temp(temp)),
                        _ => None,
                    }
                }))
            }
            HirStmt::NumericFor(for_stmt) => {
                bindings.insert(HirRepeatBinding::Local(for_stmt.binding));
            }
            HirStmt::GenericFor(for_stmt) => {
                bindings.extend(
                    for_stmt
                        .bindings
                        .iter()
                        .copied()
                        .map(HirRepeatBinding::Local),
                );
            }
            _ => {}
        });
    }
    bindings
}
