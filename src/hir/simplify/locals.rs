//! 这个文件负责把“已经明显跨语句存活的 temp”提升成 HIR local。
//!
//! 我们这里故意不去猜所有 temp 都是不是源码变量，而是只抓一类非常稳的形状：
//! 当前 block 顶层先有一次初始化，后面这批 SSA temp 通过简单别名链继续流动，并且
//! 在后续语句里继续被读/写。对这类值，继续保留 `t12 / t13 / ...` 只会让 HIR 充满
//! 版本噪音，把它们折回同一个 `LocalId` 更接近源码，也能为后续 AST/Naming 铺路。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirBlock, HirCallExpr, HirExpr, HirLValue, HirLocalDecl, HirProto, HirStmt,
    HirTableConstructor, HirTableField, HirTableKey, LocalId, TempId,
};

/// 对单个 proto 执行保守的 temp -> local 提升。
pub(super) fn promote_temps_to_locals_in_proto(proto: &mut HirProto) -> bool {
    let mut next_local_index = proto.locals.len();
    let mut new_locals = Vec::new();
    let result = promote_block(
        &mut proto.body,
        &BTreeMap::new(),
        &mut next_local_index,
        &mut new_locals,
    );
    proto.locals.extend(new_locals);
    result.changed
}

#[derive(Debug, Clone)]
struct PromotionPlan {
    decl_index: usize,
    local: LocalId,
    temps: BTreeSet<TempId>,
    removable_aliases: BTreeSet<usize>,
    init: PromotionInit,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum PromotionInit {
    FromAssign,
    Empty,
}

#[derive(Debug, Clone, Default)]
struct FallthroughSummary {
    falls_through: bool,
    assigned_temps: BTreeSet<TempId>,
}

struct PromotionResult {
    changed: bool,
    trailing_mapping: BTreeMap<TempId, LocalId>,
}

struct PlanAllocator<'a> {
    plans: &'a mut Vec<PromotionPlan>,
    reserved_temps: &'a mut BTreeSet<TempId>,
    reserved_alias_indices: &'a mut BTreeSet<usize>,
    next_local_index: &'a mut usize,
    new_locals: &'a mut Vec<LocalId>,
}

impl PlanAllocator<'_> {
    fn allocate(
        &mut self,
        decl_index: usize,
        temps: BTreeSet<TempId>,
        removable_aliases: BTreeSet<usize>,
        init: PromotionInit,
    ) {
        let local = LocalId(*self.next_local_index);
        *self.next_local_index += 1;
        self.new_locals.push(local);
        self.reserved_temps.extend(temps.iter().copied());
        self.reserved_alias_indices
            .extend(removable_aliases.iter().copied());
        self.plans.push(PromotionPlan {
            decl_index,
            local,
            temps,
            removable_aliases,
            init,
        });
    }
}

fn promote_block(
    block: &mut HirBlock,
    inherited: &BTreeMap<TempId, LocalId>,
    next_local_index: &mut usize,
    new_locals: &mut Vec<LocalId>,
) -> PromotionResult {
    let plans = collect_plans(block, inherited, next_local_index, new_locals);
    let plan_by_decl = plans.iter().fold(
        BTreeMap::<usize, Vec<&PromotionPlan>>::new(),
        |mut grouped, plan| {
            grouped.entry(plan.decl_index).or_default().push(plan);
            grouped
        },
    );
    let removable = plans
        .iter()
        .flat_map(|plan| plan.removable_aliases.iter().copied())
        .collect::<BTreeSet<_>>();

    let mut changed = !plans.is_empty();
    let mut mapping = inherited.clone();
    let original_stmts = std::mem::take(&mut block.stmts);
    let mut rewritten = Vec::with_capacity(original_stmts.len());

    for (index, mut stmt) in original_stmts.into_iter().enumerate() {
        let mut replaced_stmt = false;
        if let Some(plans) = plan_by_decl.get(&index) {
            let mapping_before_decl = mapping.clone();
            for plan in plans {
                if let Some(local_decl) =
                    rewrite_decl_stmt(&stmt, plan.local, &mapping_before_decl, plan.init)
                {
                    for temp in &plan.temps {
                        mapping.insert(*temp, plan.local);
                    }
                    replaced_stmt |= matches!(plan.init, PromotionInit::FromAssign);
                    rewritten.push(local_decl);
                }
            }
        }
        if replaced_stmt {
            continue;
        }

        if removable.contains(&index) {
            continue;
        }

        let stmt_changed = rewrite_stmt(&mut stmt, &mapping, next_local_index, new_locals);
        changed |= stmt_changed;
        rewritten.push(stmt);
    }

    block.stmts = rewritten;
    PromotionResult {
        changed,
        trailing_mapping: mapping,
    }
}

fn collect_plans(
    block: &HirBlock,
    inherited: &BTreeMap<TempId, LocalId>,
    next_local_index: &mut usize,
    new_locals: &mut Vec<LocalId>,
) -> Vec<PromotionPlan> {
    if block.stmts.iter().any(|stmt| {
        matches!(
            stmt,
            HirStmt::Continue | HirStmt::Goto(_) | HirStmt::Label(_) | HirStmt::Unstructured(_)
        )
    }) {
        return Vec::new();
    }

    let mut plans = Vec::new();
    let mut reserved_temps = inherited.keys().copied().collect::<BTreeSet<_>>();
    let mut reserved_alias_indices = BTreeSet::new();

    for (decl_index, stmt) in block.stmts.iter().enumerate() {
        if reserved_alias_indices.contains(&decl_index) {
            continue;
        }

        let Some(root_temp) = simple_temp_assign_target(stmt) else {
            continue;
        };
        if reserved_temps.contains(&root_temp) {
            continue;
        }

        let mut group = BTreeSet::from([root_temp]);
        let mut removable_aliases = BTreeSet::new();
        let mut has_future_touch = false;

        for future_index in decl_index + 1..block.stmts.len() {
            if removable_aliases.contains(&future_index) {
                continue;
            }
            let future_stmt = &block.stmts[future_index];

            if let Some(alias_temp) = alias_temp_for_group(future_stmt, &group)
                && !reserved_temps.contains(&alias_temp)
                && !group.contains(&alias_temp)
                && !stmts_touch_temp(&block.stmts[decl_index + 1..future_index], alias_temp)
            {
                group.insert(alias_temp);
                removable_aliases.insert(future_index);
                continue;
            }

            if stmt_touches_any_temp(future_stmt, &group) {
                has_future_touch = true;
            }
        }

        if !has_future_touch {
            continue;
        }

        PlanAllocator {
            plans: &mut plans,
            reserved_temps: &mut reserved_temps,
            reserved_alias_indices: &mut reserved_alias_indices,
            next_local_index,
            new_locals,
        }
        .allocate(
            decl_index,
            group,
            removable_aliases,
            PromotionInit::FromAssign,
        );
    }

    for (decl_index, stmt) in block.stmts.iter().enumerate() {
        let merge_temps = if_merge_candidate_temps(
            stmt,
            &block.stmts[..decl_index],
            &block.stmts[decl_index + 1..],
            &reserved_temps,
        );

        for temp in merge_temps {
            PlanAllocator {
                plans: &mut plans,
                reserved_temps: &mut reserved_temps,
                reserved_alias_indices: &mut reserved_alias_indices,
                next_local_index,
                new_locals,
            }
            .allocate(
                decl_index,
                BTreeSet::from([temp]),
                BTreeSet::new(),
                PromotionInit::Empty,
            );
        }
    }

    plans
}

fn simple_temp_assign_target(stmt: &HirStmt) -> Option<TempId> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [HirLValue::Temp(temp)] = assign.targets.as_slice() else {
        return None;
    };
    let [_value] = assign.values.as_slice() else {
        return None;
    };
    Some(*temp)
}

fn alias_temp_for_group(stmt: &HirStmt, group: &BTreeSet<TempId>) -> Option<TempId> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [HirLValue::Temp(alias)] = assign.targets.as_slice() else {
        return None;
    };
    let [HirExpr::TempRef(source)] = assign.values.as_slice() else {
        return None;
    };
    group.contains(source).then_some(*alias)
}

fn if_merge_candidate_temps(
    stmt: &HirStmt,
    prior_stmts: &[HirStmt],
    future_stmts: &[HirStmt],
    reserved_temps: &BTreeSet<TempId>,
) -> Vec<TempId> {
    let HirStmt::If(if_stmt) = stmt else {
        return Vec::new();
    };
    let Some(else_block) = &if_stmt.else_block else {
        return Vec::new();
    };

    let then_summary = summarize_block_fallthrough_assignments(&if_stmt.then_block);
    let else_summary = summarize_block_fallthrough_assignments(else_block);
    let Some(common_temps) =
        intersect_fallthrough_assignment_sets([then_summary.as_ref(), else_summary.as_ref()])
    else {
        return Vec::new();
    };

    common_temps
        .into_iter()
        .filter(|temp| !reserved_temps.contains(temp))
        .filter(|temp| !stmts_touch_temp(prior_stmts, *temp))
        .filter(|temp| stmts_touch_temp(future_stmts, *temp))
        .collect()
}

fn summarize_block_fallthrough_assignments(block: &HirBlock) -> Option<FallthroughSummary> {
    let mut assigned_temps = BTreeSet::new();
    let mut falls_through = true;

    for stmt in &block.stmts {
        if !falls_through {
            break;
        }

        let stmt_summary = summarize_stmt_fallthrough_assignments(stmt)?;
        if stmt_summary.falls_through {
            assigned_temps.extend(stmt_summary.assigned_temps);
        } else {
            falls_through = false;
        }
    }

    Some(FallthroughSummary {
        falls_through,
        assigned_temps,
    })
}

fn summarize_stmt_fallthrough_assignments(stmt: &HirStmt) -> Option<FallthroughSummary> {
    match stmt {
        HirStmt::LocalDecl(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Label(_) => {
            Some(FallthroughSummary {
                falls_through: true,
                assigned_temps: BTreeSet::new(),
            })
        }
        HirStmt::Assign(assign) => Some(FallthroughSummary {
            falls_through: true,
            assigned_temps: assign
                .targets
                .iter()
                .filter_map(|target| match target {
                    HirLValue::Temp(temp) => Some(*temp),
                    HirLValue::Local(_)
                    | HirLValue::Upvalue(_)
                    | HirLValue::Global(_)
                    | HirLValue::TableAccess(_) => None,
                })
                .collect(),
        }),
        HirStmt::TableSetList(_) => None,
        HirStmt::Return(_) | HirStmt::Goto(_) | HirStmt::Break | HirStmt::Continue => {
            Some(FallthroughSummary {
                falls_through: false,
                assigned_temps: BTreeSet::new(),
            })
        }
        HirStmt::If(if_stmt) => {
            let else_block = if_stmt.else_block.as_ref()?;
            let then_summary = summarize_block_fallthrough_assignments(&if_stmt.then_block)?;
            let else_summary = summarize_block_fallthrough_assignments(else_block)?;
            let assigned_temps =
                intersect_fallthrough_assignment_sets([Some(&then_summary), Some(&else_summary)])
                    .unwrap_or_default();

            Some(FallthroughSummary {
                falls_through: then_summary.falls_through || else_summary.falls_through,
                assigned_temps,
            })
        }
        HirStmt::Block(block) => summarize_block_fallthrough_assignments(block),
        HirStmt::While(_)
        | HirStmt::Repeat(_)
        | HirStmt::NumericFor(_)
        | HirStmt::GenericFor(_)
        | HirStmt::Unstructured(_) => None,
    }
}

fn intersect_fallthrough_assignment_sets<'a>(
    summaries: impl IntoIterator<Item = Option<&'a FallthroughSummary>>,
) -> Option<BTreeSet<TempId>> {
    let mut fallthrough_sets = summaries
        .into_iter()
        .flatten()
        .filter(|summary| summary.falls_through)
        .map(|summary| summary.assigned_temps.clone());
    let mut intersection = fallthrough_sets.next()?;
    for set in fallthrough_sets {
        intersection = intersection
            .intersection(&set)
            .copied()
            .collect::<BTreeSet<_>>();
    }
    Some(intersection)
}

fn rewrite_decl_stmt(
    stmt: &HirStmt,
    local: LocalId,
    mapping: &BTreeMap<TempId, LocalId>,
    init: PromotionInit,
) -> Option<HirStmt> {
    let values = match init {
        PromotionInit::FromAssign => {
            let HirStmt::Assign(assign) = stmt else {
                return None;
            };
            let [HirLValue::Temp(_temp)] = assign.targets.as_slice() else {
                return None;
            };

            assign
                .values
                .iter()
                .cloned()
                .map(|mut expr| {
                    rewrite_expr(&mut expr, mapping);
                    expr
                })
                .collect::<Vec<_>>()
        }
        PromotionInit::Empty => Vec::new(),
    };

    Some(HirStmt::LocalDecl(Box::new(HirLocalDecl {
        bindings: vec![local],
        values,
    })))
}

fn rewrite_stmt(
    stmt: &mut HirStmt,
    mapping: &BTreeMap<TempId, LocalId>,
    next_local_index: &mut usize,
    new_locals: &mut Vec<LocalId>,
) -> bool {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            local_decl.values.iter_mut().fold(false, |changed, expr| {
                rewrite_expr(expr, mapping) || changed
            })
        }
        HirStmt::Assign(assign) => {
            let targets_changed = assign.targets.iter_mut().fold(false, |changed, target| {
                rewrite_lvalue(target, mapping) || changed
            });
            let values_changed = assign.values.iter_mut().fold(false, |changed, expr| {
                rewrite_expr(expr, mapping) || changed
            });
            targets_changed || values_changed
        }
        HirStmt::TableSetList(set_list) => {
            let base_changed = rewrite_expr(&mut set_list.base, mapping);
            let values_changed = set_list.values.iter_mut().fold(false, |changed, expr| {
                rewrite_expr(expr, mapping) || changed
            });
            let trailing_changed = set_list
                .trailing_multivalue
                .as_mut()
                .is_some_and(|expr| rewrite_expr(expr, mapping));
            base_changed || values_changed || trailing_changed
        }
        HirStmt::ErrNil(err_nil) => rewrite_expr(&mut err_nil.value, mapping),
        HirStmt::ToBeClosed(to_be_closed) => rewrite_expr(&mut to_be_closed.value, mapping),
        HirStmt::CallStmt(call_stmt) => rewrite_call_expr(&mut call_stmt.call, mapping),
        HirStmt::Return(ret) => ret.values.iter_mut().fold(false, |changed, expr| {
            rewrite_expr(expr, mapping) || changed
        }),
        HirStmt::If(if_stmt) => {
            let cond_changed = rewrite_expr(&mut if_stmt.cond, mapping);
            let then_changed = promote_block(
                &mut if_stmt.then_block,
                mapping,
                next_local_index,
                new_locals,
            )
            .changed;
            let else_changed = if_stmt.else_block.as_mut().is_some_and(|else_block| {
                promote_block(else_block, mapping, next_local_index, new_locals).changed
            });
            cond_changed || then_changed || else_changed
        }
        HirStmt::While(while_stmt) => {
            let cond_changed = rewrite_expr(&mut while_stmt.cond, mapping);
            let body_changed =
                promote_block(&mut while_stmt.body, mapping, next_local_index, new_locals).changed;
            cond_changed || body_changed
        }
        HirStmt::Repeat(repeat_stmt) => {
            // `repeat ... until` 的条件和 loop body 共享同一个词法作用域。
            // body 里刚刚提升出来的 local 如果不继续带到条件里，条件就会继续挂着旧 temp，
            // 最后得到“body 已经是 l2，until 里还是 t3”这种半截 HIR。
            let body_result =
                promote_block(&mut repeat_stmt.body, mapping, next_local_index, new_locals);
            let cond_changed = rewrite_expr(&mut repeat_stmt.cond, &body_result.trailing_mapping);
            body_result.changed || cond_changed
        }
        HirStmt::NumericFor(numeric_for) => {
            let start_changed = rewrite_expr(&mut numeric_for.start, mapping);
            let limit_changed = rewrite_expr(&mut numeric_for.limit, mapping);
            let step_changed = rewrite_expr(&mut numeric_for.step, mapping);
            let body_changed =
                promote_block(&mut numeric_for.body, mapping, next_local_index, new_locals).changed;
            start_changed || limit_changed || step_changed || body_changed
        }
        HirStmt::GenericFor(generic_for) => {
            let iterator_changed = generic_for
                .iterator
                .iter_mut()
                .fold(false, |changed, expr| {
                    rewrite_expr(expr, mapping) || changed
                });
            let body_changed =
                promote_block(&mut generic_for.body, mapping, next_local_index, new_locals).changed;
            iterator_changed || body_changed
        }
        HirStmt::Block(block) => {
            promote_block(block, mapping, next_local_index, new_locals).changed
        }
        HirStmt::Unstructured(unstructured) => {
            promote_block(
                &mut unstructured.body,
                mapping,
                next_local_index,
                new_locals,
            )
            .changed
        }
        HirStmt::Break
        | HirStmt::Close(_)
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => false,
    }
}

fn rewrite_call_expr(call: &mut HirCallExpr, mapping: &BTreeMap<TempId, LocalId>) -> bool {
    let callee_changed = rewrite_expr(&mut call.callee, mapping);
    let args_changed = call
        .args
        .iter_mut()
        .fold(false, |changed, arg| rewrite_expr(arg, mapping) || changed);
    callee_changed || args_changed
}

fn rewrite_expr(expr: &mut HirExpr, mapping: &BTreeMap<TempId, LocalId>) -> bool {
    match expr {
        HirExpr::TempRef(temp) => {
            if let Some(local) = mapping.get(temp) {
                *expr = HirExpr::LocalRef(*local);
                true
            } else {
                false
            }
        }
        HirExpr::TableAccess(access) => {
            let base_changed = rewrite_expr(&mut access.base, mapping);
            let key_changed = rewrite_expr(&mut access.key, mapping);
            base_changed || key_changed
        }
        HirExpr::Unary(unary) => rewrite_expr(&mut unary.expr, mapping),
        HirExpr::Binary(binary) => {
            let lhs_changed = rewrite_expr(&mut binary.lhs, mapping);
            let rhs_changed = rewrite_expr(&mut binary.rhs, mapping);
            lhs_changed || rhs_changed
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            let lhs_changed = rewrite_expr(&mut logical.lhs, mapping);
            let rhs_changed = rewrite_expr(&mut logical.rhs, mapping);
            lhs_changed || rhs_changed
        }
        HirExpr::Decision(decision) => decision.nodes.iter_mut().fold(false, |changed, node| {
            let test_changed = rewrite_expr(&mut node.test, mapping);
            let truthy_changed = rewrite_decision_target(&mut node.truthy, mapping);
            let falsy_changed = rewrite_decision_target(&mut node.falsy, mapping);
            changed || test_changed || truthy_changed || falsy_changed
        }),
        HirExpr::Call(call) => rewrite_call_expr(call, mapping),
        HirExpr::TableConstructor(table) => rewrite_table_constructor(table, mapping),
        HirExpr::Closure(closure) => closure.captures.iter_mut().fold(false, |changed, capture| {
            rewrite_expr(&mut capture.value, mapping) || changed
        }),
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => false,
    }
}

fn rewrite_decision_target(
    target: &mut crate::hir::common::HirDecisionTarget,
    mapping: &BTreeMap<TempId, LocalId>,
) -> bool {
    match target {
        crate::hir::common::HirDecisionTarget::Expr(expr) => rewrite_expr(expr, mapping),
        crate::hir::common::HirDecisionTarget::Node(_)
        | crate::hir::common::HirDecisionTarget::CurrentValue => false,
    }
}

fn rewrite_table_constructor(
    table: &mut HirTableConstructor,
    mapping: &BTreeMap<TempId, LocalId>,
) -> bool {
    let fields_changed = table.fields.iter_mut().fold(false, |changed, field| {
        let field_changed = match field {
            HirTableField::Array(expr) => rewrite_expr(expr, mapping),
            HirTableField::Record(field) => {
                let key_changed = match &mut field.key {
                    HirTableKey::Name(_) => false,
                    HirTableKey::Expr(expr) => rewrite_expr(expr, mapping),
                };
                let value_changed = rewrite_expr(&mut field.value, mapping);
                key_changed || value_changed
            }
        };
        changed || field_changed
    });
    let trailing_changed = table
        .trailing_multivalue
        .as_mut()
        .is_some_and(|expr| rewrite_expr(expr, mapping));

    fields_changed || trailing_changed
}

fn rewrite_lvalue(lvalue: &mut HirLValue, mapping: &BTreeMap<TempId, LocalId>) -> bool {
    match lvalue {
        HirLValue::Temp(temp) => {
            if let Some(local) = mapping.get(temp) {
                *lvalue = HirLValue::Local(*local);
                true
            } else {
                false
            }
        }
        HirLValue::TableAccess(access) => {
            let base_changed = rewrite_expr(&mut access.base, mapping);
            let key_changed = rewrite_expr(&mut access.key, mapping);
            base_changed || key_changed
        }
        HirLValue::Local(_) | HirLValue::Upvalue(_) | HirLValue::Global(_) => false,
    }
}

fn stmts_touch_temp(stmts: &[HirStmt], temp: TempId) -> bool {
    stmts.iter().any(|stmt| stmt_touches_temp(stmt, temp))
}

fn stmt_touches_any_temp(stmt: &HirStmt, temps: &BTreeSet<TempId>) -> bool {
    temps.iter().any(|temp| stmt_touches_temp(stmt, *temp))
}

fn stmt_touches_temp(stmt: &HirStmt, temp: TempId) -> bool {
    match stmt {
        HirStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter()
            .any(|expr| expr_touches_temp(expr, temp)),
        HirStmt::Assign(assign) => {
            assign
                .targets
                .iter()
                .any(|target| lvalue_touches_temp(target, temp))
                || assign
                    .values
                    .iter()
                    .any(|expr| expr_touches_temp(expr, temp))
        }
        HirStmt::TableSetList(set_list) => {
            expr_touches_temp(&set_list.base, temp)
                || set_list
                    .values
                    .iter()
                    .any(|expr| expr_touches_temp(expr, temp))
                || set_list
                    .trailing_multivalue
                    .as_ref()
                    .is_some_and(|expr| expr_touches_temp(expr, temp))
        }
        HirStmt::ErrNil(err_nil) => expr_touches_temp(&err_nil.value, temp),
        HirStmt::ToBeClosed(to_be_closed) => expr_touches_temp(&to_be_closed.value, temp),
        HirStmt::CallStmt(call_stmt) => call_expr_touches_temp(&call_stmt.call, temp),
        HirStmt::Return(ret) => ret.values.iter().any(|expr| expr_touches_temp(expr, temp)),
        HirStmt::If(if_stmt) => {
            expr_touches_temp(&if_stmt.cond, temp)
                || stmts_touch_temp(&if_stmt.then_block.stmts, temp)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(|else_block| stmts_touch_temp(&else_block.stmts, temp))
        }
        HirStmt::While(while_stmt) => {
            expr_touches_temp(&while_stmt.cond, temp)
                || stmts_touch_temp(&while_stmt.body.stmts, temp)
        }
        HirStmt::Repeat(repeat_stmt) => {
            stmts_touch_temp(&repeat_stmt.body.stmts, temp)
                || expr_touches_temp(&repeat_stmt.cond, temp)
        }
        HirStmt::NumericFor(numeric_for) => {
            expr_touches_temp(&numeric_for.start, temp)
                || expr_touches_temp(&numeric_for.limit, temp)
                || expr_touches_temp(&numeric_for.step, temp)
                || stmts_touch_temp(&numeric_for.body.stmts, temp)
        }
        HirStmt::GenericFor(generic_for) => {
            generic_for
                .iterator
                .iter()
                .any(|expr| expr_touches_temp(expr, temp))
                || stmts_touch_temp(&generic_for.body.stmts, temp)
        }
        HirStmt::Block(block) => stmts_touch_temp(&block.stmts, temp),
        HirStmt::Unstructured(unstructured) => stmts_touch_temp(&unstructured.body.stmts, temp),
        HirStmt::Break
        | HirStmt::Close(_)
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => false,
    }
}

fn call_expr_touches_temp(call: &HirCallExpr, temp: TempId) -> bool {
    expr_touches_temp(&call.callee, temp)
        || call.args.iter().any(|arg| expr_touches_temp(arg, temp))
}

fn expr_touches_temp(expr: &HirExpr, temp: TempId) -> bool {
    match expr {
        HirExpr::TempRef(other) => *other == temp,
        HirExpr::TableAccess(access) => {
            expr_touches_temp(&access.base, temp) || expr_touches_temp(&access.key, temp)
        }
        HirExpr::Unary(unary) => expr_touches_temp(&unary.expr, temp),
        HirExpr::Binary(binary) => {
            expr_touches_temp(&binary.lhs, temp) || expr_touches_temp(&binary.rhs, temp)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_touches_temp(&logical.lhs, temp) || expr_touches_temp(&logical.rhs, temp)
        }
        HirExpr::Decision(decision) => decision.nodes.iter().any(|node| {
            expr_touches_temp(&node.test, temp)
                || decision_target_touches_temp(&node.truthy, temp)
                || decision_target_touches_temp(&node.falsy, temp)
        }),
        HirExpr::Call(call) => call_expr_touches_temp(call, temp),
        HirExpr::TableConstructor(table) => {
            table.fields.iter().any(|field| match field {
                HirTableField::Array(expr) => expr_touches_temp(expr, temp),
                HirTableField::Record(field) => {
                    matches!(&field.key, HirTableKey::Expr(expr) if expr_touches_temp(expr, temp))
                        || expr_touches_temp(&field.value, temp)
                }
            }) || table
                .trailing_multivalue
                .as_ref()
                .is_some_and(|expr| expr_touches_temp(expr, temp))
        }
        HirExpr::Closure(closure) => closure
            .captures
            .iter()
            .any(|capture| expr_touches_temp(&capture.value, temp)),
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => false,
    }
}

fn decision_target_touches_temp(
    target: &crate::hir::common::HirDecisionTarget,
    temp: TempId,
) -> bool {
    match target {
        crate::hir::common::HirDecisionTarget::Expr(expr) => expr_touches_temp(expr, temp),
        crate::hir::common::HirDecisionTarget::Node(_)
        | crate::hir::common::HirDecisionTarget::CurrentValue => false,
    }
}

fn lvalue_touches_temp(lvalue: &HirLValue, temp: TempId) -> bool {
    match lvalue {
        HirLValue::Temp(other) => *other == temp,
        HirLValue::TableAccess(access) => {
            expr_touches_temp(&access.base, temp) || expr_touches_temp(&access.key, temp)
        }
        HirLValue::Local(_) | HirLValue::Upvalue(_) | HirLValue::Global(_) => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::common::{HirAssign, HirIf, HirModule, HirProto, HirProtoRef, HirReturn};

    #[test]
    fn promotes_temp_alias_chain_into_single_local() {
        let mut module = HirModule {
            entry: HirProtoRef(0),
            protos: vec![dummy_proto(HirBlock {
                stmts: vec![
                    HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Temp(TempId(0))],
                        values: vec![HirExpr::Boolean(true)],
                    })),
                    HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Temp(TempId(1))],
                        values: vec![HirExpr::TempRef(TempId(0))],
                    })),
                    HirStmt::If(Box::new(HirIf {
                        cond: HirExpr::TempRef(TempId(0)),
                        then_block: HirBlock {
                            stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                                targets: vec![HirLValue::Temp(TempId(1))],
                                values: vec![HirExpr::Integer(41)],
                            }))],
                        },
                        else_block: None,
                    })),
                    HirStmt::Return(Box::new(HirReturn {
                        values: vec![HirExpr::TempRef(TempId(1))],
                    })),
                ],
            })],
        };

        super::super::simplify_hir(&mut module);

        assert_eq!(module.protos[0].locals.len(), 1);
        assert!(matches!(
            module.protos[0].body.stmts.as_slice(),
            [
                HirStmt::LocalDecl(local_decl),
                HirStmt::If(if_stmt),
                HirStmt::Return(ret),
            ]
                if matches!(local_decl.bindings.as_slice(), [LocalId(0)])
                    && matches!(local_decl.values.as_slice(), [HirExpr::Boolean(true)])
                    && matches!(&if_stmt.cond, HirExpr::LocalRef(LocalId(0)))
                    && matches!(if_stmt.then_block.stmts.as_slice(), [HirStmt::Assign(assign)]
                        if matches!(assign.targets.as_slice(), [HirLValue::Local(LocalId(0))]))
                    && matches!(ret.values.as_slice(), [HirExpr::LocalRef(LocalId(0))])
        ));
    }

    #[test]
    fn promotes_if_merge_temp_into_local_decl() {
        let mut module = HirModule {
            entry: HirProtoRef(0),
            protos: vec![dummy_proto(HirBlock {
                stmts: vec![
                    HirStmt::If(Box::new(HirIf {
                        cond: HirExpr::Boolean(true),
                        then_block: HirBlock {
                            stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                                targets: vec![HirLValue::Temp(TempId(0))],
                                values: vec![HirExpr::Integer(41)],
                            }))],
                        },
                        else_block: Some(HirBlock {
                            stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                                targets: vec![HirLValue::Temp(TempId(0))],
                                values: vec![HirExpr::Integer(7)],
                            }))],
                        }),
                    })),
                    HirStmt::Return(Box::new(HirReturn {
                        values: vec![HirExpr::TempRef(TempId(0))],
                    })),
                ],
            })],
        };

        super::super::simplify_hir(&mut module);

        assert_eq!(module.protos[0].locals.len(), 1);
        assert!(matches!(
            module.protos[0].body.stmts.as_slice(),
            [
                HirStmt::LocalDecl(local_decl),
                HirStmt::If(if_stmt),
                HirStmt::Return(ret),
            ]
                if matches!(local_decl.bindings.as_slice(), [LocalId(0)])
                    && local_decl.values.is_empty()
                    && matches!(if_stmt.then_block.stmts.as_slice(), [HirStmt::Assign(assign)]
                        if matches!(assign.targets.as_slice(), [HirLValue::Local(LocalId(0))]))
                    && matches!(if_stmt.else_block.as_ref().map(|block| block.stmts.as_slice()), Some([HirStmt::Assign(assign)])
                        if matches!(assign.targets.as_slice(), [HirLValue::Local(LocalId(0))]))
                    && matches!(ret.values.as_slice(), [HirExpr::LocalRef(LocalId(0))])
        ));
    }

    fn dummy_proto(body: HirBlock) -> HirProto {
        HirProto {
            id: HirProtoRef(0),
            source: None,
            line_range: crate::parser::ProtoLineRange {
                defined_start: 0,
                defined_end: 0,
            },
            signature: crate::parser::ProtoSignature {
                num_params: 0,
                is_vararg: false,
                has_vararg_param_reg: false,
                named_vararg_table: false,
            },
            params: Vec::new(),
            locals: Vec::new(),
            upvalues: Vec::new(),
            temps: vec![TempId(0), TempId(1)],
            body,
            children: Vec::new(),
        }
    }
}
