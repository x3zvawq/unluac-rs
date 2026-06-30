//! branch-value 收敛：把“分支只是在为同一个 binding 选值”的 HIR 形态收回值语义。
//!
//! 这个文件承接两类已经进入 HIR、但还没有完全结构化的 branch-value 形状：
//! 1. fallback CFG 遗留的 `if cond then x=v; goto L end; x=d; label L` 壳；
//! 2. `locals` pass 提升 temp 后暴露出来的 `local X; if cond then X=a else X=b end` 壳；
//! 3. nil-only fallback alias：`local X; if A == nil then X=b else X=A end`。
//!
//! 它依赖前层 HIR/StructureFacts 已经给出合法的 branch、label/goto 和 binding 边界；
//! 这里只做 HIR 内部的语义收敛，不重新解释 CFG，也不会跨过仍有其它入边的 label。
//! 对需要复制默认值的形状，只允许复制无副作用的常量或引用，避免为了可读性改变求值语义。
//! nil fallback 不会被恢复成 `A or b`，因为 `or` 会把 `false` 也视为 fallback 条件。
//!
//! 对 local 形态，除了平铺的两臂形状以外，结构恢复阶段经常因为短路条件被翻译成多层嵌套 `if`
//! 而把同一个 binding 的赋值散落在树形 if/else 的所有叶子上。这里通过 `try_collapse_block_to_value`
//! 递归地把"每条路径都只是给 binding 赋一个值"的子树折回单条 Decision 表达式，
//! 让后续 `decision::collapse_value_decision_expr` + `logical-simplify` 还原成扁平的 and/or 链。
//! 以及短路链常见的"`local LX = expr; if LX then X = LX else REST`"形态也会被识别成 `expr or REST`。
//!
//! 例子：
//! - 输入：`local l0; if cond then l0 = "a" else l0 = "b" end`
//! - 输出：`local l0 = cond and "a" or "b"`
//! - 输入：`local l0; if c1 then if c2 then l0 = a else l0 = b end else l0 = c end`
//! - 输出：`local l0 = c1 and (c2 and a or b) or c`
//! - 输入：`if a then if b then t=v; goto L end end; t=0; label L`
//! - 输出：`if a then if b then t=v else t=0 end else t=0 end`

use std::collections::BTreeMap;

use super::local_shapes::{empty_single_local_decl_binding, matches_local_lvalue};
use super::mention::{block_mentions_local, expr_mentions_local};
use super::visit::HirVisitor;
use super::walk::{HirRewritePass, rewrite_proto};
use crate::hir::HirLabelId;
use crate::hir::common::{
    HirAssign, HirBinaryExpr, HirBinaryOpKind, HirBlock, HirDecisionExpr, HirDecisionNode,
    HirDecisionNodeRef, HirDecisionTarget, HirExpr, HirIf, HirLValue, HirLocalDecl, HirProto,
    HirStmt, HirUnaryOpKind, LocalId,
};

pub(super) fn fold_branch_values_in_proto(proto: &mut HirProto) -> bool {
    rewrite_proto(proto, &mut BranchValuePass)
}

struct BranchValuePass;

impl HirRewritePass for BranchValuePass {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        let goto_changed = fold_branch_value_goto_labels_in_block(&mut block.stmts);
        let nil_fallback_changed = fold_nil_fallback_alias_locals_in_block(&mut block.stmts);
        let local_changed = fold_branch_value_locals_in_block(&mut block.stmts);
        goto_changed || nil_fallback_changed || local_changed
    }
}

/// 扫描 block 中的 fallback label/goto branch-value 壳，先收回普通 `if/else`。
fn fold_branch_value_goto_labels_in_block(stmts: &mut Vec<HirStmt>) -> bool {
    let mut changed = false;

    while let Some(fold) = find_branch_value_goto_label_fold(stmts) {
        match fold.kind {
            BranchValueGotoFoldKind::Direct => {
                let if_stmt = stmts[fold.if_index].clone();
                let fallback_stmt = stmts[fold.if_index + 1].clone();
                let Some(rewritten) = rewrite_direct_goto_value_if(if_stmt, fallback_stmt) else {
                    break;
                };
                stmts[fold.if_index] = rewritten;
                stmts.drain((fold.if_index + 1)..=fold.label_index);
            }
            BranchValueGotoFoldKind::NestedDefault => {
                let outer_stmt = stmts[fold.if_index].clone();
                let prefix_stmts = stmts[(fold.if_index + 1)..fold.default_label_index].to_vec();
                let fallback_stmt = stmts[fold.default_label_index + 1].clone();
                let Some(rewritten) =
                    rewrite_nested_default_goto_value_if(outer_stmt, prefix_stmts, fallback_stmt)
                else {
                    break;
                };
                stmts[fold.if_index] = rewritten;
                stmts.drain((fold.if_index + 1)..=fold.label_index);
            }
        }
        changed = true;
    }

    changed
}

/// 扫描 block 中的 `local X; if cond then X=a else X=b end` 形状，
/// 尝试把它收回 `local X = cond and a or b` 一类的值表达式。
fn fold_branch_value_locals_in_block(stmts: &mut Vec<HirStmt>) -> bool {
    let mut changed = false;
    let mut index = 1;

    while index < stmts.len() {
        let Some((binding, value)) =
            collapsible_branch_value_local(&stmts[index - 1], &stmts[index])
        else {
            index += 1;
            continue;
        };

        stmts[index - 1] = HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: vec![binding],
            values: vec![value],
        }));
        stmts.remove(index);
        changed = true;
    }

    changed
}

/// 扫描 block 中相邻的 `local X; if A == nil then X=b else X=A end` 形状，
/// 改写成 `local X=A; if X == nil then X=b end`。
fn fold_nil_fallback_alias_locals_in_block(stmts: &mut [HirStmt]) -> bool {
    let mut changed = false;
    let mut index = 0;

    while index + 1 < stmts.len() {
        let Some(rewrite) = nil_fallback_alias_rewrite(&stmts[index], &stmts[index + 1]) else {
            index += 1;
            continue;
        };

        stmts[index] = HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: vec![rewrite.target],
            values: vec![HirExpr::LocalRef(rewrite.source)],
        }));
        stmts[index + 1] = HirStmt::If(Box::new(HirIf {
            cond: nil_check_for_local(rewrite.target),
            then_block: rewrite.then_block,
            else_block: None,
        }));
        changed = true;
        index += 2;
    }

    changed
}

struct NilFallbackAliasRewrite {
    target: LocalId,
    source: LocalId,
    then_block: HirBlock,
}

fn nil_fallback_alias_rewrite(
    decl_stmt: &HirStmt,
    if_stmt: &HirStmt,
) -> Option<NilFallbackAliasRewrite> {
    let target = empty_single_local_decl_binding(decl_stmt)?;
    let HirStmt::If(if_stmt) = if_stmt else {
        return None;
    };
    let else_block = if_stmt.else_block.as_ref()?;
    let (source, fallback_block) = if let Some(source) = nil_check_local(&if_stmt.cond) {
        let then_value = terminal_local_assign_value(&if_stmt.then_block, target)?;
        let else_value = single_local_assign_value(else_block, target)?;
        if !matches!(else_value, HirExpr::LocalRef(local) if *local == source)
            || expr_mentions_local(then_value, target)
        {
            return None;
        }
        (source, if_stmt.then_block.clone())
    } else {
        let source = negated_nil_check_local(&if_stmt.cond)?;
        let then_value = single_local_assign_value(&if_stmt.then_block, target)?;
        let else_value = terminal_local_assign_value(else_block, target)?;
        if !matches!(then_value, HirExpr::LocalRef(local) if *local == source)
            || expr_mentions_local(else_value, target)
        {
            return None;
        }
        (source, else_block.clone())
    };
    Some(NilFallbackAliasRewrite {
        target,
        source,
        then_block: fallback_block,
    })
}

fn nil_check_local(expr: &HirExpr) -> Option<LocalId> {
    let HirExpr::Binary(binary) = expr else {
        return None;
    };
    if binary.op != HirBinaryOpKind::Eq {
        return None;
    }
    match (&binary.lhs, &binary.rhs) {
        (HirExpr::LocalRef(local), HirExpr::Nil) | (HirExpr::Nil, HirExpr::LocalRef(local)) => {
            Some(*local)
        }
        _ => None,
    }
}

fn negated_nil_check_local(expr: &HirExpr) -> Option<LocalId> {
    let HirExpr::Unary(unary) = expr else {
        return None;
    };
    (unary.op == HirUnaryOpKind::Not)
        .then(|| nil_check_local(&unary.expr))
        .flatten()
}

fn nil_check_for_local(local: LocalId) -> HirExpr {
    HirExpr::Binary(Box::new(HirBinaryExpr {
        op: HirBinaryOpKind::Eq,
        lhs: HirExpr::LocalRef(local),
        rhs: HirExpr::Nil,
    }))
}

fn single_local_assign_value(block: &HirBlock, target: LocalId) -> Option<&HirExpr> {
    let [HirStmt::Assign(assign)] = block.stmts.as_slice() else {
        return None;
    };
    single_assign_value(assign, target)
}

fn terminal_local_assign_value(block: &HirBlock, target: LocalId) -> Option<&HirExpr> {
    let HirStmt::Assign(assign) = block.stmts.last()? else {
        return None;
    };
    single_assign_value(assign, target)
}

fn collapsible_branch_value_local(
    local_decl_stmt: &HirStmt,
    if_stmt: &HirStmt,
) -> Option<(LocalId, HirExpr)> {
    let binding = empty_single_local_decl_binding(local_decl_stmt)?;
    let HirStmt::If(if_stmt) = if_stmt else {
        return None;
    };
    let value = branch_value_expr(binding, if_stmt)?;
    Some((binding, value))
}

fn branch_value_expr(binding: LocalId, if_stmt: &HirIf) -> Option<HirExpr> {
    let truthy = try_collapse_block_to_value(&if_stmt.then_block, binding)?;
    let else_block = if_stmt.else_block.as_ref()?;
    let falsy = try_collapse_block_to_value(else_block, binding)?;
    if expr_mentions_local(&if_stmt.cond, binding)
        || expr_mentions_local(&truthy, binding)
        || expr_mentions_local(&falsy, binding)
    {
        return None;
    }
    finalize_branch_value(&if_stmt.cond, truthy, falsy)
}

fn finalize_branch_value(cond: &HirExpr, truthy: HirExpr, falsy: HirExpr) -> Option<HirExpr> {
    let decision = HirDecisionExpr {
        entry: HirDecisionNodeRef(0),
        nodes: vec![HirDecisionNode {
            id: HirDecisionNodeRef(0),
            test: cond.clone(),
            truthy: HirDecisionTarget::Expr(truthy),
            falsy: HirDecisionTarget::Expr(falsy),
        }],
    };
    let value = crate::hir::decision::finalize_value_decision_expr(decision);
    (!matches!(value, HirExpr::Decision(_))).then_some(value)
}

/// 递归地尝试把一个 block 折叠成"对 `binding` 唯一赋值"的值表达式。
///
/// 支持三种形态：
/// 1. 单条 `assign binding = expr`；
/// 2. 单条 `if cond then THEN else ELSE end`，THEN/ELSE 各自递归满足；
/// 3. `local LX = v; if LX then assign binding = LX else REST` —— 等价于 `v or REST_value`，
///    `LX` 在 if 之外不可见，因此可以把它消解成 `v or REST_value`。
fn try_collapse_block_to_value(block: &HirBlock, binding: LocalId) -> Option<HirExpr> {
    match block.stmts.as_slice() {
        [HirStmt::Assign(assign)] => single_assign_value(assign, binding).cloned(),
        [HirStmt::If(if_stmt)] => branch_value_expr(binding, if_stmt),
        [HirStmt::LocalDecl(decl), HirStmt::If(if_stmt)] => {
            collapse_temp_guard_pattern(decl, if_stmt, binding)
        }
        _ => None,
    }
}

#[derive(Clone, Copy)]
struct BranchValueGotoFold {
    if_index: usize,
    default_label_index: usize,
    label_index: usize,
    kind: BranchValueGotoFoldKind,
}

#[derive(Clone, Copy)]
enum BranchValueGotoFoldKind {
    Direct,
    NestedDefault,
}

fn find_branch_value_goto_label_fold(stmts: &[HirStmt]) -> Option<BranchValueGotoFold> {
    let label_refs = count_label_references(stmts);
    let label_indices = index_top_level_labels(stmts);
    find_nested_default_goto_label_fold(stmts, &label_refs, &label_indices)
        .or_else(|| find_direct_goto_label_fold(stmts, &label_refs))
}

fn find_direct_goto_label_fold(
    stmts: &[HirStmt],
    label_refs: &BTreeMap<HirLabelId, usize>,
) -> Option<BranchValueGotoFold> {
    if stmts.len() < 3 {
        return None;
    }

    for if_index in (0..=(stmts.len() - 3)).rev() {
        let label_index = if_index + 2;
        let HirStmt::Label(label) = &stmts[label_index] else {
            continue;
        };
        if label_ref_count(label_refs, label.id) != 1 {
            continue;
        }
        if direct_goto_value_matches(&stmts[if_index], &stmts[if_index + 1], label.id) {
            return Some(BranchValueGotoFold {
                if_index,
                default_label_index: if_index + 1,
                label_index,
                kind: BranchValueGotoFoldKind::Direct,
            });
        }
    }

    None
}

fn find_nested_default_goto_label_fold(
    stmts: &[HirStmt],
    label_refs: &BTreeMap<HirLabelId, usize>,
    label_indices: &BTreeMap<HirLabelId, usize>,
) -> Option<BranchValueGotoFold> {
    if stmts.len() < 5 {
        return None;
    }

    for if_index in (0..stmts.len()).rev() {
        let Some(default_label) = single_goto_if_target(&stmts[if_index]) else {
            continue;
        };
        let Some(default_label_index) = label_indices.get(&default_label).copied() else {
            continue;
        };
        if default_label_index <= if_index {
            continue;
        }
        let Some(label_index) = default_label_index.checked_add(2) else {
            continue;
        };
        if label_index >= stmts.len() {
            continue;
        }
        let HirStmt::Label(join_label) = &stmts[label_index] else {
            continue;
        };
        if label_ref_count(label_refs, default_label) != 1
            || label_ref_count(label_refs, join_label.id) != 1
        {
            continue;
        }
        let prefix = &stmts[(if_index + 1)..default_label_index];
        if nested_default_goto_value_matches(
            &stmts[if_index],
            prefix,
            &stmts[default_label_index + 1],
            join_label.id,
        ) {
            return Some(BranchValueGotoFold {
                if_index,
                default_label_index,
                label_index,
                kind: BranchValueGotoFoldKind::NestedDefault,
            });
        }
    }

    None
}

fn index_top_level_labels(stmts: &[HirStmt]) -> BTreeMap<HirLabelId, usize> {
    stmts
        .iter()
        .enumerate()
        .filter_map(|(index, stmt)| match stmt {
            HirStmt::Label(label) => Some((label.id, index)),
            _ => None,
        })
        .collect()
}

fn direct_goto_value_matches(
    if_stmt: &HirStmt,
    fallback_stmt: &HirStmt,
    label: HirLabelId,
) -> bool {
    let HirStmt::If(if_stmt) = if_stmt else {
        return false;
    };
    if has_non_empty_else(if_stmt) {
        return false;
    }
    let Some((fallback_target, fallback_value)) = single_assign(fallback_stmt) else {
        return false;
    };
    if !target_allows_default_duplication(fallback_target)
        || !is_branch_default_value_expr(fallback_value)
    {
        return false;
    }
    terminal_goto_assign_target(&if_stmt.then_block, label)
        .is_some_and(|success_target| success_target == fallback_target)
}

fn nested_default_goto_value_matches(
    outer_stmt: &HirStmt,
    prefix_stmts: &[HirStmt],
    fallback_stmt: &HirStmt,
    label: HirLabelId,
) -> bool {
    let HirStmt::If(outer_if) = outer_stmt else {
        return false;
    };
    if has_non_empty_else(outer_if) || single_goto_if_target(outer_stmt).is_none() {
        return false;
    }
    let Some((fallback_target, fallback_value)) = single_assign(fallback_stmt) else {
        return false;
    };
    if !target_allows_default_duplication(fallback_target)
        || !is_branch_default_value_expr(fallback_value)
    {
        return false;
    }
    let [.., HirStmt::If(inner_if)] = prefix_stmts else {
        return false;
    };
    if has_non_empty_else(inner_if) {
        return false;
    }
    terminal_goto_assign_target(&inner_if.then_block, label)
        .is_some_and(|success_target| success_target == fallback_target)
}

fn rewrite_direct_goto_value_if(if_stmt: HirStmt, fallback_stmt: HirStmt) -> Option<HirStmt> {
    let HirStmt::If(mut if_stmt) = if_stmt else {
        return None;
    };
    if_stmt.then_block.stmts.pop()?;
    if_stmt.else_block = Some(HirBlock {
        stmts: vec![fallback_stmt],
    });
    Some(HirStmt::If(if_stmt))
}

fn rewrite_nested_default_goto_value_if(
    outer_stmt: HirStmt,
    prefix_stmts: Vec<HirStmt>,
    fallback_stmt: HirStmt,
) -> Option<HirStmt> {
    let HirStmt::If(mut outer_if) = outer_stmt else {
        return None;
    };
    outer_if.cond = outer_if.cond.negate();
    let mut then_stmts = prefix_stmts;
    let Some(HirStmt::If(inner_stmt)) = then_stmts.pop() else {
        return None;
    };
    let mut inner_if = *inner_stmt;
    inner_if.then_block.stmts.pop()?;
    inner_if.else_block = Some(HirBlock {
        stmts: vec![fallback_stmt.clone()],
    });
    then_stmts.push(HirStmt::If(Box::new(inner_if)));
    outer_if.then_block = HirBlock { stmts: then_stmts };
    outer_if.else_block = Some(HirBlock {
        stmts: vec![fallback_stmt],
    });
    Some(HirStmt::If(outer_if))
}

fn single_goto_if_target(stmt: &HirStmt) -> Option<HirLabelId> {
    let HirStmt::If(if_stmt) = stmt else {
        return None;
    };
    if has_non_empty_else(if_stmt) {
        return None;
    }
    let [HirStmt::Goto(goto)] = if_stmt.then_block.stmts.as_slice() else {
        return None;
    };
    Some(goto.target)
}

fn has_non_empty_else(if_stmt: &HirIf) -> bool {
    if_stmt
        .else_block
        .as_ref()
        .is_some_and(|block| !block.stmts.is_empty())
}

fn terminal_goto_assign_target(block: &HirBlock, label: HirLabelId) -> Option<&HirLValue> {
    let [.., HirStmt::Assign(assign), HirStmt::Goto(goto)] = block.stmts.as_slice() else {
        return None;
    };
    if goto.target != label {
        return None;
    }
    let [target] = assign.targets.as_slice() else {
        return None;
    };
    let [_] = assign.values.as_slice() else {
        return None;
    };
    Some(target)
}

fn count_label_references(stmts: &[HirStmt]) -> BTreeMap<HirLabelId, usize> {
    let mut collector = LabelReferenceCount::default();
    super::visit::visit_stmts(stmts, &mut collector);
    collector.counts
}

fn label_ref_count(label_refs: &BTreeMap<HirLabelId, usize>, label: HirLabelId) -> usize {
    label_refs.get(&label).copied().unwrap_or(0)
}

#[derive(Default)]
struct LabelReferenceCount {
    counts: BTreeMap<HirLabelId, usize>,
}

impl HirVisitor for LabelReferenceCount {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        let HirStmt::Goto(goto_stmt) = stmt else {
            return;
        };
        *self.counts.entry(goto_stmt.target).or_default() += 1;
    }
}

fn single_assign(stmt: &HirStmt) -> Option<(&HirLValue, &HirExpr)> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [target] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.as_slice() else {
        return None;
    };
    Some((target, value))
}

fn target_allows_default_duplication(target: &HirLValue) -> bool {
    matches!(target, HirLValue::Temp(_) | HirLValue::Local(_))
}

fn is_branch_default_value_expr(expr: &HirExpr) -> bool {
    matches!(
        expr,
        HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::Int64(_)
            | HirExpr::UInt64(_)
            | HirExpr::Complex { .. }
            | HirExpr::ParamRef(_)
            | HirExpr::LocalRef(_)
            | HirExpr::UpvalueRef(_)
            | HirExpr::TempRef(_)
            | HirExpr::GlobalRef(_)
    )
}

fn single_assign_value(assign: &HirAssign, binding: LocalId) -> Option<&HirExpr> {
    let [target] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.as_slice() else {
        return None;
    };
    matches_local_lvalue(target, binding).then_some(value)
}

/// 处理 `local LX = v; if LX then assign binding = LX else REST end` 这一短路守卫形态。
///
/// 该形态来自结构恢复阶段把 `binding = v or RESTV` 这种短路赋值展开成"先把 `v` 物化到
/// 新 temp `LX`，再用 `LX` 做条件判断"的中间形态。如果 `LX` 在这之外没有被引用过，
/// 就可以重新折回 `binding = v or RESTV`，避免给最终输出留下毫无意义的物化壳。
fn collapse_temp_guard_pattern(
    decl: &HirLocalDecl,
    if_stmt: &HirIf,
    binding: LocalId,
) -> Option<HirExpr> {
    let [lx] = decl.bindings.as_slice() else {
        return None;
    };
    let [lx_value] = decl.values.as_slice() else {
        return None;
    };
    let lx = *lx;

    // cond 必须就是 `LocalRef(lx)`
    let HirExpr::LocalRef(cond_local) = &if_stmt.cond else {
        return None;
    };
    if *cond_local != lx {
        return None;
    }

    // then 分支必须就是 `assign binding = LocalRef(lx)`
    let [HirStmt::Assign(then_assign)] = if_stmt.then_block.stmts.as_slice() else {
        return None;
    };
    let then_value = single_assign_value(then_assign, binding)?;
    let HirExpr::LocalRef(then_local) = then_value else {
        return None;
    };
    if *then_local != lx {
        return None;
    }

    let else_block = if_stmt.else_block.as_ref()?;
    if expr_mentions_local(lx_value, lx)
        || expr_mentions_local(lx_value, binding)
        || block_mentions_local(else_block, lx)
    {
        return None;
    }
    let rest_value = try_collapse_block_to_value(else_block, binding)?;
    if expr_mentions_local(&rest_value, binding) || expr_mentions_local(&rest_value, lx) {
        return None;
    }

    finalize_branch_value(lx_value, lx_value.clone(), rest_value)
}
