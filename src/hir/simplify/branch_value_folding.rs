//! branch-value 收敛：把“分支只是在为同一个 binding 选值”的 HIR 形态收回值语义。
//!
//! 这个文件承接四类已经进入 HIR、但还没有完全结构化的 branch-value 形状：
//! 1. `locals` 前仍以 temp 表示的“所有分支只给同一 target 选值”树；
//! 2. fallback CFG 遗留的 `if cond then x=v; goto L end; x=d; label L` 壳；
//! 3. `locals` fallback 提升后暴露的 `local X; if cond then X=a else X=b end` 壳；
//! 4. nil-only fallback alias：`local X; if A == nil then X=b else X=A end`。
//!
//! 它依赖前层 HIR/StructureFacts 已经给出合法的 branch、label/goto 和 binding 边界；
//! 这里只做 HIR 内部的语义收敛，不重新解释 CFG，也不会跨过仍有其它入边的 label。
//! 对需要复制默认值的形状，只允许复制无副作用的常量或引用，避免为了可读性改变求值语义。
//! nil fallback 不会被恢复成 `A or b`，因为 `or` 会把 `false` 也视为 fallback 条件。
//!
//! 对 Temp/Local binding，除了平铺的两臂形状以外，结构恢复阶段经常因为短路条件被翻译成多层嵌套 `if`
//! 而把同一个 binding 的赋值散落在树形 if/else 的所有叶子上。raw Temp 没有稳定的中间
//! 源码身份，因此由 `BranchValueDecisionBuilder` 一次建立完整 Decision 后统一 finalize；
//! Local 则保留逐层 finalize 的严格恢复边界。两条路径最终都由 logical-simplify 还原
//! 成扁平的 and/or 链，不能为共用实现而放宽 Local 候选。
//! 短路链常见的 guard local 可依靠词法作用域直接消解；raw temp 只有在完整候选根语句之外
//! 没有 touch、候选表达式不再引用它，且没有 debug local 身份时才会提前消解。无法证明的形状
//! 保持原树，交给 `locals::branch_merge` 物化稳定 binding 后在下一轮重试，不能为追求折叠丢状态。
//! guard producer 的结果通过 `CurrentValue` 进入 Decision 结果臂，带调用或动态读取的 producer
//! 也只在原位置求值一次，不能把同一表达式 clone 成条件与结果后重复执行。
//! raw Temp 收成值后，仅把本轮新生成的 target 交给 temp-inline 的根级 Call/Return 定向入口；
//! 不能重跑全 proto 的普通内联，也不能让 `locals` 延后到另一个 phase。
//! goto/label 壳先建立一次 label facts，再选择不交叉区间线性重建 block；独立候选不会每命中一个
//! 就重新扫描整块。
//!
//! 例子：
//! - 输入：`local l0; if cond then l0 = "a" else l0 = "b" end`
//! - 输出：`local l0 = cond and "a" or "b"`
//! - 输入：`local l0; if c1 then if c2 then l0 = a else l0 = b end else l0 = c end`
//! - 输出：`local l0 = c1 and (c2 and a or b) or c`
//! - 输入：`t0=v; if t0 then t1=t0 else t1=d end; use(t1)`，且 t0 无其它 touch/capture
//! - 输出：`t1=v or d; use(t1)`
//! - 输入：`if a then if b then t=v; goto L end end; t=0; label L`
//! - 输出：`if a then if b then t=v else t=0 end else t=0 end`

use std::collections::{BTreeMap, BTreeSet};

use super::label_refs::count_label_references;
use super::local_shapes::empty_single_local_decl_binding;
use super::mention::{block_mentions_local, expr_mentions_local, expr_mentions_temp};
use super::temp_inline::inline_exposed_branch_value_sinks_in_proto_with_facts;
use super::temp_touch::collect_temp_refs_by_stmt;
use super::walk::{HirRewritePass, rewrite_proto};
use crate::ast::{DecompileDialect, ReadabilityOptions};
use crate::hir::HirLabelId;
use crate::hir::common::{
    HirAssign, HirBinaryExpr, HirBinaryOpKind, HirBlock, HirDecisionExpr, HirDecisionNode,
    HirDecisionNodeRef, HirDecisionTarget, HirExpr, HirIf, HirLValue, HirLocalDecl, HirProto,
    HirStmt, HirUnaryOpKind, HirValuePack, LocalId, TempId,
};
use crate::hir::promotion::ProtoPromotionFacts;

mod decision_builder;

use decision_builder::BranchValueDecisionBuilder;

pub(super) fn fold_branch_values_in_proto(
    proto: &mut HirProto,
    readability: ReadabilityOptions,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
) -> bool {
    let exposed_temps = fold_root_branch_value_temps(proto);
    let raw_temp_changed = !exposed_temps.is_empty();
    inline_exposed_branch_value_sinks_in_proto_with_facts(
        proto,
        &exposed_temps,
        readability,
        facts,
        dialect,
    );
    let label_refs = count_label_references(&proto.body.stmts);
    let other_changed = rewrite_proto(
        proto,
        &mut BranchValuePass {
            label_refs: &label_refs,
        },
    );
    raw_temp_changed || other_changed
}

struct BranchValuePass<'a> {
    label_refs: &'a BTreeMap<HirLabelId, usize>,
}

impl HirRewritePass for BranchValuePass<'_> {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        let goto_changed =
            fold_branch_value_goto_labels_in_block(&mut block.stmts, self.label_refs);
        let nil_decision_changed = fold_nil_fallback_decision_locals_in_block(&mut block.stmts);
        let nil_fallback_changed = fold_nil_fallback_alias_locals_in_block(&mut block.stmts);
        let local_changed = fold_branch_value_locals_in_block(&mut block.stmts);
        goto_changed || nil_decision_changed || nil_fallback_changed || local_changed
    }
}

/// 把 `local target = Decision(source == nil ? fallback : source)` 物化为
/// `local target = source; if target == nil then target = fallback end`。
///
/// 结构化 HIR 有时会把已经恢复过的 nil fallback 重新编码成一个单节点 Decision，
/// 尤其是在源码经过一轮反编译后再次编译时。把它留给 Decision elimination 会丢掉
/// 原本已经证明的“无 else fallback”形状；这里仅接受 direct local、单节点 DAG 和
/// 不读取 target 的 fallback，因此不会重复求值 source，也不会改变 fallback 的时序。
fn fold_nil_fallback_decision_locals_in_block(stmts: &mut Vec<HirStmt>) -> bool {
    let mut changed = false;
    let mut index = 0;
    while index < stmts.len() {
        let Some(rewrite) = nil_fallback_decision_rewrite(&stmts[index]) else {
            index += 1;
            continue;
        };

        stmts[index] = HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: vec![rewrite.target],
            values: HirValuePack::fixed(vec![HirExpr::LocalRef(rewrite.source)]),
        }));
        stmts.insert(
            index + 1,
            HirStmt::If(Box::new(HirIf {
                cond: nil_check_for_local(rewrite.target),
                then_block: HirBlock {
                    stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Local(rewrite.target)],
                        values: HirValuePack::fixed(vec![rewrite.fallback]),
                    }))],
                },
                else_block: None,
            })),
        );
        changed = true;
        index += 2;
    }
    changed
}

struct NilFallbackDecisionRewrite {
    target: LocalId,
    source: LocalId,
    fallback: HirExpr,
}

fn nil_fallback_decision_rewrite(stmt: &HirStmt) -> Option<NilFallbackDecisionRewrite> {
    let HirStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    let [target] = local_decl.bindings.as_slice() else {
        return None;
    };
    let [HirExpr::Decision(decision)] = local_decl.values.fixed.as_slice() else {
        return None;
    };
    // 候选拒绝[SemanticBarrier:ValueArity]：fixed Decision 后仍有 tail 时，改写成单值 local 会丢失 tail 的值宽度。
    // 候选拒绝[ProofIncomplete]：多节点 nil Decision 尚未证明可物化成单个无 else fallback；应消费完整 Decision 路径事实。
    if local_decl.values.tail.is_some() || decision.nodes.len() != 1 {
        return None;
    }
    assert_eq!(
        decision.entry.index(),
        0,
        "single-node HIR Decision entry must reference its only node"
    );
    let node = &decision.nodes[0];
    let source = nil_check_local(&node.test)?;
    let (fallback, source_target) = match (&node.truthy, &node.falsy) {
        (
            HirDecisionTarget::Expr(fallback),
            HirDecisionTarget::Expr(HirExpr::LocalRef(source_target)),
        ) => (fallback.clone(), *source_target),
        _ => return None,
    };
    // 候选拒绝[SemanticBarrier:Scope]：`target == source` 或 fallback 读取 target 时，移到声明后的 if 会把 RHS 的外层读取改成新局部读取。
    if source_target != source || *target == source || expr_mentions_local(&fallback, *target) {
        return None;
    }
    Some(NilFallbackDecisionRewrite {
        target: *target,
        source,
        fallback,
    })
}

/// 扫描 block 中的 fallback label/goto branch-value 壳，先收回普通 `if/else`。
fn fold_branch_value_goto_labels_in_block(
    stmts: &mut Vec<HirStmt>,
    label_refs: &BTreeMap<HirLabelId, usize>,
) -> bool {
    let folds = plan_branch_value_goto_folds(stmts, label_refs);
    if folds.is_empty() {
        return false;
    }
    apply_branch_value_goto_folds(stmts, folds);
    true
}

/// 扫描 block 中的 `local X; if cond then X=a else X=b end` 形状，
/// 尝试把它收回 `local X = cond and a or b` 一类的值表达式。
fn fold_branch_value_locals_in_block(stmts: &mut Vec<HirStmt>) -> bool {
    let mut changed = false;
    let original = std::mem::take(stmts);
    let mut rewritten = Vec::with_capacity(original.len());
    let mut original = original.into_iter().peekable();
    while let Some(stmt) = original.next() {
        let Some((binding, value)) = original
            .peek()
            .and_then(|next| collapsible_branch_value_local(&stmt, next))
        else {
            rewritten.push(stmt);
            continue;
        };
        original.next();
        rewritten.push(HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: vec![binding],
            values: HirValuePack::fixed(vec![value]),
        })));
        changed = true;
    }
    *stmts = rewritten;
    changed
}

/// `locals` 之前只处理 proto 根 block 的机械 temp 值树。每个 proto 单独调用，因此同号
/// TempId 不会跨 child proto 混合；现有 per-stmt touch facts 证明 guard 没有逃出候选语句。
fn fold_root_branch_value_temps(proto: &mut HirProto) -> Vec<TempId> {
    if !proto
        .body
        .stmts
        .iter()
        .any(|stmt| matches!(stmt, HirStmt::If(_)))
    {
        return Vec::new();
    }

    let refs_by_stmt = collect_temp_refs_by_stmt(&proto.body.stmts);
    let mut stmt_touch_counts = BTreeMap::<TempId, usize>::new();
    for temps in &refs_by_stmt {
        for temp in temps {
            *stmt_touch_counts.entry(*temp).or_default() += 1;
        }
    }

    let mut exposed_temps = Vec::new();
    for stmt in &mut proto.body.stmts {
        let Some((target, replacement, guards)) = collapsible_branch_value_temp(stmt) else {
            continue;
        };
        let guards_are_mechanical = guards.iter().all(|guard| {
            // 候选拒绝[SemanticBarrier:Lifetime]：guard 若还被其它根语句读取，删除其赋值会留下未定义/旧 epoch 的 temp 读取。
            stmt_touch_counts.get(guard) == Some(&1)
                // 候选拒绝[LayerBoundary]：带 debug-local identity 的 temp 由 locals/source identity 层决定，HIR 值折叠不能抢先删除。
                && proto
                    .temp_debug_locals
                    .get(guard.index())
                    .is_none_or(Option::is_none)
        });
        if guards_are_mechanical {
            *stmt = replacement;
            exposed_temps.push(target);
        }
    }
    exposed_temps
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
            values: HirValuePack::fixed(vec![HirExpr::LocalRef(rewrite.source)]),
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
    // 候选拒绝[SemanticBarrier:ControlFlow]：`local x; if a==nil then x=b end` 的 a 非 nil 路径保留 nil，改写成 `local x=a` 会变成 a。
    let else_block = if_stmt.else_block.as_ref()?;
    let (source, fallback_block) = if let Some(source) = nil_check_local(&if_stmt.cond) {
        let then_value = terminal_local_assign_value(&if_stmt.then_block, target)?;
        let else_value = single_local_assign_value(else_block, target)?;
        if !matches!(else_value, HirExpr::LocalRef(local) if *local == source)
            || expr_mentions_local(then_value, target)
        {
            // 候选拒绝[ProofIncomplete]：fallback 读取空声明 target 时理论上仍见 nil，但需先证明 source != target 与整个 prefix 不改写 target。
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
            // 候选拒绝[ProofIncomplete]：negated fallback 读取空声明 target 时需证明 source != target 与 fallback prefix 的 target epoch。
            return None;
        }
        (source, else_block.clone())
    };
    if target == source {
        // 候选拒绝[SemanticBarrier:Scope]：最小 HIR `outer x=7; local x; if x==nil then x=1 else x=x end` 得 1，改成 `local x=x` 后得 7；官方编译器会先消去 `x=x`，尚无能命中该接受点的源码回归。
        return None;
    }
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

#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
enum BranchValueBinding {
    Temp(TempId),
    Local(LocalId),
}

impl BranchValueBinding {
    fn from_lvalue(lvalue: &HirLValue) -> Option<Self> {
        match lvalue {
            HirLValue::Temp(temp) => Some(Self::Temp(*temp)),
            HirLValue::Local(local) => Some(Self::Local(*local)),
            HirLValue::Param(_)
            | HirLValue::Upvalue(_)
            | HirLValue::Global(_)
            | HirLValue::TableAccess(_) => None,
        }
    }

    fn into_lvalue(self) -> HirLValue {
        match self {
            Self::Temp(temp) => HirLValue::Temp(temp),
            Self::Local(local) => HirLValue::Local(local),
        }
    }

    fn mentions_expr(self, expr: &HirExpr) -> bool {
        match self {
            Self::Temp(temp) => expr_mentions_temp(expr, temp),
            Self::Local(local) => expr_mentions_local(expr, local),
        }
    }
}

fn single_local_assign_value(block: &HirBlock, target: LocalId) -> Option<&HirExpr> {
    let [HirStmt::Assign(assign)] = block.stmts.as_slice() else {
        return None;
    };
    single_assign_value(assign, BranchValueBinding::Local(target))
}

fn terminal_local_assign_value(block: &HirBlock, target: LocalId) -> Option<&HirExpr> {
    let HirStmt::Assign(assign) = block.stmts.last()? else {
        return None;
    };
    single_assign_value(assign, BranchValueBinding::Local(target))
}

fn collapsible_branch_value_local(
    local_decl_stmt: &HirStmt,
    if_stmt: &HirStmt,
) -> Option<(LocalId, HirExpr)> {
    let binding = empty_single_local_decl_binding(local_decl_stmt)?;
    let HirStmt::If(if_stmt) = if_stmt else {
        return None;
    };
    let value = branch_value_expr(BranchValueBinding::Local(binding), if_stmt)?;
    Some((binding, value))
}

fn collapsible_branch_value_temp(stmt: &HirStmt) -> Option<(TempId, HirStmt, BTreeSet<TempId>)> {
    let HirStmt::If(if_stmt) = stmt else {
        return None;
    };
    let binding = branch_value_binding_in_block(&if_stmt.then_block)?;
    let BranchValueBinding::Temp(target) = binding else {
        return None;
    };
    let mut builder = BranchValueDecisionBuilder::new();
    let root = builder.collapse_if(if_stmt, binding)?;
    // raw temp 没有 local 壳提供稳定的中间边界；若整棵树尚不能收成值表达式，
    // 只折叠内层会生成一份新的控制形状，并可能让下一次反编译失去原短路 owner。
    // 因此这里全有或全无，保持原树交给 locals 后的路径继续处理。
    let (value, guards) = builder.finish(root, binding)?;
    let replacement = assign_binding_value(binding, value);
    Some((target, replacement, guards))
}

fn branch_value_expr(binding: BranchValueBinding, if_stmt: &HirIf) -> Option<HirExpr> {
    let truthy = try_collapse_block_to_value(&if_stmt.then_block, binding)?;
    // 候选拒绝[ProofIncomplete]：空 local 的无 else 路径可取 nil，但当前 builder 没有把“未赋值 epoch == nil”作为 falsy target 事实。
    let falsy = try_collapse_block_to_value(if_stmt.else_block.as_ref()?, binding)?;
    if binding.mentions_expr(&if_stmt.cond)
        || binding.mentions_expr(&truthy)
        || binding.mentions_expr(&falsy)
    {
        // 候选拒绝[SemanticBarrier:Scope]：`local x; if x then x=a else x=b end` 若改成 initializer，RHS 的 x 会解析到外层而非已声明的 nil local。
        return None;
    }
    finalize_branch_value_targets(
        &if_stmt.cond,
        HirDecisionTarget::Expr(truthy),
        HirDecisionTarget::Expr(falsy),
    )
}

fn try_collapse_block_to_value(block: &HirBlock, binding: BranchValueBinding) -> Option<HirExpr> {
    match block.stmts.as_slice() {
        [HirStmt::Assign(assign)] => single_assign_value(assign, binding).cloned(),
        [HirStmt::If(if_stmt)] => branch_value_expr(binding, if_stmt),
        [HirStmt::LocalDecl(decl), HirStmt::If(if_stmt)] => {
            collapse_local_guard_pattern(decl, if_stmt, binding)
        }
        // 候选拒绝[ProofIncomplete]：其它叶块可能仅含可搬移的中性语句，也可能有 call/control effect；需逐句路径 effect summary，不能按长度 blanket 判定。
        _ => None,
    }
}

fn collapse_local_guard_pattern(
    decl: &HirLocalDecl,
    if_stmt: &HirIf,
    binding: BranchValueBinding,
) -> Option<HirExpr> {
    let [guard] = decl.bindings.as_slice() else {
        return None;
    };
    let [value] = decl.values.fixed.as_slice() else {
        return None;
    };
    if decl.values.tail.is_some()
        || !matches!(if_stmt.cond, HirExpr::LocalRef(local) if local == *guard)
    {
        return None;
    }
    let [HirStmt::Assign(then_assign)] = if_stmt.then_block.stmts.as_slice() else {
        return None;
    };
    if !matches!(single_assign_value(then_assign, binding)?, HirExpr::LocalRef(local) if local == guard)
    {
        return None;
    }

    // 候选拒绝[ProofIncomplete]：空 output local 的 guard 无 else 路径可取 nil；当前折叠器尚未携带该初始化 epoch 作为 rest target。
    let rest_block = if_stmt.else_block.as_ref()?;
    if expr_mentions_local(value, *guard)
        || binding.mentions_expr(value)
        || block_mentions_local(rest_block, *guard)
    {
        // 候选拒绝[SemanticBarrier:Scope]：删除 guard/local 壳会让 value/rest 中对 guard 或 output binding 的读取改指外层或丢失当前快照。
        return None;
    }
    let rest_value = try_collapse_block_to_value(rest_block, binding)?;
    if binding.mentions_expr(&rest_value) || expr_mentions_local(&rest_value, *guard) {
        // 候选拒绝[SemanticBarrier:Scope]：rest value 仍读取被删除 guard/output binding，直接内联会改变读取的 lexical identity。
        return None;
    }
    finalize_branch_value_targets(
        value,
        HirDecisionTarget::CurrentValue,
        HirDecisionTarget::Expr(rest_value),
    )
}

fn finalize_branch_value_targets(
    cond: &HirExpr,
    truthy: HirDecisionTarget,
    falsy: HirDecisionTarget,
) -> Option<HirExpr> {
    let decision = HirDecisionExpr {
        entry: HirDecisionNodeRef(0),
        nodes: vec![HirDecisionNode {
            id: HirDecisionNodeRef(0),
            test: cond.clone(),
            truthy,
            falsy,
        }],
    };
    let value = crate::hir::decision::finalize_value_decision_expr(decision);
    // 候选拒绝[ProofIncomplete]：共享/不可表达 Decision 尚未收成普通逻辑表达式；应增强 decision collapse，而非把内部 DAG 泄露给 local initializer。
    (!matches!(value, HirExpr::Decision(_))).then_some(value)
}

fn branch_value_binding_in_block(block: &HirBlock) -> Option<BranchValueBinding> {
    match block.stmts.as_slice() {
        [HirStmt::Assign(assign)] => single_assign_binding(assign),
        [HirStmt::If(if_stmt)]
        | [HirStmt::LocalDecl(_), HirStmt::If(if_stmt)]
        | [HirStmt::Assign(_), HirStmt::If(if_stmt)] => {
            branch_value_binding_in_block(&if_stmt.then_block)
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

struct PreparedBranchValueGotoFold {
    start: usize,
    end: usize,
    replacement: HirStmt,
}

fn plan_branch_value_goto_folds(
    stmts: &[HirStmt],
    label_refs: &BTreeMap<HirLabelId, usize>,
) -> Vec<PreparedBranchValueGotoFold> {
    let label_indices = index_top_level_labels(stmts);
    let mut candidates = Vec::new();
    for if_index in 0..stmts.len() {
        if let Some(fold) =
            nested_default_goto_label_fold_at(stmts, if_index, label_refs, &label_indices)
        {
            candidates.push(fold);
            continue;
        }
        if let Some(fold) = direct_goto_label_fold_at(stmts, if_index, label_refs) {
            candidates.push(fold);
        }
    }

    // 右侧候选优先。交叉/包含候选由 fixed-point 下一轮在内层收敛后重试；独立区间
    // 本轮一次处理，避免每命中一个就重建 label facts 并重扫整个 block。
    let mut next_start = stmts.len();
    let mut selected = Vec::new();
    for fold in candidates.into_iter().rev() {
        // 候选搜索裁剪[ConvergenceGuard]：与右侧已选区间交叉/包含的候选留给 fixed-point 下一轮，不是语义拒绝。
        if fold.label_index < next_start {
            next_start = fold.if_index;
            selected.push(fold);
        }
    }
    selected.reverse();
    selected
        .into_iter()
        .filter_map(|fold| prepare_branch_value_goto_fold(stmts, fold))
        .collect()
}

fn direct_goto_label_fold_at(
    stmts: &[HirStmt],
    if_index: usize,
    label_refs: &BTreeMap<HirLabelId, usize>,
) -> Option<BranchValueGotoFold> {
    let label_index = if_index.checked_add(2)?;
    let HirStmt::Label(label) = stmts.get(label_index)? else {
        return None;
    };
    // 候选拒绝[SemanticBarrier:ControlFlow]：join label 若有第二个 goto 入口，删掉 label 会破坏该入口的控制流目标。
    if label_ref_count(label_refs, label.id) != 1
        || !direct_goto_value_matches(stmts.get(if_index)?, stmts.get(if_index + 1)?, label.id)
    {
        return None;
    }
    Some(BranchValueGotoFold {
        if_index,
        default_label_index: if_index + 1,
        label_index,
        kind: BranchValueGotoFoldKind::Direct,
    })
}

fn nested_default_goto_label_fold_at(
    stmts: &[HirStmt],
    if_index: usize,
    label_refs: &BTreeMap<HirLabelId, usize>,
    label_indices: &BTreeMap<HirLabelId, usize>,
) -> Option<BranchValueGotoFold> {
    let default_label = single_goto_if_target(stmts.get(if_index)?)?;
    let default_label_index = label_indices.get(&default_label).copied()?;
    // 候选拒绝[SemanticBarrier:ControlFlow]：default label 位于 if 之前时是回边；把它内联成 else 会把循环执行改成单次分支。
    if default_label_index <= if_index {
        return None;
    }
    let label_index = default_label_index.checked_add(2)?;
    let HirStmt::Label(join_label) = stmts.get(label_index)? else {
        return None;
    };
    // 候选拒绝[SemanticBarrier:ControlFlow]：default/join 任一 label 有额外入口时，删除 label 会截断该入口可达路径。
    if label_ref_count(label_refs, default_label) != 1
        || label_ref_count(label_refs, join_label.id) != 1
        || !nested_default_goto_value_matches(
            &stmts[if_index],
            &stmts[(if_index + 1)..default_label_index],
            &stmts[default_label_index + 1],
            join_label.id,
        )
    {
        return None;
    }
    Some(BranchValueGotoFold {
        if_index,
        default_label_index,
        label_index,
        kind: BranchValueGotoFoldKind::NestedDefault,
    })
}

fn prepare_branch_value_goto_fold(
    stmts: &[HirStmt],
    fold: BranchValueGotoFold,
) -> Option<PreparedBranchValueGotoFold> {
    // 候选拒绝[ConvergenceGuard]：matcher 已验证 if/terminal goto 形状；rewrite 返回 None 表示 plan 与 rewrite 的内部契约漂移。
    let replacement = match fold.kind {
        BranchValueGotoFoldKind::Direct => rewrite_direct_goto_value_if(
            stmts[fold.if_index].clone(),
            stmts[fold.if_index + 1].clone(),
        )?,
        BranchValueGotoFoldKind::NestedDefault => rewrite_nested_default_goto_value_if(
            stmts[fold.if_index].clone(),
            stmts[(fold.if_index + 1)..fold.default_label_index].to_vec(),
            stmts[fold.default_label_index + 1].clone(),
        )?,
    };
    Some(PreparedBranchValueGotoFold {
        start: fold.if_index,
        end: fold.label_index,
        replacement,
    })
}

fn apply_branch_value_goto_folds(
    stmts: &mut Vec<HirStmt>,
    folds: Vec<PreparedBranchValueGotoFold>,
) {
    let original = std::mem::take(stmts);
    let removed = folds
        .iter()
        .map(|fold| fold.end - fold.start)
        .sum::<usize>();
    let mut rewritten = Vec::with_capacity(original.len().saturating_sub(removed));
    let mut original = original.into_iter().enumerate().peekable();

    for fold in folds {
        while original
            .peek()
            .is_some_and(|(index, _)| *index < fold.start)
        {
            let (_, stmt) = original.next().expect("peeked statement must exist");
            rewritten.push(stmt);
        }
        while original.peek().is_some_and(|(index, _)| *index <= fold.end) {
            original.next();
        }
        rewritten.push(fold.replacement);
    }
    rewritten.extend(original.map(|(_, stmt)| stmt));
    *stmts = rewritten;
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
    // 候选拒绝[SemanticBarrier:ControlFlow]：候选 if 已有非空 else 时，安装 fallback else 会覆盖原 false-path 行为。
    if has_non_empty_else(if_stmt) {
        return false;
    }
    let HirStmt::Assign(fallback_assign) = fallback_stmt else {
        return false;
    };
    // Direct fold 只把 fallback 原样移入唯一 false arm；targets 相同即可，RHS 与
    // value-pack 的求值/宽度都留在原 assignment 内，不需要 nested 复制白名单。
    terminal_goto_assign(&if_stmt.then_block, label)
        .is_some_and(|success_assign| success_assign.targets == fallback_assign.targets)
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
    // 候选拒绝[SemanticBarrier:ControlFlow]：outer if 已有 false-path 时，改写生成的 fallback else 会覆盖这条既有路径。
    if has_non_empty_else(outer_if) || single_goto_if_target(outer_stmt).is_none() {
        return false;
    }
    let Some((fallback_target, fallback_value)) = single_assign(fallback_stmt) else {
        return false;
    };
    // 候选拒绝[ProofIncomplete]：fallback 只复制到互斥分支且每条路径一次；当前 target/value 白名单缺少路径互斥与 lvalue 求值时点证明。
    if !target_allows_default_duplication(fallback_target)
        || !is_branch_default_value_expr(fallback_value)
    {
        return false;
    }
    let [.., HirStmt::If(inner_if)] = prefix_stmts else {
        return false;
    };
    // 候选拒绝[SemanticBarrier:ControlFlow]：inner if 已有 else 时，写入 fallback else 会覆盖原 false-path 行为。
    if has_non_empty_else(inner_if) {
        return false;
    }
    terminal_goto_assign_target(&inner_if.then_block, label)
        .is_some_and(|success_target| success_target == fallback_target)
}

fn rewrite_direct_goto_value_if(if_stmt: HirStmt, fallback_stmt: HirStmt) -> Option<HirStmt> {
    // 候选拒绝[ConvergenceGuard]：direct matcher 已证明输入是 if 且 then 以目标 goto 终结，以下失败仅表示内部不变量损坏。
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
    // 候选拒绝[ConvergenceGuard]：nested matcher 已证明 outer/inner if 与 terminal goto；以下失败仅表示 plan/rewrite 不变量损坏。
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
    let assign = terminal_goto_assign(block, label)?;
    let [target] = assign.targets.as_slice() else {
        return None;
    };
    let [_] = assign.values.fixed.as_slice() else {
        return None;
    };
    if assign.values.tail.is_some() {
        return None;
    }
    Some(target)
}

fn terminal_goto_assign(block: &HirBlock, label: HirLabelId) -> Option<&HirAssign> {
    let [.., HirStmt::Assign(assign), HirStmt::Goto(goto)] = block.stmts.as_slice() else {
        return None;
    };
    if goto.target != label {
        return None;
    }
    Some(assign)
}

fn label_ref_count(label_refs: &BTreeMap<HirLabelId, usize>, label: HirLabelId) -> usize {
    label_refs.get(&label).copied().unwrap_or(0)
}

fn single_assign(stmt: &HirStmt) -> Option<(&HirLValue, &HirExpr)> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [target] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.fixed.as_slice() else {
        return None;
    };
    if assign.values.tail.is_some() {
        return None;
    }
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
            | HirExpr::Vector(_)
            | HirExpr::Complex { .. }
            | HirExpr::ParamRef(_)
            | HirExpr::LocalRef(_)
            | HirExpr::UpvalueRef(_)
            | HirExpr::TempRef(_)
            | HirExpr::GlobalRef(_)
    )
}

fn single_assign_value(assign: &HirAssign, binding: BranchValueBinding) -> Option<&HirExpr> {
    let [target] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.fixed.as_slice() else {
        return None;
    };
    if assign.values.tail.is_some() {
        return None;
    }
    (BranchValueBinding::from_lvalue(target) == Some(binding)).then_some(value)
}

fn single_assign_binding(assign: &HirAssign) -> Option<BranchValueBinding> {
    let [target] = assign.targets.as_slice() else {
        return None;
    };
    let [_] = assign.values.fixed.as_slice() else {
        return None;
    };
    if assign.values.tail.is_some() {
        return None;
    }
    BranchValueBinding::from_lvalue(target)
}

fn assign_binding_value(binding: BranchValueBinding, value: HirExpr) -> HirStmt {
    HirStmt::Assign(Box::new(HirAssign {
        targets: vec![binding.into_lvalue()],
        values: HirValuePack::fixed(vec![value]),
    }))
}

/// 处理 `local LX = v; if LX then assign binding = LX else REST end` 这一短路守卫形态。
///
/// 该形态来自结构恢复阶段把 `binding = v or RESTV` 这种短路赋值展开成"先把 `v` 物化到
/// 新 temp `LX`，再用 `LX` 做条件判断"的中间形态。如果 `LX` 在这之外没有被引用过，
/// 就可以重新折回 `binding = v or RESTV`，避免给最终输出留下毫无意义的物化壳。
struct RawTempGuardShape<'a> {
    guard: TempId,
    binding: BranchValueBinding,
    value: &'a HirExpr,
    rest_block: &'a HirBlock,
    guard_is_truthy_value: bool,
}

fn raw_temp_guard_shape<'a>(
    assign_stmt: &'a HirStmt,
    if_stmt: &'a HirStmt,
) -> Option<RawTempGuardShape<'a>> {
    let (HirLValue::Temp(guard), value) = single_assign(assign_stmt)? else {
        return None;
    };
    let guard = *guard;
    let HirStmt::If(if_stmt) = if_stmt else {
        return None;
    };
    if !matches!(if_stmt.cond, HirExpr::TempRef(temp) if temp == guard) {
        return None;
    }
    // 候选拒绝[SemanticBarrier:ControlFlow]：`t=v; if t then out=t end` 的 false-path 保留 out 旧值，不能构造成总有结果的短路值。
    let else_block = if_stmt.else_block.as_ref()?;
    let (binding, rest_block, guard_is_truthy_value) =
        if let Some(binding) = block_assigns_binding_from_temp(&if_stmt.then_block, guard) {
            (binding, else_block, true)
        } else {
            let binding = block_assigns_binding_from_temp(else_block, guard)?;
            (binding, &if_stmt.then_block, false)
        };
    // 候选拒绝[ProofIncomplete]：binding 与 guard 相同时可形成原地短路更新，但需证明 CurrentValue 指向赋值后的 guard epoch 才能折叠。
    if binding == BranchValueBinding::Temp(guard) {
        return None;
    }
    Some(RawTempGuardShape {
        guard,
        binding,
        value,
        rest_block,
        guard_is_truthy_value,
    })
}

fn block_assigns_binding_from_temp(block: &HirBlock, temp: TempId) -> Option<BranchValueBinding> {
    let [HirStmt::Assign(assign)] = block.stmts.as_slice() else {
        return None;
    };
    let binding = single_assign_binding(assign)?;
    matches!(single_assign_value(assign, binding)?, HirExpr::TempRef(value) if *value == temp)
        .then_some(binding)
}
