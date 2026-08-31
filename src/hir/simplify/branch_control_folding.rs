//! branch-control 收敛：删除无求值行为的空/常量分支，把公共 direct-copy 尾部移出分支，
//! 将 repeat 尾部的单次 break guard 收回 until 条件，并把残留前向 goto 壳恢复成普通条件结构。
//!
//! 这里只消费已经存在的 `If/Goto/Label`，不重新解释 CFG，也不接管同一 lvalue 选值；
//! branch-value 形状仍由 `branch_value_folding` 先处理。每轮先为当前 block 建一次 label
//! 位置和引用计数，再按不交叉区间从右向左改写，避免多个 guard 共用 label 时反复全块
//! 扫描和重建。
//!
//! 例如 `if false then body end` 会被删除，`if true then body end` 会保留原 branch block
//! 的词法作用域后去掉条件壳；动态 lookup、调用、table 构造与元方法比较都不进入该规则。

mod path_conditions;

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirBlock, HirCallExpr, HirCallStmt, HirExpr, HirIf, HirLValue, HirLabelId, HirLogicalExpr,
    HirProto, HirStmt, HirUnaryOpKind, LocalId, TempId,
};
use crate::hir::expr_safety::{expr_is_discard_safe, expr_is_repeatable};

use super::carried_locals::{CarryBinding, single_binding_copy};
use super::expr_facts::expr_truthiness;
use super::label_refs::count_label_references;
use super::logical_simplify::{normalize_condition_context, simplify_condition_truthiness_shape};
use super::visit::{HirVisitor, visit_block, visit_expr, visit_stmts};
use super::walk::{HirRewritePass, rewrite_proto};

pub(super) fn fold_branch_control_in_proto(proto: &mut HirProto) -> bool {
    let mut changed = false;
    loop {
        let discard_facts = DiscardBoundaryFacts::new(proto);
        let path_changed =
            path_conditions::specialize_stable_path_conditions(proto, &discard_facts);
        changed |= path_changed
            | rewrite_proto(
                proto,
                &mut BranchControlPass {
                    discard_facts: &discard_facts,
                },
            );
        // 删除不可达写可能让下一项 local 立刻满足稳定性证明。这里收完本 pass 自己的
        // 单调链，避免合法的长链逐项消耗全局 scheduler 的固定轮次预算。
        if !path_changed {
            return changed;
        }
    }
}

struct BranchControlPass<'a> {
    discard_facts: &'a DiscardBoundaryFacts,
}

impl HirRewritePass for BranchControlPass<'_> {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        let constant_changed = fold_constant_control(&mut block.stmts, self.discard_facts);
        let common_tail_changed = sink_common_direct_copy_tails(&mut block.stmts);
        let empty_changed = remove_discard_safe_empty_ifs(&mut block.stmts);
        let terminal_changed = fold_forward_gotos(&mut block.stmts, FoldKind::TerminalElse);
        let guard_changed = fold_forward_gotos(&mut block.stmts, FoldKind::Guard);
        let nop_changed = remove_nop_goto_labels(&mut block.stmts);
        constant_changed
            || common_tail_changed
            || empty_changed
            || terminal_changed
            || guard_changed
            || nop_changed
    }

    fn rewrite_stmt(&mut self, stmt: &mut HirStmt) -> bool {
        fold_trailing_repeat_break_condition(stmt)
            || fold_effect_only_call(stmt)
            || fold_leading_while_break_guard(stmt)
            || naturalize_if_polarity(stmt)
    }
}

fn sink_common_direct_copy_tails(stmts: &mut Vec<HirStmt>) -> bool {
    let original = std::mem::take(stmts);
    let mut rewritten = Vec::with_capacity(original.len());
    let mut changed = false;

    for stmt in original {
        let HirStmt::If(mut if_stmt) = stmt else {
            rewritten.push(stmt);
            continue;
        };
        let Some(common_tail) = take_common_direct_copy_tail(&mut if_stmt) else {
            rewritten.push(HirStmt::If(if_stmt));
            continue;
        };
        rewritten.push(HirStmt::If(if_stmt));
        rewritten.push(common_tail);
        changed = true;
    }

    *stmts = rewritten;
    changed
}

fn take_common_direct_copy_tail(if_stmt: &mut HirIf) -> Option<HirStmt> {
    let else_block = if_stmt.else_block.as_ref()?;
    let then_tail = if_stmt.then_block.stmts.last()?;
    let else_tail = else_block.stmts.last()?;
    if then_tail != else_tail {
        return None;
    }
    let (target, source) = single_binding_copy(then_tail)?;
    if !arm_allows_direct_copy_sink(&if_stmt.then_block, target, source)
        || !arm_allows_direct_copy_sink(else_block, target, source)
    {
        return None;
    }

    let common_tail = if_stmt
        .then_block
        .stmts
        .pop()
        .expect("validated common-copy then arm must have a tail");
    let removed_else_tail = if_stmt
        .else_block
        .as_mut()
        .expect("validated common-copy candidate must have an else arm")
        .stmts
        .pop()
        .expect("validated common-copy else arm must have a tail");
    assert_eq!(
        removed_else_tail, common_tail,
        "validated common-copy arm tails must remain equal until apply"
    );
    Some(common_tail)
}

fn arm_allows_direct_copy_sink(
    block: &HirBlock,
    target: CarryBinding,
    source: CarryBinding,
) -> bool {
    if block
        .stmts
        .iter()
        .any(|stmt| matches!(stmt, HirStmt::ToBeClosed(_)))
    {
        // 候选拒绝[SemanticBarrier:Lifetime]：arm 顶层 TBC 在原 copy 之后、arm 退出时关闭；把 copy 移到分支外会改成先 close 后 copy（regress_175#3）。
        return false;
    }
    let mut visitor = DirectCopySinkBoundary {
        locals: [target.local(), source.local()],
        safe: true,
    };
    visit_block(block, &mut visitor);
    assert!(
        visitor.safe,
        "equal common-copy tails cannot redeclare their LocalId in either arm"
    );
    true
}

struct DirectCopySinkBoundary {
    locals: [Option<LocalId>; 2],
    safe: bool,
}

impl DirectCopySinkBoundary {
    fn introduces(&self, local: LocalId) -> bool {
        self.locals.contains(&Some(local))
    }
}

impl HirVisitor for DirectCopySinkBoundary {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        self.safe &= match stmt {
            HirStmt::LocalDecl(local_decl) => !local_decl
                .bindings
                .iter()
                .any(|local| self.introduces(*local)),
            HirStmt::NumericFor(numeric_for) => !self.introduces(numeric_for.binding),
            HirStmt::GenericFor(generic_for) => !generic_for
                .bindings
                .iter()
                .any(|local| self.introduces(*local)),
            _ => true,
        };
    }
}

fn fold_constant_control(stmts: &mut Vec<HirStmt>, discard_facts: &DiscardBoundaryFacts) -> bool {
    let original = std::mem::take(stmts);
    let mut rewritten = Vec::with_capacity(original.len());
    let mut changed = false;

    for stmt in original {
        if let HirStmt::While(current) = &stmt
            && current.body.stmts.is_empty()
            && expr_is_repeatable(&current.cond)
            && matches!(rewritten.last(),
                Some(HirStmt::While(previous))
                    if previous.body.stmts.is_empty() && previous.cond == current.cond)
        {
            changed = true;
            continue;
        }
        if matches!(&stmt, HirStmt::Block(block) if block.stmts.is_empty()) {
            changed = true;
            continue;
        }
        if let HirStmt::While(while_stmt) = &stmt
            && while_stmt.cond == HirExpr::Boolean(false)
        {
            let boundary = discard_facts.block_boundary(&while_stmt.body);
            if boundary.has_control_entry() {
                // 候选拒绝[SemanticBarrier:ControlFlow]：全局 label 引用数大于 body 内部引用数，如外部 `goto L` 指向 body 内 `::L::`；删除 body 会丢失确定的跳转目标。
                rewritten.push(stmt);
                continue;
            }
            if boundary.has_identity() {
                // 候选拒绝[PolicyBoundary]：未执行 body 内的 debug/PhysicalRoot/TBC 身份按源码证据策略保留（regress339 retain-debug）。
                rewritten.push(stmt);
                continue;
            }
            if boundary.has_diagnostic() {
                // 候选拒绝[LayerBoundary]：ErrNil/Unresolved 是前层显式诊断，branch-control 不得静默吞掉（regress339 Lua 5.5 ERRNNIL）。
                rewritten.push(stmt);
                continue;
            }
            changed = true;
            continue;
        }
        let HirStmt::If(mut if_stmt) = stmt else {
            rewritten.push(stmt);
            continue;
        };
        let selected_then = if expr_is_discard_safe(&if_stmt.cond)
            && !discard_safe_expr_has_unresolved(&if_stmt.cond)
        {
            expr_truthiness(&if_stmt.cond).or_else(|| {
                if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(|else_block| if_stmt.then_block == *else_block)
                    .then_some(true)
            })
        } else {
            None
        };
        let Some(selected_then) = selected_then else {
            // 候选拒绝[ProofIncomplete]：条件若不在 discard-safe 且 truthiness 已知的子集，
            // 当前规则没有“保留一次条件求值再选臂”的表示；Unresolved 另按诊断策略保留。
            rewritten.push(HirStmt::If(if_stmt));
            continue;
        };

        let discarded = if selected_then {
            if_stmt.else_block.as_ref()
        } else {
            Some(&if_stmt.then_block)
        };
        let discarded_boundary = discarded.map(|block| discard_facts.block_boundary(block));
        if discarded_boundary.is_some_and(DiscardBoundary::has_control_entry) {
            // 候选拒绝[SemanticBarrier:ControlFlow]：全局 label 引用数大于 arm 内部引用数，如外部 `goto L` 指向 arm 内 `::L::`；删除 arm 会丢失确定入边。
            rewritten.push(HirStmt::If(if_stmt));
            continue;
        }
        if discarded_boundary.is_some_and(DiscardBoundary::has_identity) {
            // 候选拒绝[PolicyBoundary]：未选 arm 的 debug/PhysicalRoot/TBC 身份仍属于项目要保留的源码证据（regress339 retain-debug）。
            rewritten.push(HirStmt::If(if_stmt));
            continue;
        }
        if discarded_boundary.is_some_and(DiscardBoundary::has_diagnostic) {
            // 候选拒绝[LayerBoundary]：ErrNil/Unresolved 由诊断 owner 生成，branch-control 不删除其承载 arm（regress339 Lua 5.5 ERRNNIL）。
            rewritten.push(HirStmt::If(if_stmt));
            continue;
        }

        let selected = if selected_then {
            if_stmt.then_block
        } else {
            if_stmt.else_block.take().unwrap_or_default()
        };
        if !selected.stmts.is_empty() {
            rewritten.push(HirStmt::Block(Box::new(selected)));
        }
        changed = true;
    }

    *stmts = rewritten;
    changed
}

/// branch-control 只在丢弃不可达代码时消费的 proto 身份与诊断边界。
///
/// `locals` 已经把可保留的源码 local 稳定成 `LocalId`；尚未物化的
/// debug temp 仍以 `temp_debug_locals` 标记。这里冻结两类身份，不重建 debug scope。
pub(super) struct DiscardBoundaryFacts {
    protected_locals: BTreeSet<LocalId>,
    protected_temps: BTreeSet<TempId>,
    label_refs: BTreeMap<HirLabelId, usize>,
}

impl DiscardBoundaryFacts {
    fn new(proto: &HirProto) -> Self {
        let mut protected_locals = proto.physical_root_locals.clone();
        protected_locals.extend(
            proto
                .locals
                .iter()
                .copied()
                .zip(&proto.local_debug_hints)
                .filter_map(|(local, hint)| hint.is_some().then_some(local)),
        );
        let protected_temps = proto
            .temps
            .iter()
            .copied()
            .zip(&proto.temp_debug_locals)
            .filter_map(|(temp, hint)| hint.is_some().then_some(temp))
            .collect();
        let label_refs = count_label_references(&proto.body.stmts);
        Self {
            protected_locals,
            protected_temps,
            label_refs,
        }
    }

    pub(super) fn block_boundary(&self, block: &HirBlock) -> DiscardBoundary {
        let mut visitor = DiscardBoundaryVisitor {
            facts: self,
            boundary: DiscardBoundary::default(),
            labels: BTreeSet::new(),
            internal_label_refs: BTreeMap::new(),
        };
        visit_block(block, &mut visitor);
        visitor.finish()
    }

    pub(super) fn stmts_boundary(&self, stmts: &[HirStmt]) -> DiscardBoundary {
        let mut visitor = DiscardBoundaryVisitor {
            facts: self,
            boundary: DiscardBoundary::default(),
            labels: BTreeSet::new(),
            internal_label_refs: BTreeMap::new(),
        };
        visit_stmts(stmts, &mut visitor);
        visitor.finish()
    }
}

#[derive(Clone, Copy, Default)]
pub(super) struct DiscardBoundary {
    identity: bool,
    diagnostic: bool,
    control_entry: bool,
}

impl DiscardBoundary {
    pub(super) fn has_identity(self) -> bool {
        self.identity
    }

    pub(super) fn has_diagnostic(self) -> bool {
        self.diagnostic
    }

    pub(super) fn has_control_entry(self) -> bool {
        self.control_entry
    }
}

struct DiscardBoundaryVisitor<'a> {
    facts: &'a DiscardBoundaryFacts,
    boundary: DiscardBoundary,
    labels: BTreeSet<HirLabelId>,
    internal_label_refs: BTreeMap<HirLabelId, usize>,
}

impl DiscardBoundaryVisitor<'_> {
    fn finish(mut self) -> DiscardBoundary {
        self.boundary.control_entry = self.labels.iter().any(|label| {
            let all_refs = self
                .facts
                .label_refs
                .get(label)
                .copied()
                .unwrap_or_default();
            let internal_refs = self
                .internal_label_refs
                .get(label)
                .copied()
                .unwrap_or_default();
            all_refs > internal_refs
        });
        self.boundary
    }
}

impl HirVisitor for DiscardBoundaryVisitor<'_> {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::LocalDecl(local_decl) => {
                self.boundary.identity |= local_decl
                    .bindings
                    .iter()
                    .any(|local| self.facts.protected_locals.contains(local));
            }
            HirStmt::ErrNil(_) => self.boundary.diagnostic = true,
            HirStmt::ToBeClosed(_) | HirStmt::Close(_) => self.boundary.identity = true,
            HirStmt::Goto(goto) => {
                *self.internal_label_refs.entry(goto.target).or_default() += 1;
            }
            HirStmt::Label(label) => {
                self.labels.insert(label.id);
            }
            _ => {}
        }
    }

    fn visit_expr(&mut self, expr: &HirExpr) {
        self.boundary.diagnostic |= matches!(expr, HirExpr::Unresolved(_));
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.boundary.identity |=
            matches!(lvalue, HirLValue::Temp(temp) if self.facts.protected_temps.contains(temp));
    }
}

fn fold_effect_only_call(stmt: &mut HirStmt) -> bool {
    let HirStmt::If(if_stmt) = stmt else {
        return false;
    };
    if !if_arms_are_empty(if_stmt) {
        return false;
    }

    let Some(call) = take_effect_only_call(&mut if_stmt.cond) else {
        return false;
    };
    *stmt = HirStmt::CallStmt(Box::new(HirCallStmt { call: *call }));
    true
}

fn remove_discard_safe_empty_ifs(stmts: &mut Vec<HirStmt>) -> bool {
    let original_len = stmts.len();
    stmts.retain(|stmt| {
        !matches!(
            stmt,
            HirStmt::If(if_stmt)
                if if_arms_are_empty(if_stmt)
                    && expr_is_discard_safe(&if_stmt.cond)
                    && !discard_safe_expr_has_unresolved(&if_stmt.cond)
        )
    });
    stmts.len() != original_len
}

/// `expr_is_discard_safe` 可递归接纳的表达式形状中是否仍携带显式诊断。
fn discard_safe_expr_has_unresolved(expr: &HirExpr) -> bool {
    match expr {
        HirExpr::Unresolved(_) => true,
        HirExpr::Unary(unary) => discard_safe_expr_has_unresolved(&unary.expr),
        HirExpr::Binary(binary) => {
            discard_safe_expr_has_unresolved(&binary.lhs)
                || discard_safe_expr_has_unresolved(&binary.rhs)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            discard_safe_expr_has_unresolved(&logical.lhs)
                || discard_safe_expr_has_unresolved(&logical.rhs)
        }
        _ => false,
    }
}

fn if_arms_are_empty(if_stmt: &HirIf) -> bool {
    if_stmt.then_block.stmts.is_empty()
        && if_stmt
            .else_block
            .as_ref()
            .is_none_or(|block| block.stmts.is_empty())
}

fn take_effect_only_call(mut expr: &mut HirExpr) -> Option<Box<HirCallExpr>> {
    loop {
        match expr {
            HirExpr::Call(_) => {
                let HirExpr::Call(call) = std::mem::replace(expr, HirExpr::Nil) else {
                    unreachable!("matched call must remain a call")
                };
                return Some(call);
            }
            HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
                expr = &mut unary.expr;
            }
            _ => return None,
        }
    }
}

fn fold_trailing_repeat_break_condition(stmt: &mut HirStmt) -> bool {
    let HirStmt::Repeat(repeat_stmt) = stmt else {
        return false;
    };
    let Some((tail, prefix)) = repeat_stmt.body.stmts.split_last() else {
        return false;
    };
    let HirStmt::If(outer) = tail else {
        return false;
    };
    if !matches!(outer.then_block.stmts.as_slice(), [HirStmt::Break]) {
        return false;
    }

    let (nested_else, outer_cond, moved_cond) = if let Some(else_block) = &outer.else_block {
        let [HirStmt::If(nested)] = else_block.stmts.as_slice() else {
            return false;
        };
        if nested.else_block.is_some()
            || !matches!(nested.then_block.stmts.as_slice(), [HirStmt::Break])
        {
            return false;
        }
        (true, Some(&outer.cond), &nested.cond)
    } else {
        (false, None, &outer.cond)
    };
    if matches!(moved_cond, HirExpr::LogicalOr(_))
        || matches!(repeat_stmt.cond, HirExpr::LogicalOr(_))
    {
        // 候选拒绝[PolicyBoundary]：条件语境下 `A or (B or C)` 的短路可精确保持；这里只选择每轮最多吸收一个尾部 break stage，避免把独立退出阶段过度压平。
        return false;
    }
    if !repeat_condition_fold_is_safe(
        prefix,
        outer_cond
            .into_iter()
            .chain([moved_cond, &repeat_stmt.cond]),
    ) {
        // 候选拒绝[SemanticBarrier:ControlFlow]：prefix 的当前 repeat continue 会从“跳过 moved 条件、只测原 latch”变成测试合成条件；跨尾部 goto/label 同样改变可达路径。
        // 候选拒绝[ProofIncomplete]：共享 visitor 未区分 nested loop/jump owner，且 Close/TBC 的 break-vs-normal-exit 关闭序尚无精确 owner 证明，安全子集也被一并拒绝；
        // 候选拒绝[LayerBoundary]：Decision/Unresolved 应先由上游消除或保留诊断。
        return false;
    }

    let lhs = if nested_else {
        let Some(HirStmt::If(outer)) = repeat_stmt.body.stmts.last_mut() else {
            unreachable!("validated repeat tail must remain an if");
        };
        let mut nested_stmts = outer
            .else_block
            .take()
            .expect("validated repeat tail must retain its else block")
            .stmts;
        let Some(HirStmt::If(nested)) = nested_stmts.pop() else {
            unreachable!("validated repeat else must contain one if");
        };
        nested.cond
    } else {
        let Some(HirStmt::If(guard)) = repeat_stmt.body.stmts.pop() else {
            unreachable!("validated repeat tail must remain an if");
        };
        guard.cond
    };
    let rhs = std::mem::replace(&mut repeat_stmt.cond, HirExpr::Boolean(false));
    let folded = HirExpr::LogicalOr(Box::new(HirLogicalExpr { lhs, rhs }));
    // branch-control synthesizes this condition after the general logical pass.  Re-run only
    // the condition-safe normalizer here so shared stable guards are absorbed without changing
    // Lua value semantics in ordinary expression positions.
    repeat_stmt.cond = simplify_condition_truthiness_shape(&folded).unwrap_or(folded);
    true
}

fn repeat_condition_fold_is_safe<'a>(
    prefix: &[HirStmt],
    exprs: impl IntoIterator<Item = &'a HirExpr>,
) -> bool {
    let mut boundary = RepeatConditionFoldBoundary { safe: true };
    visit_stmts(prefix, &mut boundary);
    for expr in exprs {
        visit_expr(expr, &mut boundary);
    }
    boundary.safe
}

struct RepeatConditionFoldBoundary {
    safe: bool,
}

impl HirVisitor for RepeatConditionFoldBoundary {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        self.safe &= !matches!(
            stmt,
            HirStmt::ToBeClosed(_)
                | HirStmt::Close(_)
                | HirStmt::Continue
                | HirStmt::Goto(_)
                | HirStmt::Label(_)
        );
    }

    fn visit_expr(&mut self, expr: &HirExpr) {
        self.safe &= !matches!(expr, HirExpr::Decision(_) | HirExpr::Unresolved(_));
    }
}

fn fold_leading_while_break_guard(stmt: &mut HirStmt) -> bool {
    let HirStmt::While(while_stmt) = stmt else {
        return false;
    };
    if while_stmt.cond != HirExpr::Boolean(true) {
        return false;
    }
    let Some(HirStmt::If(guard)) = while_stmt.body.stmts.first() else {
        return false;
    };
    if guard.else_block.is_some() || !matches!(guard.then_block.stmts.as_slice(), [HirStmt::Break])
    {
        return false;
    }
    while_stmt.cond = normalize_condition_context(&guard.cond, true).expr;
    while_stmt.body.stmts.remove(0);
    true
}

fn naturalize_if_polarity(stmt: &mut HirStmt) -> bool {
    let HirStmt::If(if_stmt) = stmt else {
        return false;
    };
    let Some(else_block) = if_stmt.else_block.as_ref() else {
        return false;
    };
    if if_stmt.then_block.stmts.is_empty() || else_block.stmts.is_empty() {
        return false;
    }

    let current = normalize_condition_context(&if_stmt.cond, false);
    let negated = normalize_condition_context(&if_stmt.cond, true);
    if negated.not_cost < current.not_cost {
        let Some(else_block) = if_stmt.else_block.as_mut() else {
            return false;
        };
        if_stmt.cond = negated.expr;
        std::mem::swap(&mut if_stmt.then_block, else_block);
        return true;
    }

    if current.changed {
        if_stmt.cond = current.expr;
        return true;
    }
    false
}

#[derive(Clone, Copy)]
enum FoldKind {
    TerminalElse,
    Guard,
}

struct FoldGroup {
    label: HirLabelId,
    label_index: usize,
    candidates: Vec<FoldCandidate>,
}

#[derive(Clone, Copy)]
struct FoldCandidate {
    if_index: usize,
    invert_cond: bool,
}

fn fold_forward_gotos(stmts: &mut Vec<HirStmt>, kind: FoldKind) -> bool {
    let label_indices = index_top_level_labels(stmts);
    let label_refs = count_label_references(stmts);
    let mut groups = BTreeMap::<usize, FoldGroup>::new();

    for (if_index, stmt) in stmts.iter().enumerate() {
        let Some((target, invert_cond)) = fold_target(stmt, kind) else {
            continue;
        };
        let Some(label_index) = label_indices.get(&target).copied() else {
            // 候选拒绝[LayerBoundary]：目标 label 不在当前顶层 block，不能由局部 forward-fold 重建。
            continue;
        };
        if label_index <= if_index + 1 {
            // 候选拒绝[LayerBoundary]：反向跳转属于循环恢复，紧邻跳转属于 nop-label 清理。
            continue;
        }
        let body = &stmts[(if_index + 1)..label_index];
        if !can_move_into_branch(body) {
            // 候选拒绝[SemanticBarrier:Scope/ControlFlow]：区间 local 若在 label 后仍被引用，移入 arm 会使 use 失去作用域；区间 goto/label 则可能改变跳转配对或跳入 local 的合法性。
            continue;
        }
        if matches!(kind, FoldKind::TerminalElse)
            && is_branch_value_assignment(stmt, body, invert_cond)
        {
            // 候选拒绝[LayerBoundary]：同 lvalue 的两臂赋值是 branch-values 的值选择候选，本 pass 不抢先改成控制流 else。
            continue;
        }
        groups
            .entry(label_index)
            .or_insert_with(|| FoldGroup {
                label: target,
                label_index,
                candidates: Vec::new(),
            })
            .candidates
            .push(FoldCandidate {
                if_index,
                invert_cond,
            });
    }

    if groups.is_empty() {
        return false;
    }

    // 可移动区间不含顶层 label，因此不同目标的区间不会交叉。倒序改写可保持更早
    // 区间的原始索引稳定；同一 label 的多个 guard 在一次改写中直接嵌套。
    for group in groups.into_values().rev() {
        let keep_label =
            label_refs.get(&group.label).copied().unwrap_or_default() > group.candidates.len();
        rewrite_fold_group(stmts, group, kind, keep_label);
    }
    true
}

fn rewrite_fold_group(
    stmts: &mut Vec<HirStmt>,
    group: FoldGroup,
    kind: FoldKind,
    keep_label: bool,
) {
    let first = group.candidates[0].if_index;
    let mut next = group.label_index;
    let mut nested = Vec::new();

    for candidate in group.candidates.into_iter().rev() {
        let if_index = candidate.if_index;
        let mut body = stmts[(if_index + 1)..next].to_vec();
        body.append(&mut nested);
        let HirStmt::If(if_stmt) = stmts[if_index].clone() else {
            unreachable!("branch-control fold index must point to an if")
        };
        nested = vec![HirStmt::If(Box::new(rewrite_if(
            *if_stmt,
            body,
            kind,
            candidate.invert_cond,
        )))];
        next = if_index;
    }

    if keep_label {
        nested.push(stmts[group.label_index].clone());
    }
    stmts.splice(first..=group.label_index, nested);
}

fn rewrite_if(mut if_stmt: HirIf, body: Vec<HirStmt>, kind: FoldKind, invert_cond: bool) -> HirIf {
    if invert_cond {
        if_stmt.cond = if_stmt.cond.negate();
        if_stmt.then_block = if_stmt
            .else_block
            .take()
            .expect("inverted fold must have an else block");
    }
    match kind {
        FoldKind::TerminalElse => {
            assert!(
                matches!(if_stmt.then_block.stmts.last(), Some(HirStmt::Goto(_))),
                "validated terminal-else fold must retain its terminal goto until apply"
            );
            if_stmt
                .then_block
                .stmts
                .pop()
                .expect("validated terminal-else fold must have a branch tail");
            if_stmt.else_block = Some(HirBlock { stmts: body });
        }
        FoldKind::Guard => {
            if_stmt.cond = if_stmt.cond.negate();
            if_stmt.then_block = HirBlock { stmts: body };
            if_stmt.else_block = None;
        }
    }
    if_stmt
}

fn fold_target(stmt: &HirStmt, kind: FoldKind) -> Option<(HirLabelId, bool)> {
    let HirStmt::If(if_stmt) = stmt else {
        return None;
    };
    let else_block = if_stmt.else_block.as_ref();
    let (branch, invert_cond) = match else_block {
        Some(else_block) if if_stmt.then_block.stmts.is_empty() => (else_block, true),
        Some(else_block) if else_block.stmts.is_empty() => (&if_stmt.then_block, false),
        None => (&if_stmt.then_block, false),
        Some(_) => return None,
    };
    match kind {
        FoldKind::TerminalElse => {
            if branch.stmts.len() < 2 {
                return None;
            }
            let HirStmt::Goto(goto) = branch.stmts.last()? else {
                return None;
            };
            Some((goto.target, invert_cond))
        }
        FoldKind::Guard => {
            let [HirStmt::Goto(goto)] = branch.stmts.as_slice() else {
                return None;
            };
            Some((goto.target, invert_cond))
        }
    }
}

fn can_move_into_branch(stmts: &[HirStmt]) -> bool {
    // `if cond then prefix; goto A end; goto B; ::A::` 是 island 常见的双向出口。
    // Guard/TerminalElse 都可把唯一的备用 goto 收进反向 arm；没有 binding 被搬动，
    // 最终 AST scope verifier 仍确认目标 label 对嵌套 arm 可见且没有跳进 local/TBC。
    if matches!(stmts, [HirStmt::Goto(_)]) {
        return true;
    }
    stmts.iter().all(|stmt| {
        !matches!(
            stmt,
            HirStmt::LocalDecl(_) | HirStmt::Goto(_) | HirStmt::Label(_)
        )
    })
}

fn is_branch_value_assignment(if_stmt: &HirStmt, else_body: &[HirStmt], invert_cond: bool) -> bool {
    let HirStmt::If(if_stmt) = if_stmt else {
        return false;
    };
    let branch = if invert_cond {
        let Some(else_block) = if_stmt.else_block.as_ref() else {
            return false;
        };
        else_block
    } else {
        &if_stmt.then_block
    };
    let [HirStmt::Assign(then_assign), HirStmt::Goto(_)] = branch.stmts.as_slice() else {
        return false;
    };
    let [HirStmt::Assign(else_assign)] = else_body else {
        return false;
    };
    then_assign.targets == else_assign.targets
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

fn remove_nop_goto_labels(stmts: &mut Vec<HirStmt>) -> bool {
    let label_refs = count_label_references(stmts);
    let mut old = std::mem::take(stmts).into_iter().peekable();
    let mut rewritten = Vec::with_capacity(old.len());
    let mut changed = false;

    while let Some(stmt) = old.next() {
        let HirStmt::Goto(goto) = &stmt else {
            rewritten.push(stmt);
            continue;
        };
        let Some(HirStmt::Label(label)) = old.peek() else {
            rewritten.push(stmt);
            continue;
        };
        if goto.target != label.id {
            rewritten.push(stmt);
            continue;
        }

        let label = old.next().expect("peeked label must remain available");
        if label_refs.get(&goto.target).copied().unwrap_or_default() > 1 {
            rewritten.push(label);
        }
        changed = true;
    }

    *stmts = rewritten;
    changed
}
