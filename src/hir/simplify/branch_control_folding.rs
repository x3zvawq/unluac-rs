//! 清理空/常量分支、公共复制尾部和前向 goto 壳，并恢复 repeat 尾部条件。
//!
//! 消费当前 HIR 的 If/Goto/Label、词法入口与目标方言安全事实，不重新解释 CFG；
//! 同一 binding 选值仍由 branch_value_folding 先处理。
//! 例如 if false then body end 可删除，if true then body end 则须保留 body
//! 的词法作用域；有事件的条件仍在原位置求值。

mod alternative_arms;

use std::collections::{BTreeMap, BTreeSet};

use crate::graph::PositionIndex;

use crate::hir::common::{
    HirBinaryOpKind, HirBlock, HirCallExpr, HirCallStmt, HirExpr, HirIf, HirLValue, HirLabelId,
    HirLocalDecl, HirLogicalExpr, HirProto, HirStmt, HirUnaryOpKind, HirValuePack, LocalId,
};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::ProtoPromotionFacts;

use super::carried_locals::{CarryBinding, single_binding_copy};
use super::expr_facts::expr_truthiness;
use super::label_refs::count_label_references;
use super::lexical_cfg::{LexicalCfgFailure, validate_region_entry};
use super::logical_simplify::{
    condition_needs_normalization, condition_not_costs, normalize_condition_context,
    simplify_condition_truthiness_shape_with_safety,
};
use super::mention::{stmts_mentioned_locals, stmts_protected_locals};
use super::walk::{HirRewritePass, rewrite_block};
use crate::hir::visit::{HirVisitor, visit_block, visit_expr, visit_stmt_structure, visit_stmts};

pub(super) fn fold_branch_control_in_proto(
    proto: &mut HirProto,
    promotion_facts: &mut ProtoPromotionFacts,
    safety: HirExprSafety,
) -> bool {
    let primitive_locals = ImmutablePrimitiveLocals::new(&proto.body);
    let discard_facts = DiscardBoundaryFacts {
        local_debug_hints: &proto.local_debug_hints,
        temp_debug_hints: &proto.temp_debug_locals,
        physical_root_locals: &proto.physical_root_locals,
        label_refs: count_label_references(&proto.body.stmts),
    };
    let forward_move_facts = ForwardBranchMoveFacts {
        local_debug_hints: &proto.local_debug_hints,
        local_debug_scopes: &proto.local_debug_scopes,
        physical_root_locals: &proto.physical_root_locals,
        resource_locals: stmts_protected_locals(&proto.body.stmts),
    };
    let first_new_local = proto.local_count;
    let mut pass = BranchControlPass {
        promotion_facts,
        discard_facts: &discard_facts,
        forward_move_facts: &forward_move_facts,
        primitive_locals: &primitive_locals,
        next_local_index: first_new_local,
        safety,
        read_alternatives: Default::default(),
    };
    let rewrite_changed = rewrite_block(&mut proto.body, &mut pass);
    let next_local_index = pass.next_local_index;
    for index in first_new_local..next_local_index {
        let local = LocalId(index);
        proto.local_debug_hints.push(None);
        proto.local_debug_scopes.push(None);
        promotion_facts.record_home_free_local(local);
    }
    proto.local_count = next_local_index;
    rewrite_changed
}

struct BranchControlPass<'a> {
    read_alternatives: alternative_arms::ReadAlternativeCache,
    promotion_facts: &'a ProtoPromotionFacts,
    discard_facts: &'a DiscardBoundaryFacts<'a>,
    forward_move_facts: &'a ForwardBranchMoveFacts<'a>,
    primitive_locals: &'a ImmutablePrimitiveLocals,
    next_local_index: usize,
    safety: HirExprSafety,
}

impl HirRewritePass for BranchControlPass<'_> {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        let constant_changed = fold_constant_control(
            &mut block.stmts,
            self.discard_facts,
            self.safety,
            &mut self.next_local_index,
            self.promotion_facts,
            &mut self.read_alternatives,
        );
        let common_tail_changed = sink_common_direct_copy_tails(&mut block.stmts);
        let leading_escape_changed = fold_leading_branch_escapes(&mut block.stmts);
        let adjacent_goto_changed = fold_adjacent_conditional_gotos(&mut block.stmts);
        let empty_changed =
            remove_discard_safe_empty_ifs(&mut block.stmts, self.safety, self.primitive_locals);
        let mut exit_changed = false;
        for index in 0..block.stmts.len().saturating_sub(1) {
            let HirStmt::Label(label) = &block.stmts[index + 1] else {
                continue;
            };
            // 紧随整个 if 的无 cleanup label 也是两臂的正常出口；只向现有
            // forward-fold 提供这个已知边界，不把真实 label 移进子作用域。
            // 候选拒绝[ProofIncomplete]：带资源交接的外层出口尚不能投影为 arm fallthrough。
            if !label.tbc_barriers.is_empty() || !label.entry_cleanup.is_empty() {
                continue;
            }
            let target = label.id;
            let HirStmt::If(branch) = &mut block.stmts[index] else {
                continue;
            };
            for arm in std::iter::once(&mut branch.then_block).chain(branch.else_block.iter_mut()) {
                for kind in [FoldKind::TerminalElse, FoldKind::Guard] {
                    exit_changed |= fold_forward_gotos(
                        &mut arm.stmts,
                        kind,
                        self.forward_move_facts,
                        &self.discard_facts.label_refs,
                        self.safety,
                        self.primitive_locals,
                        Some(target),
                    );
                }
            }
        }
        let terminal_changed = fold_forward_gotos(
            &mut block.stmts,
            FoldKind::TerminalElse,
            self.forward_move_facts,
            &self.discard_facts.label_refs,
            self.safety,
            self.primitive_locals,
            None,
        );
        let guard_changed = fold_forward_gotos(
            &mut block.stmts,
            FoldKind::Guard,
            self.forward_move_facts,
            &self.discard_facts.label_refs,
            self.safety,
            self.primitive_locals,
            None,
        );
        let nop_changed = remove_nop_goto_labels(&mut block.stmts);
        constant_changed
            || common_tail_changed
            || leading_escape_changed
            || adjacent_goto_changed
            || empty_changed
            || exit_changed
            || terminal_changed
            || guard_changed
            || nop_changed
    }

    fn rewrite_stmt(&mut self, stmt: &mut HirStmt) -> bool {
        fold_trailing_repeat_break_condition(stmt, self.safety)
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

impl HirVisitor<'_> for DirectCopySinkBoundary {
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

fn fold_constant_control(
    stmts: &mut Vec<HirStmt>,
    discard_facts: &DiscardBoundaryFacts,
    safety: HirExprSafety,
    next_local_index: &mut usize,
    promotion_facts: &ProtoPromotionFacts,
    read_alternatives: &mut alternative_arms::ReadAlternativeCache,
) -> bool {
    let original = std::mem::take(stmts);
    let mut rewritten = Vec::with_capacity(original.len());
    let mut changed = false;

    for stmt in original {
        if let HirStmt::While(current) = &stmt
            && current.body.stmts.is_empty()
            // 候选拒绝[SemanticBarrier:Metamethod]：LuaJIT cdata equality 可调用 ctype `__eq`；合并两个空 while 会少求值一次（regress_391）。
            && safety.is_repeatable(&current.cond)
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
                // 候选拒绝[PolicyBoundary]：项目保留未执行 body 中的 ErrNil/Unresolved
                // 失败证据，branch-control 不静默吞掉（regress339 Lua 5.5 ERRNNIL）。
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
        // 空 else 不拥有声明、事件或入口；统一其形状，使后续 repeat/guard 消费同一合同。
        if if_stmt
            .else_block
            .as_ref()
            .is_some_and(|block| block.stmts.is_empty())
        {
            if_stmt.else_block = None;
            changed = true;
        }
        let truthiness = expr_truthiness(&if_stmt.cond, safety);
        let exact_arms = if_stmt
            .else_block
            .as_ref()
            .is_some_and(|else_block| if_stmt.then_block == *else_block);
        let merged_arm = if truthiness.is_none() && !exact_arms {
            if_stmt.else_block.as_ref().and_then(|else_block| {
                alternative_arms::merge_read_alternatives(
                    &if_stmt.then_block,
                    else_block,
                    promotion_facts,
                    read_alternatives,
                )
            })
        } else {
            None
        };
        let arms_are_equal = exact_arms || merged_arm.is_some();
        let discard_condition = safety.is_discard_safe_without_residual(&if_stmt.cond);
        let selected_then = truthiness.or(arms_are_equal.then_some(true));
        let Some(selected_then) = selected_then else {
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
            // 候选拒绝[PolicyBoundary]：项目保留未选 arm 中的 ErrNil/Unresolved
            // 失败证据及其承载边界（regress339 Lua 5.5 ERRNNIL）。
            rewritten.push(HirStmt::If(if_stmt));
            continue;
        }

        if !discard_condition {
            // 条件结果只为控制转移服务。独立短作用域确保表达式完整求值一次，且其临时
            // GC root 在进入选定 arm 前释放，保持原 branch test 的求值次数、顺序和寿命。
            let local = LocalId(*next_local_index);
            *next_local_index += 1;
            let condition = std::mem::replace(&mut if_stmt.cond, HirExpr::Nil);
            rewritten.push(HirStmt::Block(Box::new(HirBlock {
                stmts: vec![HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![local],
                    values: HirValuePack::fixed(vec![condition]),
                    initializer_merge_transaction: None,
                }))],
            })));
        }

        let selected = if selected_then {
            merged_arm.unwrap_or(if_stmt.then_block)
        } else {
            if_stmt.else_block.take().unwrap_or_default()
        };
        if matches!(selected.stmts.as_slice(), [HirStmt::Return(_)]) {
            // 单条返回没有该 arm 独有的声明或资源范围；不制造阻断外层同臂合并的空作用域。
            rewritten.extend(selected.stmts);
        } else if !selected.stmts.is_empty() {
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
/// debug temp 仍以 `temp_debug_locals` 标记。身份映射直接借用；label 计数属于本轮 body 快照。
pub(super) struct DiscardBoundaryFacts<'a> {
    local_debug_hints: &'a [Option<String>],
    temp_debug_hints: &'a [Option<String>],
    physical_root_locals: &'a BTreeSet<LocalId>,
    label_refs: BTreeMap<HirLabelId, usize>,
}

impl DiscardBoundaryFacts<'_> {
    pub(super) fn block_boundary(&self, block: &HirBlock) -> DiscardBoundary {
        self.stmts_boundary(&block.stmts)
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
    facts: &'a DiscardBoundaryFacts<'a>,
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

impl HirVisitor<'_> for DiscardBoundaryVisitor<'_> {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::LocalDecl(local_decl) => {
                self.boundary.identity |= local_decl.bindings.iter().any(|local| {
                    self.facts.physical_root_locals.contains(local)
                        || matches!(
                            self.facts.local_debug_hints.get(local.index()),
                            Some(Some(_))
                        )
                });
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
        self.boundary.identity |= matches!(lvalue, HirLValue::Temp(temp) if matches!(self.facts.temp_debug_hints.get(temp.index()), Some(Some(_))));
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

#[derive(Default)]
struct ImmutablePrimitiveLocals {
    candidates: BTreeSet<LocalId>,
    written: BTreeSet<LocalId>,
}

impl ImmutablePrimitiveLocals {
    fn new(body: &HirBlock) -> Self {
        let mut index = Self::default();
        visit_block(body, &mut index);
        let captured = super::mention::stmts_reference_captured_bindings(&body.stmts);
        index.written.extend(captured.locals);
        index
            .candidates
            .retain(|local| !index.written.contains(local));
        index
    }

    fn contains(&self, local: LocalId) -> bool {
        self.candidates.contains(&local)
    }
}

impl HirVisitor<'_> for ImmutablePrimitiveLocals {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        let HirStmt::LocalDecl(decl) = stmt else {
            return;
        };
        if let ([local], [value], None) = (
            decl.bindings.as_slice(),
            decl.values.fixed.as_slice(),
            &decl.values.tail,
        ) && is_primitive_literal(value)
        {
            self.candidates.insert(*local);
        }
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        if let HirLValue::Local(local) = lvalue {
            self.written.insert(*local);
        }
    }
}

fn is_primitive_literal(expr: &HirExpr) -> bool {
    matches!(
        expr,
        HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
    )
}

fn primitive_value_is_known(expr: &HirExpr, locals: &ImmutablePrimitiveLocals) -> bool {
    is_primitive_literal(expr)
        || matches!(expr, HirExpr::LocalRef(local) if locals.contains(*local))
}

fn is_discard_safe_with_primitive_locals(
    expr: &HirExpr,
    safety: HirExprSafety,
    primitive_locals: &ImmutablePrimitiveLocals,
) -> bool {
    if safety.is_discard_safe_without_residual(expr) {
        return true;
    }
    match expr {
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
            is_discard_safe_with_primitive_locals(&unary.expr, safety, primitive_locals)
        }
        HirExpr::Binary(binary) if binary.op == HirBinaryOpKind::Eq => {
            primitive_value_is_known(&binary.lhs, primitive_locals)
                && primitive_value_is_known(&binary.rhs, primitive_locals)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            is_discard_safe_with_primitive_locals(&logical.lhs, safety, primitive_locals)
                && is_discard_safe_with_primitive_locals(&logical.rhs, safety, primitive_locals)
        }
        _ => false,
    }
}

fn remove_discard_safe_empty_ifs(
    stmts: &mut Vec<HirStmt>,
    safety: HirExprSafety,
    primitive_locals: &ImmutablePrimitiveLocals,
) -> bool {
    let original_len = stmts.len();
    stmts.retain(|stmt| {
        !matches!(
            stmt,
            HirStmt::If(if_stmt)
                if if_arms_are_empty(if_stmt)
                    // 候选拒绝[SemanticBarrier:Metamethod]：LuaJIT cdata equality 可调用 ctype `__eq`；删除空 if 会漏掉这次调用（regress_391）。
                    // 候选接受：若 equality 两侧都由 immutable primitive local/literal 证明为原始值，LuaJIT 也不会进入 ctype `__eq`。
                    && is_discard_safe_with_primitive_locals(
                        &if_stmt.cond,
                        safety,
                        primitive_locals,
                    )
        )
    });
    stmts.len() != original_len
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

fn fold_trailing_repeat_break_condition(stmt: &mut HirStmt, safety: HirExprSafety) -> bool {
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

    let (nested_else, moved_cond) = if let Some(else_block) = &outer.else_block {
        let [HirStmt::If(nested)] = else_block.stmts.as_slice() else {
            return false;
        };
        if nested.else_block.is_some()
            || !matches!(nested.then_block.stmts.as_slice(), [HirStmt::Break])
        {
            return false;
        }
        (true, &nested.cond)
    } else {
        (false, &outer.cond)
    };
    if !repeat_condition_fold_is_safe(prefix, [moved_cond, &repeat_stmt.cond]) {
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
    repeat_stmt.cond =
        simplify_condition_truthiness_shape_with_safety(&folded, safety).unwrap_or(folded);
    true
}

fn repeat_condition_fold_is_safe<'a>(
    prefix: &[HirStmt],
    exprs: impl IntoIterator<Item = &'a HirExpr>,
) -> bool {
    let ownership = repeat_prefix_ownership(prefix, 0, 0);
    if ownership.current_loop_continue {
        // 候选拒绝[SemanticBarrier:ControlFlow]：当前 repeat owner 的 continue 会从“跳过 moved 条件、只测原 latch”变成测试合成条件（regress_294）；嵌套 loop owner 原位消费自己的 continue。
        return false;
    }
    if ownership.current_repeat_region_resource {
        // 候选拒绝[SemanticBarrier:Resource]：当前 repeat owner 的 TBC 在 Lua 5.5 会由 close-scopes 围住尾部 break；折进 latch 会把条件从 close 前移到 close 后（regress_369）。嵌套 loop 的资源已在进入外层 tail 前关闭。
        return false;
    }
    // label/goto 与整个 prefix 都保持原位：跳出 prefix 的边同时绕过旧 tail 和新 latch；
    // 任意落入 prefix 后正常落空的边则在两种表示中都依次到达 moved condition 与旧 latch。
    // `continue` 是唯一会绕过旧 tail 却直达新 latch 的当前 owner，已由上面的专用事实拒绝。
    let mut boundary = RepeatConditionFoldMovedExprBoundary::default();
    for expr in exprs {
        visit_expr(expr, &mut boundary);
    }
    if boundary.decision {
        // 候选拒绝[LayerBoundary]：被重挂到 latch 的 Decision 由 eliminate-decisions
        // 原位物化；其 invalidation 会让 branch-control 在 owner 收敛后重跑（regress_370）。
        return false;
    }
    if boundary.unresolved {
        // 候选拒绝[PolicyBoundary]：Unresolved 没有可声明等价的 Lua 求值语义；项目选择
        // 原位保留 permissive 诊断，而不是把失败节点重挂进普通 latch 表达式。
        return false;
    }
    true
}

#[derive(Default)]
struct RepeatPrefixOwnership {
    current_loop_continue: bool,
    current_repeat_region_resource: bool,
}

fn repeat_prefix_ownership(
    stmts: &[HirStmt],
    loop_depth: usize,
    resource_scope_depth: usize,
) -> RepeatPrefixOwnership {
    let mut ownership = RepeatPrefixOwnership::default();
    for stmt in stmts {
        collect_repeat_prefix_ownership(stmt, loop_depth, resource_scope_depth, &mut ownership);
    }
    ownership
}

fn collect_repeat_prefix_ownership(
    stmt: &HirStmt,
    loop_depth: usize,
    resource_scope_depth: usize,
    ownership: &mut RepeatPrefixOwnership,
) {
    match stmt {
        HirStmt::LocalRootRelease(_) => {}
        HirStmt::If(if_stmt) => {
            collect_repeat_prefix_ownership_stmts(
                &if_stmt.then_block.stmts,
                loop_depth,
                resource_scope_depth + 1,
                ownership,
            );
            if let Some(else_block) = &if_stmt.else_block {
                collect_repeat_prefix_ownership_stmts(
                    &else_block.stmts,
                    loop_depth,
                    resource_scope_depth + 1,
                    ownership,
                );
            }
        }
        HirStmt::While(while_stmt) => {
            collect_repeat_prefix_ownership_stmts(
                &while_stmt.body.stmts,
                loop_depth + 1,
                resource_scope_depth + 1,
                ownership,
            );
        }
        HirStmt::Repeat(repeat_stmt) => {
            collect_repeat_prefix_ownership_stmts(
                &repeat_stmt.body.stmts,
                loop_depth + 1,
                resource_scope_depth + 1,
                ownership,
            );
        }
        HirStmt::NumericFor(numeric_for) => {
            collect_repeat_prefix_ownership_stmts(
                &numeric_for.body.stmts,
                loop_depth + 1,
                resource_scope_depth + 1,
                ownership,
            );
        }
        HirStmt::GenericFor(generic_for) => {
            collect_repeat_prefix_ownership_stmts(
                &generic_for.body.stmts,
                loop_depth + 1,
                resource_scope_depth + 1,
                ownership,
            );
        }
        HirStmt::Block(block) => {
            collect_repeat_prefix_ownership_stmts(
                &block.stmts,
                loop_depth,
                resource_scope_depth + 1,
                ownership,
            );
        }
        HirStmt::Continue => ownership.current_loop_continue |= loop_depth == 0,
        HirStmt::ToBeClosed(_) | HirStmt::Close(_) => {
            ownership.current_repeat_region_resource |= resource_scope_depth == 0;
        }
        HirStmt::LocalDecl(_)
        | HirStmt::GlobalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::Break
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => {}
    }
}

fn collect_repeat_prefix_ownership_stmts(
    stmts: &[HirStmt],
    loop_depth: usize,
    resource_scope_depth: usize,
    ownership: &mut RepeatPrefixOwnership,
) {
    for stmt in stmts {
        collect_repeat_prefix_ownership(stmt, loop_depth, resource_scope_depth, ownership);
    }
}

#[derive(Default)]
struct RepeatConditionFoldMovedExprBoundary {
    decision: bool,
    unresolved: bool,
}

impl HirVisitor<'_> for RepeatConditionFoldMovedExprBoundary {
    fn visit_expr(&mut self, expr: &HirExpr) {
        self.decision |= matches!(expr, HirExpr::Decision(_));
        self.unresolved |= matches!(expr, HirExpr::Unresolved(_));
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
    let HirStmt::If(guard) = while_stmt.body.stmts.remove(0) else {
        unreachable!("validated loop guard remains the first statement");
    };
    while_stmt.cond = normalize_condition_context(guard.cond, true);
    true
}

fn naturalize_if_polarity(stmt: &mut HirStmt) -> bool {
    let HirStmt::If(if_stmt) = stmt else {
        return false;
    };
    let Some(else_block) = if_stmt.else_block.as_mut() else {
        return false;
    };
    if if_stmt.then_block.stmts.is_empty() || else_block.stmts.is_empty() {
        return false;
    }

    let [positive, negative] = condition_not_costs(&if_stmt.cond);
    if negative < positive {
        if_stmt.cond =
            normalize_condition_context(std::mem::replace(&mut if_stmt.cond, HirExpr::Nil), true);
        std::mem::swap(&mut if_stmt.then_block, else_block);
        return true;
    }

    if condition_needs_normalization(&if_stmt.cond) {
        if_stmt.cond =
            normalize_condition_context(std::mem::replace(&mut if_stmt.cond, HirExpr::Nil), false);
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
    block_exit: bool,
}

#[derive(Clone, Copy)]
struct FoldCandidate {
    if_index: usize,
    invert_cond: bool,
}

struct ForwardBranchMoveFacts<'a> {
    local_debug_hints: &'a [Option<String>],
    local_debug_scopes: &'a [Option<usize>],
    physical_root_locals: &'a BTreeSet<LocalId>,
    resource_locals: BTreeSet<LocalId>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum BranchMoveFailure {
    AmbiguousControl,
    ExternalControlEntry,
    DebugScope,
    PhysicalRoot,
    ResourceScope,
    LiveAfterJoin,
    CollectableRoot,
    UnsupportedRootFlow,
}

#[derive(Eq, Ord, PartialEq, PartialOrd)]
enum MoveBoundary {
    Label,
    Close,
}

struct BranchMoveRegion<'a> {
    stmts: &'a [HirStmt],
    suffix: &'a [HirStmt],
    has_label: bool,
    has_cleanup: bool,
}

fn fold_forward_gotos(
    stmts: &mut Vec<HirStmt>,
    kind: FoldKind,
    move_facts: &ForwardBranchMoveFacts,
    owner_label_refs: &BTreeMap<HirLabelId, usize>,
    safety: HirExprSafety,
    primitive_locals: &ImmutablePrimitiveLocals,
    continuation: Option<HirLabelId>,
) -> bool {
    let mut label_indices = index_top_level_labels(stmts);
    if let Some(target) = continuation {
        label_indices.entry(target).or_insert(stmts.len());
    }
    let mut boundaries = PositionIndex::default();
    let mut indexed_end = 0;
    let mut groups = BTreeMap::<usize, FoldGroup>::new();

    for (if_index, stmt) in stmts.iter().enumerate() {
        let Some((target, invert_cond)) = fold_target(stmt, kind) else {
            continue;
        };
        let Some(label_index) = label_indices.get(&target).copied() else {
            // 候选拒绝[SemanticBarrier:ControlFlow]：目标 label 不在当前词法 block
            // 时，goto 可能跳出外层或进入另一个局部区域；将当前后缀搬入 arm
            // 会把本来不在该边上的语句变成条件执行，并改变跳转的词法作用域。
            continue;
        };
        if label_index <= if_index {
            // 候选拒绝[SemanticBarrier:ControlFlow]：反向边会重入 if 之前的区域；
            // forward-fold 只会构造单次前向执行的 arm，会删除后续迭代的回边语义。
            continue;
        }
        if label_index == if_index + 1 {
            // 这条无操作边已由 fold_adjacent_conditional_gotos 原位删除；若同一 label
            // 仍有其它入口，它会继续保留为真实目标，否则 deferred dead-labels 清扫它。
            continue;
        }
        let range = (if_index + 1)..label_index;
        // 候选起点递增，终点可回退；只补充此前查询并集之外的子树，跳过永不再查的空隙。
        for (index, stmt) in stmts
            .iter()
            .enumerate()
            .take(range.end)
            .skip(indexed_end.max(range.start))
        {
            visit_stmt_structure(stmt, &mut |stmt| match stmt {
                HirStmt::Label(_) => boundaries.record(MoveBoundary::Label, index),
                HirStmt::Close(_) => boundaries.record(MoveBoundary::Close, index),
                _ => {}
            });
        }
        indexed_end = indexed_end.max(range.end);
        let region = BranchMoveRegion {
            stmts: &stmts[range.clone()],
            suffix: &stmts[(label_index + 1).min(stmts.len())..],
            has_label: boundaries
                .last_in(&MoveBoundary::Label, range.clone())
                .is_some(),
            has_cleanup: boundaries.last_in(&MoveBoundary::Close, range).is_some(),
        };
        let Err(failure) = can_move_into_branch(
            region,
            move_facts,
            owner_label_refs,
            safety,
            primitive_locals,
        ) else {
            groups
                .entry(label_index)
                .or_insert_with(|| FoldGroup {
                    label: target,
                    label_index,
                    candidates: Vec::new(),
                    block_exit: label_index == stmts.len(),
                })
                .candidates
                .push(FoldCandidate {
                    if_index,
                    invert_cond,
                });
            continue;
        };
        match failure {
            BranchMoveFailure::AmbiguousControl => {
                // 重复 label 没有唯一 CFG owner，不属于 forward-fold 的支持输入。
            }
            BranchMoveFailure::ExternalControlEntry => {
                // 候选拒绝[SemanticBarrier:ControlFlow]：区间 label 有外部入口；将 label
                // 嵌入 arm 会让原入口丢失目标或改为跳入条件作用域。
            }
            BranchMoveFailure::DebugScope => {
                // 候选拒绝[SemanticBarrier:DebugScope]：移动带 debug identity/scope 的
                // declaration 会改变 line hook/debug.getlocal 可观察的声明起点和终点。
            }
            BranchMoveFailure::PhysicalRoot | BranchMoveFailure::CollectableRoot => {
                // 候选拒绝[SemanticBarrier:Lifetime]：原 local 在 join 后仍保持对象根；移入
                // arm 会提前结束根生命周期，weak table/finalizer 可观察对象更早回收。
            }
            BranchMoveFailure::ResourceScope => {
                // 候选拒绝[SemanticBarrier:ResourceLifetime]：for binder/<close> identity 的
                // scope end 是刷新或关闭事件；移入 arm 会把事件提前到 join 之前。
            }
            BranchMoveFailure::LiveAfterJoin => {
                // 候选拒绝[SemanticBarrier:Scope]：join 后仍引用区间 local；移入 arm 会让
                // 该 use 脱离 declaration 的词法作用域。
            }
            BranchMoveFailure::UnsupportedRootFlow => {
                // 含可能承载对象的后写需要 reaching-root 证明，不属于本 fold 的局部
                // value-pack grammar；这里不把缺失证明伪装成对象必然存活到 join。
            }
        }
    }

    if groups.is_empty() {
        return false;
    }

    // 区间内的 self-contained label/goto 可以随整个区域移动；因此不同目标的候选可能
    // 嵌套或交叉。本轮只取从右向左互不重叠的组，未选候选由 scheduler 下一轮消费。
    let mut selected = Vec::new();
    let mut next_start = stmts.len() + 1;
    for group in groups.into_values().rev() {
        let start = group.candidates[0].if_index;
        if group.label_index >= next_start {
            continue;
        }
        next_start = start;
        selected.push(group);
    }
    let mut original = std::mem::take(stmts).into_iter();
    let mut rewritten = Vec::with_capacity(original.len());
    let mut position = 0;
    // 选择顺序仍从右到左；提交按原坐标顺序消费互不重叠的区域，不重复移动已处理后缀。
    for group in selected.into_iter().rev() {
        let first = group.candidates[0].if_index;
        rewritten.extend(original.by_ref().take(first - position));
        let region = original
            .by_ref()
            .take(group.label_index - first + 1)
            .collect();
        position = group.label_index + 1;
        let keep_label = !group.block_exit
            && owner_label_refs
                .get(&group.label)
                .copied()
                .unwrap_or_default()
                > group.candidates.len();
        rewritten.extend(rewrite_fold_group(region, group, kind, keep_label));
    }
    rewritten.extend(original);
    *stmts = rewritten;
    true
}

// 前导 guard 跳到整个 if 的紧随出口时，只将 guard 并入条件，body 的词法层不移动。
// 条件沿原路径各求值一次；多层 guard 用短路 AND 表达，不复制后继 body。
fn fold_leading_branch_escapes(stmts: &mut [HirStmt]) -> bool {
    let mut changed = false;
    for index in 0..stmts.len().saturating_sub(1) {
        let HirStmt::Label(label) = &stmts[index + 1] else {
            continue;
        };
        // 候选拒绝[ProofIncomplete]：这里只证明无资源交接的前导退出；尚未核对
        // 带 close/cleanup 的跳转边改为条件 fallthrough 后的清理归属。
        if !label.tbc_barriers.is_empty() || !label.entry_cleanup.is_empty() {
            continue;
        }
        let target = label.id;
        let HirStmt::If(branch) = &mut stmts[index] else {
            continue;
        };
        if branch
            .else_block
            .as_ref()
            .is_some_and(|block| !block.stmts.is_empty())
        {
            continue;
        }
        let mut guards = Vec::new();
        for stmt in &branch.then_block.stmts {
            let Some(escape) = leading_escape_condition(stmt, target) else {
                break;
            };
            guards.push(normalize_condition_context(escape, true));
        }
        if guards.is_empty() {
            continue;
        }
        let count = guards.len();
        for guard in guards {
            branch.cond = HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
                lhs: std::mem::replace(&mut branch.cond, HirExpr::Boolean(false)),
                rhs: guard,
            }));
        }
        // 一次收完连续 guard，避免逐轮 remove(0) 搬移整个后缀并耗尽调度预算。
        drop(branch.then_block.stmts.drain(..count));
        changed = true;
    }
    changed
}

fn leading_escape_condition(mut stmt: &HirStmt, target: HirLabelId) -> Option<HirExpr> {
    let mut conditions = Vec::new();
    while let HirStmt::If(guard) = stmt {
        if guard
            .else_block
            .as_ref()
            .is_some_and(|block| !block.stmts.is_empty())
        {
            return None;
        }
        let [child] = guard.then_block.stmts.as_slice() else {
            return None;
        };
        conditions.push(&guard.cond);
        stmt = child;
    }
    if !matches!(stmt, HirStmt::Goto(jump) if jump.target == target) {
        return None;
    }
    let mut condition = conditions.pop()?.clone();
    for outer in conditions.into_iter().rev() {
        condition = HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
            lhs: outer.clone(),
            rhs: condition,
        }));
    }
    Some(condition)
}

fn fold_adjacent_conditional_gotos(stmts: &mut [HirStmt]) -> bool {
    let mut changed = false;
    for index in 0..stmts.len().saturating_sub(1) {
        let Some(HirStmt::Label(label)) = stmts.get(index + 1) else {
            continue;
        };
        let target = label.id;
        let Some(HirStmt::If(if_stmt)) = stmts.get_mut(index) else {
            continue;
        };

        let then_is_target = matches!(if_stmt.then_block.stmts.as_slice(), [HirStmt::Goto(goto)] if goto.target == target);
        let else_is_target = if_stmt.else_block.as_ref().is_some_and(|else_block| {
            matches!(else_block.stmts.as_slice(), [HirStmt::Goto(goto)] if goto.target == target)
        });
        let else_is_empty = if_stmt
            .else_block
            .as_ref()
            .is_none_or(|else_block| else_block.stmts.is_empty());

        if then_is_target && else_is_empty {
            // `goto` 与普通 fallthrough 都紧接着进入同一 label；只删除无操作边，保留
            // condition 的一次求值。后续 empty-if/effect-only 规则决定它能否继续收敛。
            if_stmt.then_block.stmts.clear();
            changed = true;
        } else if else_is_target && if_stmt.then_block.stmts.is_empty() {
            if_stmt
                .else_block
                .as_mut()
                .expect("matched else target must remain present")
                .stmts
                .clear();
            changed = true;
        }
    }
    changed
}

fn rewrite_fold_group(
    mut stmts: Vec<HirStmt>,
    group: FoldGroup,
    kind: FoldKind,
    keep_label: bool,
) -> Vec<HirStmt> {
    let first = group.candidates[0].if_index;
    let label = (!group.block_exit).then(|| stmts.pop().expect("fold region ends at its label"));
    let mut nested = Vec::new();

    for candidate in group.candidates.into_iter().rev() {
        let mut body = stmts.split_off(candidate.if_index - first + 1);
        body.append(&mut nested);
        let Some(HirStmt::If(if_stmt)) = stmts.pop() else {
            unreachable!("branch-control fold index must point to an if")
        };
        nested = vec![HirStmt::If(Box::new(rewrite_if(
            *if_stmt,
            body,
            kind,
            candidate.invert_cond,
        )))];
    }

    if keep_label {
        nested.push(label.expect("retained label belongs to this block"));
    }
    nested
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

fn can_move_into_branch(
    region: BranchMoveRegion<'_>,
    facts: &ForwardBranchMoveFacts,
    owner_label_refs: &BTreeMap<HirLabelId, usize>,
    safety: HirExprSafety,
    primitive_locals: &ImmutablePrimitiveLocals,
) -> Result<(), BranchMoveFailure> {
    let BranchMoveRegion {
        stmts,
        suffix,
        has_label,
        has_cleanup,
    } = region;
    // 没有内部 label 就没有待验证的控制入口；含 label 时仍核对重复定义及完整引用计数。
    if has_label {
        match validate_region_entry(stmts, owner_label_refs) {
            Ok(_) => {}
            Err(LexicalCfgFailure::AmbiguousLabel) => {
                return Err(BranchMoveFailure::AmbiguousControl);
            }
            Err(LexicalCfgFailure::ExternalEntry) => {
                return Err(BranchMoveFailure::ExternalControlEntry);
            }
        }
    }

    // raw cleanup 的边界仍位于指令之间；先由资源 pass 物化 owner，再移动整个词法块。
    if has_cleanup {
        return Err(BranchMoveFailure::ResourceScope);
    }

    let mut suffix_mentions = None;
    let mut root_writes = None;
    for (decl_index, stmt) in stmts.iter().enumerate() {
        let HirStmt::LocalDecl(decl) = stmt else {
            continue;
        };
        for (binding_index, &local) in decl.bindings.iter().enumerate() {
            if matches!(facts.local_debug_hints.get(local.index()), Some(Some(_)))
                || matches!(facts.local_debug_scopes.get(local.index()), Some(Some(_)))
            {
                return Err(BranchMoveFailure::DebugScope);
            }
            if facts.physical_root_locals.contains(&local) {
                return Err(BranchMoveFailure::PhysicalRoot);
            }
            if facts.resource_locals.contains(&local) {
                return Err(BranchMoveFailure::ResourceScope);
            }
            if suffix_mentions
                .get_or_insert_with(|| stmts_mentioned_locals(suffix))
                .contains(&local)
            {
                return Err(BranchMoveFailure::LiveAfterJoin);
            }
            let initial_is_gc_inert =
                pack_slot_is_gc_inert(&decl.values, binding_index, safety, primitive_locals);
            let writes = root_writes
                .get_or_insert_with(|| local_root_write_positions(stmts, safety, primitive_locals))
                .get(&local);
            let written_later = writes.is_some_and(|writes| writes.last_write > decl_index);
            let collectable_later = writes.is_some_and(|writes| {
                writes
                    .last_collectable
                    .is_some_and(|index| index > decl_index)
            });
            if !initial_is_gc_inert && !written_later {
                return Err(BranchMoveFailure::CollectableRoot);
            }
            if (!initial_is_gc_inert && written_later) || collectable_later {
                return Err(BranchMoveFailure::UnsupportedRootFlow);
            }
        }
    }
    Ok(())
}

fn pack_slot_is_gc_inert(
    pack: &HirValuePack,
    index: usize,
    safety: HirExprSafety,
    primitive_locals: &ImmutablePrimitiveLocals,
) -> bool {
    pack.fixed.get(index).map_or_else(
        || pack.tail.is_none(),
        |expr| {
            safety.result_is_gc_inert(expr)
                || matches!(expr, HirExpr::LocalRef(local) if primitive_locals.contains(*local))
        },
    )
}

fn local_root_write_positions(
    stmts: &[HirStmt],
    safety: HirExprSafety,
    primitive_locals: &ImmutablePrimitiveLocals,
) -> BTreeMap<LocalId, LocalRootWritePositions> {
    let mut writes = BTreeMap::<LocalId, LocalRootWritePositions>::new();
    for (stmt_index, stmt) in stmts.iter().enumerate() {
        let mut record = |local, gc_inert: bool| {
            let positions = writes.entry(local).or_default();
            positions.last_write = stmt_index;
            if !gc_inert {
                positions.last_collectable = Some(stmt_index);
            }
        };
        visit_stmt_structure(stmt, &mut |stmt| match stmt {
            HirStmt::Assign(assign) => {
                for (index, target) in assign.targets.iter().enumerate() {
                    if let HirLValue::Local(local) = target {
                        record(
                            *local,
                            pack_slot_is_gc_inert(&assign.values, index, safety, primitive_locals),
                        );
                    }
                }
            }
            HirStmt::LocalDecl(decl) => {
                for local in &decl.bindings {
                    record(*local, false);
                }
            }
            HirStmt::NumericFor(for_stmt) => record(for_stmt.binding, false),
            HirStmt::GenericFor(for_stmt) => {
                for local in &for_stmt.bindings {
                    record(*local, false);
                }
            }
            _ => {}
        });
    }
    writes
}

/// 直接语句位置也代表其整个嵌套子树；查询严格排除声明所在语句。
#[derive(Default)]
struct LocalRootWritePositions {
    last_write: usize,
    last_collectable: Option<usize>,
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
