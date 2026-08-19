//! 统计 HIR block 中 carried binding 的读写与提及；依赖 HirVisitor，不负责修改语句；例如判断候选 binding 是否在尾部仍被读取。

use super::*;

#[derive(Default)]
pub(super) struct BindingFacts {
    pub(super) reads: BTreeMap<CarryBinding, usize>,
    pub(super) writes: BTreeMap<CarryBinding, usize>,
}

impl HirVisitor for BindingFacts {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let Some(binding) = carry_binding_from_expr(expr) {
            *self.reads.entry(binding).or_default() += 1;
        }
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        if let Some(binding) = carry_binding_from_lvalue(lvalue) {
            *self.writes.entry(binding).or_default() += 1;
        }
    }
}

pub(super) fn binding_facts(stmts: &[HirStmt]) -> BindingFacts {
    let mut facts = BindingFacts::default();
    visit_stmts(stmts, &mut facts);
    facts
}

pub(super) fn binding_is_read_in_stmts(stmts: &[HirStmt], binding: CarryBinding) -> bool {
    binding_facts(stmts)
        .reads
        .get(&binding)
        .copied()
        .unwrap_or(0)
        != 0
}

pub(super) fn binding_is_written_in_stmts(stmts: &[HirStmt], binding: CarryBinding) -> bool {
    binding_facts(stmts)
        .writes
        .get(&binding)
        .copied()
        .unwrap_or(0)
        != 0
}

pub(super) fn binding_is_mentioned_in_stmts(stmts: &[HirStmt], binding: CarryBinding) -> bool {
    let facts = binding_facts(stmts);
    facts.reads.contains_key(&binding) || facts.writes.contains_key(&binding)
}

pub(super) fn bindings_are_mentioned_in_stmts(
    stmts: &[HirStmt],
    bindings: &[CarryBinding],
) -> bool {
    let facts = binding_facts(stmts);
    bindings
        .iter()
        .any(|binding| facts.reads.contains_key(binding) || facts.writes.contains_key(binding))
}

pub(super) fn bindings_are_mentioned_in_exprs<'a>(
    exprs: impl IntoIterator<Item = &'a HirExpr>,
    bindings: &[CarryBinding],
) -> bool {
    let mut facts = BindingFacts::default();
    for expr in exprs {
        super::super::super::visit::visit_expr(expr, &mut facts);
    }
    bindings
        .iter()
        .any(|binding| facts.reads.contains_key(binding))
}
