//! 发布 region 内的 carried 读取身份与写入次数，不修改语句。
//! 读取只用于存在性判断；写入次数还需与预期出口数比较，例如每个分支必须恰好写一次 result。

use super::*;

#[derive(Default)]
pub(super) struct BindingFacts {
    pub(super) reads: BTreeSet<CarryBinding>,
    pub(super) writes: BTreeMap<CarryBinding, usize>,
}

impl HirVisitor for BindingFacts {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let Some(binding) = carry_binding_from_expr(expr) {
            self.reads.insert(binding);
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
