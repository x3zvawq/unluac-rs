//! carried binding 读取事实的只读收集器。
//!
//! 这个模块只扫描表达式/语句里对 local/temp binding 的读取，用于判断 handoff seed
//! 是否只读取单个 carried 状态，以及 suffix 是否仍观察旧 binding。它不判断写入安全性，
//! 也不执行 rewrite。
//!
//! 例子：
//! - 输入表达式：`state + 1`
//! - 输出事实：读取了唯一 carried binding `state`

use std::collections::BTreeSet;

use crate::hir::common::{HirExpr, HirStmt};

use super::super::visit::{HirVisitor, visit_expr, visit_stmts};
use super::binding::CarryBinding;

#[derive(Default)]
pub(super) struct BindingReadCollector {
    pub(super) reads: BTreeSet<CarryBinding>,
}

impl BindingReadCollector {
    pub(super) fn collect_stmts(&mut self, stmts: &[HirStmt]) {
        visit_stmts(stmts, self);
    }

    pub(super) fn collect_expr(&mut self, expr: &HirExpr) {
        visit_expr(expr, self);
    }

    pub(super) fn single_read(&self) -> Option<CarryBinding> {
        let mut reads = self.reads.iter();
        let read = *reads.next()?;
        reads.next().is_none().then_some(read)
    }
}

impl HirVisitor for BindingReadCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        let binding = match expr {
            HirExpr::LocalRef(local) => Some(CarryBinding::Local(*local)),
            HirExpr::TempRef(temp) => Some(CarryBinding::Temp(*temp)),
            _ => None,
        };
        if let Some(binding) = binding {
            self.reads.insert(binding);
        }
    }
}
