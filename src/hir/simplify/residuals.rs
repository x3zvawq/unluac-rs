//! 发布 HIR 收敛后的残余节点与控制语法要求。
//!
//! 消费当前 HIR，保留失败诊断证据并退役已经消失的前层要求。

use crate::hir::common::{HirControlFlowFeature, HirExitRequirement};
use crate::hir::visit::{HirVisitor, visit_block};
use crate::hir::{HirExpr, HirModule, HirStmt};

#[derive(Default)]
pub(super) struct HirExitResiduals {
    pub decisions: usize,
    pub unresolved: usize,
    goto_label: bool,
    continue_statement: bool,
}

impl HirExitResiduals {
    pub fn has_soft_residuals(&self) -> bool {
        self.decisions != 0 || self.unresolved != 0
    }
}

impl HirVisitor<'_> for HirExitResiduals {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::Goto(_) | HirStmt::Label(_) => self.goto_label = true,
            HirStmt::Continue => self.continue_statement = true,
            _ => {}
        }
    }

    fn visit_expr(&mut self, expr: &HirExpr) {
        match expr {
            HirExpr::Decision(decision) if !decision.emit_as_luau_if => self.decisions += 1,
            HirExpr::Unresolved(_) => self.unresolved += 1,
            _ => {}
        }
    }
}

pub(super) fn finalize_hir_exit_requirements(module: &mut HirModule) -> HirExitResiduals {
    let mut total = HirExitResiduals::default();
    for proto in &mut module.protos {
        let mut residuals = HirExitResiduals::default();
        visit_block(&proto.body, &mut residuals);
        total.decisions += residuals.decisions;
        total.unresolved += residuals.unresolved;
        if proto.failure.is_some() {
            continue;
        }
        proto
            .exit_requirements
            .retain(|requirement| match requirement {
                HirExitRequirement::RequiredControlFlow { feature, .. } => match feature {
                    HirControlFlowFeature::GotoLabel => residuals.goto_label,
                    HirControlFlowFeature::ContinueStatement => residuals.continue_statement,
                },
                HirExitRequirement::UnresolvedValue { .. } => true,
            });
    }
    total
}

pub(super) fn emit_hir_warning(message: String) {
    eprintln!("[unluac][hir-warning] {message}");
}
