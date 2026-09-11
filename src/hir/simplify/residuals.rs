//! HIR 收敛后的退出事实。
//!
//! 消费共享 HIR visitor 统计仍存在的 Decision/Unresolved 与控制语法；不读取 Structure。
//! 例如不可达 goto 已被 HIR 删除，原先从 Structure 带入的 goto 要求也应在这里退役，
//! 不能迫使 AST 根据过期要求拒绝 Lua 5.1。失败 proto 与 unresolved 诊断仍保留原证据。

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
            HirExpr::Decision(_) => self.decisions += 1,
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
