//! 将 HIR 已证明的 TBC 声明配对降低为目标方言的 close 声明。
//!
//! 消费显式绑定与 value-pack 身份，不重建资源协议或作用域。

use crate::hir::{HirExpr, HirLValue, HirStmt, HirTbcDeclaration};

use super::super::exprs::PackLoweringContext;
use super::super::{AstLowerError, AstLowerer};
use crate::ast::common::{AstBindingRef, AstLocalAttr, AstLocalDecl, AstStmt};

impl<'a> AstLowerer<'a> {
    pub(in crate::ast::build) fn try_lower_close_decl(
        &mut self,
        proto_index: usize,
        stmts: &[HirStmt],
        index: usize,
    ) -> Result<Option<(AstStmt, usize)>, AstLowerError> {
        let Some(previous) = stmts.get(index) else {
            return Ok(None);
        };
        let Some(HirStmt::ToBeClosed(to_be_closed)) = stmts.get(index + 1) else {
            return Ok(None);
        };
        // 保留不精确 temp 包的专用诊断；其它不配对形状由残留 TBC 入口报告。
        if let (HirStmt::Assign(assign), HirExpr::TempRef(_)) = (previous, &to_be_closed.value)
            && assign.values.exact_result_len() != Some(assign.targets.len())
        {
            return Err(AstLowerError::InvalidToBeClosed {
                proto: proto_index,
                reason: "to-be-closed declaration must have one value for every binding",
            });
        }
        let Some(declaration) = to_be_closed.declaration(previous) else {
            return Ok(None);
        };
        if !self.target.caps.local_close {
            return Err(AstLowerError::UnsupportedFeature {
                dialect: self.target.version,
                feature: "local <close>",
                context: match declaration {
                    HirTbcDeclaration::Local { .. } => "to-be-closed local declaration",
                    HirTbcDeclaration::Temps { .. } => "to-be-closed synthesized temp local",
                },
            });
        }
        let (bindings, values) = match declaration {
            HirTbcDeclaration::Local { local, declaration } => (
                vec![self.lower_local_binding(proto_index, local, AstLocalAttr::Close)],
                &declaration.values,
            ),
            HirTbcDeclaration::Temps {
                close_temp,
                assignment,
            } => (
                assignment
                    .targets
                    .iter()
                    .map(|target| {
                        let HirLValue::Temp(temp) = target else {
                            unreachable!("TBC declaration query admits only temp targets");
                        };
                        let mut binding = self.lower_temp_binding(proto_index, *temp);
                        if binding.id == AstBindingRef::Temp(close_temp) {
                            binding.attr = AstLocalAttr::Close;
                        }
                        binding
                    })
                    .collect(),
                &assignment.values,
            ),
        };
        let values = self.lower_value_pack(
            proto_index,
            values,
            PackLoweringContext::TargetCounted(bindings.len()),
        )?;
        Ok(Some((
            AstStmt::LocalDecl(Box::new(AstLocalDecl {
                bindings,
                values,
                // TBC 配对是独立声明事务，不继承 initializer-merge 或 root profile。
                initializer_merge_transaction: None,
                initializer_root_profile: None,
            })),
            2,
        )))
    }
}
