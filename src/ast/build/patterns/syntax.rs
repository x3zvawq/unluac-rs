//! 这个文件承载 AST build 阶段需要相邻 HIR 节点才能完成的合法语法化。
//!
//! 这里仅把 definition 与紧邻的 `ToBeClosed` 合成目标方言要求的 `<close>` 声明；它依赖
//! HIR 已经给出的 binding 与 value-pack 身份，不重新识别 low-IR 协议，也不改变求值顺序。
//! `global` 协议由 HIR 直接发布 typed `HirStmt::GlobalDecl`，本模块不会从普通声明、诊断和
//! 赋值的相邻文本形状反猜。缺失声明补全、声明合并、函数声明降糖仍属于 Readability。
//!
//! 例子：
//! - `LocalDecl(binding) + ToBeClosed(binding)` 会落成 `local binding <close> = ...`
//! - 普通 `Assign(global)` 不会在这里被猜成 `global` 声明

use crate::hir::{HirExpr, HirLValue, HirStmt};

use super::super::exprs::PackLoweringContext;
use super::super::{AstLowerError, AstLowerer};
use crate::ast::common::{AstBindingRef, AstLocalAttr, AstLocalDecl, AstStmt};

impl<'a> AstLowerer<'a> {
    pub(in crate::ast::build) fn try_lower_local_close_decl(
        &mut self,
        proto_index: usize,
        stmts: &[HirStmt],
        index: usize,
    ) -> Result<Option<(AstStmt, usize)>, AstLowerError> {
        let Some(HirStmt::LocalDecl(local_decl)) = stmts.get(index) else {
            return Ok(None);
        };
        let Some(HirStmt::ToBeClosed(to_be_closed)) = stmts.get(index + 1) else {
            return Ok(None);
        };
        let HirExpr::LocalRef(local) = &to_be_closed.value else {
            return Ok(None);
        };
        if local_decl.bindings.len() != 1 || local_decl.bindings[0] != *local {
            return Ok(None);
        }
        if !self.target.caps.local_close {
            return Err(AstLowerError::UnsupportedFeature {
                dialect: self.target.version,
                feature: "local <close>",
                context: "to-be-closed local declaration",
            });
        }
        Ok(Some((
            AstStmt::LocalDecl(Box::new(AstLocalDecl {
                bindings: vec![self.lower_local_binding(proto_index, *local, AstLocalAttr::Close)],
                values: self.lower_value_pack(
                    proto_index,
                    &local_decl.values,
                    PackLoweringContext::TargetCounted(local_decl.bindings.len()),
                )?,
                // close syntax consumes a different two-statement protocol, so it cannot retain
                // an initializer-merge endpoint even if malformed input happened to carry one.
                initializer_merge_transaction: None,
                initializer_root_profile: None,
            })),
            2,
        )))
    }

    pub(in crate::ast::build) fn try_lower_temp_close_decl(
        &mut self,
        proto_index: usize,
        stmts: &[HirStmt],
        index: usize,
    ) -> Result<Option<(AstStmt, usize)>, AstLowerError> {
        let Some(HirStmt::Assign(assign)) = stmts.get(index) else {
            return Ok(None);
        };
        let Some(HirStmt::ToBeClosed(to_be_closed)) = stmts.get(index + 1) else {
            return Ok(None);
        };
        let HirExpr::TempRef(temp) = &to_be_closed.value else {
            return Ok(None);
        };
        if assign.values.exact_result_len() != Some(assign.targets.len()) {
            return Err(AstLowerError::InvalidToBeClosed {
                proto: proto_index,
                reason: "to-be-closed declaration must have one value for every binding",
            });
        }
        let Some(HirLValue::Temp(last_target)) = assign.targets.last() else {
            return Ok(None);
        };
        if last_target != temp {
            return Ok(None);
        }
        let Some(bindings) = assign
            .targets
            .iter()
            .map(|target| match target {
                HirLValue::Temp(target) => Some(*target),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()
        else {
            return Ok(None);
        };
        if !self.target.caps.local_close {
            return Err(AstLowerError::UnsupportedFeature {
                dialect: self.target.version,
                feature: "local <close>",
                context: "to-be-closed synthesized temp local",
            });
        }
        Ok(Some((
            AstStmt::LocalDecl(Box::new(AstLocalDecl {
                bindings: bindings
                    .into_iter()
                    .map(|binding| {
                        let mut binding = self.lower_temp_binding(proto_index, binding);
                        if binding.id == AstBindingRef::Temp(*temp) {
                            binding.attr = AstLocalAttr::Close;
                        }
                        binding
                    })
                    .collect(),
                values: self.lower_value_pack(
                    proto_index,
                    &assign.values,
                    PackLoweringContext::TargetCounted(assign.targets.len()),
                )?,
                initializer_merge_transaction: None,
                initializer_root_profile: None,
            })),
            2,
        )))
    }
}
