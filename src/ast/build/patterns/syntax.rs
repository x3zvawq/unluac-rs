//! 这个文件承载 AST build 阶段“只负责合法语法化”的语法模式恢复。
//!
//! 这里的职责边界是：只把 HIR 里已经显式存在、并且能无歧义还原成某个 Lua 语法节点的
//! 形状直接降回 AST。像 `global` 这种模式，在这里仅处理字节码里确实存在对应探测/
//! 赋值序列的“显式声明”；缺失声明补全、声明合并、函数声明降糖都不属于这里，
//! 而是留给后面的 Readability。
//!
//! 例子：
//! - `LocalDecl(probe) + ErrNil + Assign(global)` 会在这里直接降成显式
//!   `AstStmt::GlobalDecl`
//! - 它不会根据一次普通 `x = ...` 写入去猜测“源码里也许应该先有 `global x`”
//! - 它也不会把 `global f = function() end` 直接美化成 `function f() end`

use crate::hir::{HirExpr, HirLValue, HirStmt};

use super::super::exprs::PackLoweringContext;
use super::super::{AstLowerError, AstLowerer};
use crate::ast::common::{
    AstBindingRef, AstGlobalAttr, AstGlobalBinding, AstGlobalBindingTarget, AstGlobalDecl,
    AstGlobalName, AstLocalAttr, AstLocalDecl, AstStmt,
};

impl<'a> AstLowerer<'a> {
    pub(in crate::ast::build) fn try_lower_global_decl(
        &mut self,
        proto_index: usize,
        stmts: &[HirStmt],
        index: usize,
    ) -> Result<Option<(AstStmt, usize)>, AstLowerError> {
        let Some(HirStmt::LocalDecl(probe)) = stmts.get(index) else {
            return Ok(None);
        };
        let Some(HirStmt::ErrNil(err_nnil)) = stmts.get(index + 1) else {
            return Ok(None);
        };
        let Some(HirStmt::Assign(assign)) = stmts.get(index + 2) else {
            return Ok(None);
        };

        if !self.target.caps.global_decl {
            return Err(AstLowerError::UnsupportedFeature {
                dialect: self.target.version,
                feature: "global",
                context: "global declaration",
            });
        }

        if probe.bindings.len() != 1
            || !matches!((&probe.values.fixed[..], &probe.values.tail), ([_], None))
            || assign.targets.len() != 1
        {
            return Ok(None);
        }
        let HirExpr::LocalRef(probe_local) = &err_nnil.value else {
            return Ok(None);
        };
        if probe.bindings[0] != *probe_local {
            return Ok(None);
        }
        if super::super::analysis::count_local_uses_in_stmts(&stmts[(index + 1)..], *probe_local)
            != 1
        {
            return Ok(None);
        }
        let HirExpr::GlobalRef(probe_global) = &probe.values.fixed[0] else {
            return Ok(None);
        };
        let HirLValue::Global(assign_global) = &assign.targets[0] else {
            return Ok(None);
        };
        if probe_global.name != assign_global.name
            || err_nnil
                .name
                .as_ref()
                .is_some_and(|name| name != &assign_global.name)
        {
            return Ok(None);
        }
        let name = assign_global.name.clone();

        let values = self.lower_value_pack(
            proto_index,
            &assign.values,
            PackLoweringContext::TargetCounted(assign.targets.len()),
        )?;
        Ok(Some((
            AstStmt::GlobalDecl(Box::new(AstGlobalDecl {
                bindings: vec![AstGlobalBinding {
                    target: AstGlobalBindingTarget::Name(AstGlobalName { text: name }),
                    attr: AstGlobalAttr::None,
                }],
                values,
            })),
            3,
        )))
    }

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
                        self.recovered_local_binding(
                            AstBindingRef::Temp(binding),
                            if binding == *temp {
                                AstLocalAttr::Close
                            } else {
                                AstLocalAttr::None
                            },
                        )
                    })
                    .collect(),
                values: self.lower_value_pack(
                    proto_index,
                    &assign.values,
                    PackLoweringContext::TargetCounted(assign.targets.len()),
                )?,
            })),
            2,
        )))
    }
}
