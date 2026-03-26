//! AST build：需要看相邻 HIR 语句模式的 lowering。

use crate::hir::{HirExpr, HirLValue, HirStmt};

use super::{AstLowerError, AstLowerer};
use crate::ast::common::{
    AstBindingRef, AstGlobalAttr, AstGlobalBinding, AstGlobalDecl, AstGlobalName, AstLocalAttr,
    AstLocalBinding, AstLocalDecl, AstStmt,
};

impl<'a> AstLowerer<'a> {
    pub(super) fn try_lower_global_decl(
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

        if probe.bindings.len() != 1 || probe.values.len() != 1 || assign.targets.len() != 1 {
            return Ok(None);
        }
        let HirExpr::LocalRef(probe_local) = &err_nnil.value else {
            return Ok(None);
        };
        if probe.bindings[0] != *probe_local {
            return Ok(None);
        }
        if super::analysis::count_local_uses_in_stmts(&stmts[(index + 1)..], *probe_local) != 1 {
            return Ok(None);
        }
        let Some(name) = err_nnil.name.as_ref() else {
            return Ok(None);
        };
        if !lvalue_matches_global_name(&assign.targets[0], name) {
            return Ok(None);
        }

        let values = assign
            .values
            .iter()
            .map(|value| self.lower_expr(proto_index, value))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Some((
            AstStmt::GlobalDecl(Box::new(AstGlobalDecl {
                bindings: vec![AstGlobalBinding {
                    name: AstGlobalName { text: name.clone() },
                    attr: AstGlobalAttr::None,
                }],
                values,
            })),
            3,
        )))
    }

    pub(super) fn try_lower_local_close_decl(
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
                bindings: vec![AstLocalBinding {
                    id: AstBindingRef::Local(*local),
                    attr: AstLocalAttr::Close,
                }],
                values: local_decl
                    .values
                    .iter()
                    .map(|value| self.lower_expr(proto_index, value))
                    .collect::<Result<Vec<_>, _>>()?,
            })),
            2,
        )))
    }

    pub(super) fn try_lower_temp_close_decl(
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
        if assign.targets.len() != 1 || assign.values.len() != 1 {
            return Err(AstLowerError::InvalidToBeClosed {
                proto: proto_index,
                reason: "to-be-closed temp must be introduced by a single-value assignment",
            });
        }
        let HirLValue::Temp(target) = &assign.targets[0] else {
            return Ok(None);
        };
        if target != temp {
            return Ok(None);
        }
        if !self.target.caps.local_close {
            return Err(AstLowerError::UnsupportedFeature {
                dialect: self.target.version,
                feature: "local <close>",
                context: "to-be-closed synthesized temp local",
            });
        }
        Ok(Some((
            AstStmt::LocalDecl(Box::new(AstLocalDecl {
                bindings: vec![AstLocalBinding {
                    id: AstBindingRef::Temp(*temp),
                    attr: AstLocalAttr::Close,
                }],
                values: vec![self.lower_expr(proto_index, &assign.values[0])?],
            })),
            2,
        )))
    }

    pub(super) fn try_lower_generic_for_init(
        &mut self,
        proto_index: usize,
        stmts: &[HirStmt],
        index: usize,
        continue_target: Option<crate::ast::AstLabelId>,
    ) -> Result<Option<(AstStmt, usize)>, AstLowerError> {
        let Some(HirStmt::Assign(assign)) = stmts.get(index) else {
            return Ok(None);
        };

        let (generic_for, consumed, close_temp) = match (stmts.get(index + 1), stmts.get(index + 2))
        {
            (Some(HirStmt::ToBeClosed(to_be_closed)), Some(HirStmt::GenericFor(generic_for))) => {
                let HirExpr::TempRef(close_temp) = &to_be_closed.value else {
                    return Ok(None);
                };
                (generic_for, 3, Some(*close_temp))
            }
            (Some(HirStmt::GenericFor(generic_for)), _) => (generic_for, 2, None),
            _ => return Ok(None),
        };

        if !assign_targets_match_generic_for_init(
            assign.targets.as_slice(),
            generic_for,
            close_temp,
        ) {
            return Ok(None);
        }

        Ok(Some((
            self.lower_generic_for_stmt(
                proto_index,
                generic_for,
                Some(assign.values.as_slice()),
                continue_target,
            )?,
            consumed,
        )))
    }
}

fn lvalue_matches_global_name(target: &HirLValue, name: &str) -> bool {
    match target {
        HirLValue::Global(global) => global.name == name,
        HirLValue::TableAccess(access) => {
            matches!(&access.key, HirExpr::String(key) if key == name)
        }
        _ => false,
    }
}

fn assign_targets_match_generic_for_init(
    targets: &[HirLValue],
    generic_for: &crate::hir::HirGenericFor,
    close_temp: Option<crate::hir::TempId>,
) -> bool {
    let expected_targets = generic_for.iterator.len() + usize::from(close_temp.is_some());
    if targets.len() != expected_targets {
        return false;
    }

    let iter_targets_match =
        targets
            .iter()
            .zip(generic_for.iterator.iter())
            .all(|(target, iterator)| match (target, iterator) {
                (HirLValue::Temp(target_temp), HirExpr::TempRef(iterator_temp)) => {
                    target_temp == iterator_temp
                }
                _ => false,
            });
    if !iter_targets_match {
        return false;
    }

    match (close_temp, targets.last()) {
        (Some(close_temp), Some(HirLValue::Temp(target_temp))) => *target_temp == close_temp,
        (None, _) => true,
        _ => false,
    }
}
