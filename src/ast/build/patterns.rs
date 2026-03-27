//! AST build：需要看相邻 HIR 语句模式的 lowering。

use crate::hir::{HirCallExpr, HirExpr, HirLValue, HirStmt, LocalId};

use super::{AstLowerError, AstLowerer};
use crate::ast::common::{
    AstAssign, AstBindingRef, AstCallKind, AstCallStmt, AstExpr, AstGlobalAttr, AstGlobalBinding,
    AstGlobalBindingTarget, AstGlobalDecl, AstGlobalName, AstLocalAttr, AstLocalDecl,
    AstMethodCallExpr, AstStmt,
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
                    target: AstGlobalBindingTarget::Name(AstGlobalName { text: name.clone() }),
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
                bindings: vec![self.lower_local_binding(proto_index, *local, AstLocalAttr::Close)],
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
                bindings: vec![self.recovered_local_binding(
                    AstBindingRef::Temp(*temp),
                    AstLocalAttr::Close,
                )],
                values: vec![self.lower_expr(proto_index, &assign.values[0])?],
            })),
            2,
        )))
    }

    pub(super) fn try_lower_method_call_chain(
        &mut self,
        proto_index: usize,
        stmts: &[HirStmt],
        index: usize,
    ) -> Result<Option<(AstStmt, usize)>, AstLowerError> {
        let Some((receiver_alias, receiver_expr)) = receiver_alias_stmt(stmts.get(index)) else {
            return Ok(None);
        };
        if super::analysis::count_local_uses_in_stmts(&stmts[(index + 1)..], receiver_alias) != 1 {
            return Ok(None);
        }

        let Some((field_alias, first_receiver, first_method)) =
            field_alias_stmt(stmts.get(index + 1))
        else {
            return Ok(None);
        };
        if !hir_exprs_equal(receiver_expr, first_receiver)
            || super::analysis::count_local_uses_in_stmts(&stmts[(index + 2)..], field_alias) != 1
        {
            return Ok(None);
        }

        let Some((result_local, first_call)) = method_call_sink(stmts.get(index + 2), field_alias)
        else {
            return Ok(None);
        };
        if first_call.args.is_empty()
            || !matches!(first_call.args.first(), Some(HirExpr::LocalRef(local)) if *local == receiver_alias)
            || super::analysis::count_local_uses_in_stmts(&stmts[(index + 3)..], result_local) != 0
        {
            return Ok(None);
        }

        let Some(second_call_stmt) = chained_method_call_stmt(stmts.get(index + 3), result_local)
        else {
            return Ok(None);
        };

        let first_expr = self.lower_method_call_expr(
            proto_index,
            receiver_expr,
            first_method,
            &first_call.args[1..],
        )?;
        let second_call =
            self.lower_chained_method_call(proto_index, first_expr, second_call_stmt)?;
        Ok(Some((
            AstStmt::CallStmt(Box::new(AstCallStmt { call: second_call })),
            4,
        )))
    }

    pub(super) fn try_lower_method_call_alias(
        &mut self,
        proto_index: usize,
        stmts: &[HirStmt],
        index: usize,
    ) -> Result<Option<(AstStmt, usize)>, AstLowerError> {
        let Some((field_alias, receiver_expr, method)) = field_alias_stmt(stmts.get(index)) else {
            return Ok(None);
        };
        if super::analysis::count_local_uses_in_stmts(&stmts[(index + 1)..], field_alias) != 1 {
            return Ok(None);
        }

        let Some(sink_stmt) = stmts.get(index + 1) else {
            return Ok(None);
        };
        let Some(lowered) = self.lower_method_alias_sink(
            proto_index,
            sink_stmt,
            field_alias,
            receiver_expr,
            method,
        )?
        else {
            return Ok(None);
        };
        Ok(Some((lowered, 2)))
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

impl<'a> AstLowerer<'a> {
    fn lower_method_alias_sink(
        &mut self,
        proto_index: usize,
        stmt: &HirStmt,
        callee_alias: LocalId,
        receiver_expr: &HirExpr,
        method: &str,
    ) -> Result<Option<AstStmt>, AstLowerError> {
        match stmt {
            HirStmt::LocalDecl(local_decl) => {
                let [value] = local_decl.values.as_slice() else {
                    return Ok(None);
                };
                let Some(call) = method_call_expr_from_hir(value, callee_alias) else {
                    return Ok(None);
                };
                let method_call = self.lower_method_call_expr(
                    proto_index,
                    receiver_expr,
                    method,
                    &call.args[1..],
                )?;
                Ok(Some(AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: local_decl
                        .bindings
                        .iter()
                        .copied()
                        .map(|binding| {
                            self.lower_local_binding(proto_index, binding, AstLocalAttr::None)
                        })
                        .collect(),
                    values: vec![method_call],
                }))))
            }
            HirStmt::Assign(assign) => {
                let [value] = assign.values.as_slice() else {
                    return Ok(None);
                };
                let Some(call) = method_call_expr_from_hir(value, callee_alias) else {
                    return Ok(None);
                };
                let method_call = self.lower_method_call_expr(
                    proto_index,
                    receiver_expr,
                    method,
                    &call.args[1..],
                )?;
                Ok(Some(AstStmt::Assign(Box::new(AstAssign {
                    targets: assign
                        .targets
                        .iter()
                        .map(|target| self.lower_lvalue(proto_index, target))
                        .collect::<Result<Vec<_>, _>>()?,
                    values: vec![method_call],
                }))))
            }
            HirStmt::CallStmt(call_stmt) => {
                if !matches!(callee_local_ref(&call_stmt.call.callee), Some(local) if local == callee_alias)
                    || !call_stmt.call.method
                    || call_stmt.call.args.is_empty()
                {
                    return Ok(None);
                }
                Ok(Some(AstStmt::CallStmt(Box::new(AstCallStmt {
                    call: self.lower_method_call_kind(
                        proto_index,
                        receiver_expr,
                        method,
                        &call_stmt.call.args[1..],
                    )?,
                }))))
            }
            _ => Ok(None),
        }
    }

    fn lower_method_call_kind(
        &mut self,
        proto_index: usize,
        receiver_expr: &HirExpr,
        method: &str,
        args: &[HirExpr],
    ) -> Result<AstCallKind, AstLowerError> {
        Ok(AstCallKind::MethodCall(Box::new(AstMethodCallExpr {
            receiver: self.lower_expr(proto_index, receiver_expr)?,
            method: method.to_owned(),
            args: args
                .iter()
                .map(|arg| self.lower_expr(proto_index, arg))
                .collect::<Result<Vec<_>, _>>()?,
        })))
    }

    fn lower_method_call_expr(
        &mut self,
        proto_index: usize,
        receiver_expr: &HirExpr,
        method: &str,
        args: &[HirExpr],
    ) -> Result<AstExpr, AstLowerError> {
        Ok(AstExpr::MethodCall(Box::new(
            match self.lower_method_call_kind(proto_index, receiver_expr, method, args)? {
                AstCallKind::MethodCall(call) => *call,
                AstCallKind::Call(_) => unreachable!("method-call lowering must keep method shape"),
            },
        )))
    }

    fn lower_chained_method_call(
        &mut self,
        proto_index: usize,
        receiver: AstExpr,
        call: &HirCallExpr,
    ) -> Result<AstCallKind, AstLowerError> {
        let HirExpr::TableAccess(access) = &call.callee else {
            return Err(AstLowerError::InvalidMethodCallPattern {
                proto: proto_index,
                reason: "chained method call must keep a field-access callee",
            });
        };
        let HirExpr::String(method) = &access.key else {
            return Err(AstLowerError::InvalidMethodCallPattern {
                proto: proto_index,
                reason: "chained method call requires a named method field",
            });
        };
        Ok(AstCallKind::MethodCall(Box::new(AstMethodCallExpr {
            receiver,
            method: method.clone(),
            args: call
                .args
                .iter()
                .skip(1)
                .map(|arg| self.lower_expr(proto_index, arg))
                .collect::<Result<Vec<_>, _>>()?,
        })))
    }
}

fn receiver_alias_stmt(stmt: Option<&HirStmt>) -> Option<(LocalId, &HirExpr)> {
    let HirStmt::LocalDecl(local_decl) = stmt? else {
        return None;
    };
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    let [value] = local_decl.values.as_slice() else {
        return None;
    };
    Some((*binding, value))
}

fn field_alias_stmt(stmt: Option<&HirStmt>) -> Option<(LocalId, &HirExpr, &str)> {
    let HirStmt::LocalDecl(local_decl) = stmt? else {
        return None;
    };
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    let [HirExpr::TableAccess(access)] = local_decl.values.as_slice() else {
        return None;
    };
    let HirExpr::String(method) = &access.key else {
        return None;
    };
    Some((*binding, &access.base, method))
}

fn method_call_sink(
    stmt: Option<&HirStmt>,
    callee_alias: LocalId,
) -> Option<(LocalId, &HirCallExpr)> {
    let HirStmt::LocalDecl(local_decl) = stmt? else {
        return None;
    };
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    let [value] = local_decl.values.as_slice() else {
        return None;
    };
    let call = method_call_expr_from_hir(value, callee_alias)?;
    Some((*binding, call))
}

fn method_call_expr_from_hir(expr: &HirExpr, callee_alias: LocalId) -> Option<&HirCallExpr> {
    let HirExpr::Call(call) = expr else {
        return None;
    };
    if !call.method
        || !matches!(callee_local_ref(&call.callee), Some(local) if local == callee_alias)
    {
        return None;
    }
    Some(call)
}

fn chained_method_call_stmt(
    stmt: Option<&HirStmt>,
    receiver_local: LocalId,
) -> Option<&HirCallExpr> {
    let HirStmt::CallStmt(call_stmt) = stmt? else {
        return None;
    };
    let HirExpr::TableAccess(access) = &call_stmt.call.callee else {
        return None;
    };
    if !call_stmt.call.method
        || !matches!(&access.base, HirExpr::LocalRef(local) if *local == receiver_local)
        || !matches!(call_stmt.call.args.first(), Some(HirExpr::LocalRef(local)) if *local == receiver_local)
    {
        return None;
    }
    Some(&call_stmt.call)
}

fn callee_local_ref(expr: &HirExpr) -> Option<LocalId> {
    let HirExpr::LocalRef(local) = expr else {
        return None;
    };
    Some(*local)
}

fn hir_exprs_equal(lhs: &HirExpr, rhs: &HirExpr) -> bool {
    lhs == rhs
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

#[cfg(test)]
mod tests;

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
