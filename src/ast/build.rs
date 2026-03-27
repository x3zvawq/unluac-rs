//! HIR -> AST build 阶段入口。

mod analysis;
mod exprs;
mod patterns;

use std::collections::BTreeSet;

use crate::hir::{HirBlock, HirGenericFor, HirModule, HirStmt, TempId};

use self::analysis::{
    block_has_continue, collect_close_temps, collect_referenced_temps, max_hir_label_id,
};
use super::common::{
    AstAssign, AstBindingRef, AstBlock, AstCallStmt, AstExpr, AstGenericFor, AstGoto, AstIf,
    AstIndexAccess, AstLabel, AstLabelId, AstLocalAttr, AstLocalBinding, AstLocalDecl,
    AstLocalOrigin, AstModule, AstNumericFor, AstRepeat, AstReturn, AstStmt, AstTargetDialect,
    AstWhile,
};
use super::error::AstLowerError;

/// 对外的 AST lowering 入口。
pub fn lower_ast(module: &HirModule, target: AstTargetDialect) -> Result<AstModule, AstLowerError> {
    let mut lowerer = AstLowerer::new(module, target);
    lowerer.lower_module()
}

struct AstLowerer<'a> {
    module: &'a HirModule,
    target: AstTargetDialect,
    next_synthetic_label: usize,
}

impl<'a> AstLowerer<'a> {
    fn new(module: &'a HirModule, target: AstTargetDialect) -> Self {
        Self {
            module,
            target,
            next_synthetic_label: max_hir_label_id(module) + 1,
        }
    }

    fn lower_module(&mut self) -> Result<AstModule, AstLowerError> {
        let body = self.lower_proto_body(self.module.entry.index())?;
        Ok(AstModule {
            entry_function: self.module.entry,
            body,
        })
    }

    fn lower_proto_body(&mut self, proto_index: usize) -> Result<AstBlock, AstLowerError> {
        let proto =
            self.module
                .protos
                .get(proto_index)
                .ok_or(AstLowerError::MissingChildProto {
                    proto: self.module.entry.index(),
                    child: proto_index,
                })?;
        let close_temps = collect_close_temps(&proto.body);
        self.lower_block(proto_index, &proto.body, Some(&close_temps), None)
    }

    fn lower_block(
        &mut self,
        proto_index: usize,
        block: &HirBlock,
        root_close_temps: Option<&BTreeSet<TempId>>,
        continue_target: Option<AstLabelId>,
    ) -> Result<AstBlock, AstLowerError> {
        let proto = &self.module.protos[proto_index];
        let mut stmts = Vec::new();
        if let Some(close_temps) = root_close_temps {
            let referenced_temps = collect_referenced_temps(block);
            let temp_bindings = proto
                .temps
                .iter()
                .copied()
                .filter(|temp| referenced_temps.contains(temp) && !close_temps.contains(temp))
                .map(|temp| {
                    self.recovered_local_binding(AstBindingRef::Temp(temp), AstLocalAttr::None)
                })
                .collect::<Vec<_>>();
            if !temp_bindings.is_empty() {
                stmts.push(AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: temp_bindings,
                    values: Vec::new(),
                })));
            }
        }

        let mut index = 0;
        while index < block.stmts.len() {
            if let Some((stmt, consumed)) =
                self.try_lower_global_decl(proto_index, &block.stmts, index)?
            {
                stmts.push(stmt);
                index += consumed;
                continue;
            }

            if let Some((stmt, consumed)) =
                self.try_lower_local_close_decl(proto_index, &block.stmts, index)?
            {
                stmts.push(stmt);
                index += consumed;
                continue;
            }

            if let Some((stmt, consumed)) =
                self.try_lower_generic_for_init(proto_index, &block.stmts, index, continue_target)?
            {
                stmts.push(stmt);
                index += consumed;
                continue;
            }

            if let Some((stmt, consumed)) =
                self.try_lower_method_call_chain(proto_index, &block.stmts, index)?
            {
                stmts.push(stmt);
                index += consumed;
                continue;
            }

            if let Some((stmt, consumed)) =
                self.try_lower_method_call_alias(proto_index, &block.stmts, index)?
            {
                stmts.push(stmt);
                index += consumed;
                continue;
            }

            if let Some((stmt, consumed)) =
                self.try_lower_temp_close_decl(proto_index, &block.stmts, index)?
            {
                stmts.push(stmt);
                index += consumed;
                continue;
            }

            let stmt = match &block.stmts[index] {
                HirStmt::LocalDecl(local_decl) => {
                    AstStmt::LocalDecl(Box::new(self.lower_local_decl(proto_index, local_decl)?))
                }
                HirStmt::Assign(assign) => {
                    AstStmt::Assign(Box::new(self.lower_assign(proto_index, assign)?))
                }
                HirStmt::TableSetList(set_list) => {
                    if set_list.trailing_multivalue.is_some() {
                        return Err(AstLowerError::UnsupportedSetListTrailingMultivalue {
                            proto: proto_index,
                        });
                    }
                    let base = self.lower_expr(proto_index, &set_list.base)?;
                    for (offset, value) in set_list.values.iter().enumerate() {
                        let index_value =
                            AstExpr::Integer(i64::from(set_list.start_index) + offset as i64);
                        let target =
                            super::common::AstLValue::IndexAccess(Box::new(AstIndexAccess {
                                base: base.clone(),
                                index: index_value,
                            }));
                        stmts.push(AstStmt::Assign(Box::new(AstAssign {
                            targets: vec![target],
                            values: vec![self.lower_expr(proto_index, value)?],
                        })));
                    }
                    index += 1;
                    continue;
                }
                HirStmt::ErrNil(_) => {
                    return Err(AstLowerError::InvalidGlobalDeclPattern { proto: proto_index });
                }
                HirStmt::ToBeClosed(_) => {
                    return Err(AstLowerError::InvalidToBeClosed {
                        proto: proto_index,
                        reason: "standalone to-be-closed has no attachable declaration",
                    });
                }
                HirStmt::Close(_) => {
                    return Err(AstLowerError::UnsupportedClose { proto: proto_index });
                }
                HirStmt::CallStmt(call_stmt) => AstStmt::CallStmt(Box::new(AstCallStmt {
                    call: self.lower_call(proto_index, &call_stmt.call)?,
                })),
                HirStmt::Return(ret) => AstStmt::Return(Box::new(AstReturn {
                    values: ret
                        .values
                        .iter()
                        .map(|value| self.lower_expr(proto_index, value))
                        .collect::<Result<Vec<_>, _>>()?,
                })),
                HirStmt::If(if_stmt) => AstStmt::If(Box::new(AstIf {
                    cond: self.lower_expr(proto_index, &if_stmt.cond)?,
                    then_block: self.lower_block(
                        proto_index,
                        &if_stmt.then_block,
                        None,
                        continue_target,
                    )?,
                    else_block: if_stmt
                        .else_block
                        .as_ref()
                        .map(|else_block| {
                            self.lower_block(proto_index, else_block, None, continue_target)
                        })
                        .transpose()?,
                })),
                HirStmt::While(while_stmt) => {
                    let loop_continue = self.loop_continue_label_if_needed(&while_stmt.body);
                    let mut body = self.lower_block(
                        proto_index,
                        &while_stmt.body,
                        None,
                        loop_continue.or(continue_target),
                    )?;
                    if let Some(label) = loop_continue {
                        body.stmts
                            .push(AstStmt::Label(Box::new(AstLabel { id: label })));
                    }
                    AstStmt::While(Box::new(AstWhile {
                        cond: self.lower_expr(proto_index, &while_stmt.cond)?,
                        body,
                    }))
                }
                HirStmt::Repeat(repeat_stmt) => {
                    let loop_continue = self.loop_continue_label_if_needed(&repeat_stmt.body);
                    let mut body = self.lower_block(
                        proto_index,
                        &repeat_stmt.body,
                        None,
                        loop_continue.or(continue_target),
                    )?;
                    if let Some(label) = loop_continue {
                        body.stmts
                            .push(AstStmt::Label(Box::new(AstLabel { id: label })));
                    }
                    AstStmt::Repeat(Box::new(AstRepeat {
                        body,
                        cond: self.lower_expr(proto_index, &repeat_stmt.cond)?,
                    }))
                }
                HirStmt::NumericFor(numeric_for) => {
                    let loop_continue = self.loop_continue_label_if_needed(&numeric_for.body);
                    let mut body = self.lower_block(
                        proto_index,
                        &numeric_for.body,
                        None,
                        loop_continue.or(continue_target),
                    )?;
                    if let Some(label) = loop_continue {
                        body.stmts
                            .push(AstStmt::Label(Box::new(AstLabel { id: label })));
                    }
                    AstStmt::NumericFor(Box::new(AstNumericFor {
                        binding: AstBindingRef::Local(numeric_for.binding),
                        start: self.lower_expr(proto_index, &numeric_for.start)?,
                        limit: self.lower_expr(proto_index, &numeric_for.limit)?,
                        step: self.lower_expr(proto_index, &numeric_for.step)?,
                        body,
                    }))
                }
                HirStmt::GenericFor(generic_for) => {
                    self.lower_generic_for_stmt(proto_index, generic_for, None, continue_target)?
                }
                HirStmt::Break => AstStmt::Break,
                HirStmt::Continue => {
                    if self.target.caps.continue_stmt {
                        AstStmt::Continue
                    } else if let Some(label) = continue_target {
                        if !self.target.caps.goto_label {
                            return Err(AstLowerError::UnsupportedFeature {
                                dialect: self.target.version,
                                feature: "continue",
                                context: "continue statement",
                            });
                        }
                        AstStmt::Goto(Box::new(AstGoto { target: label }))
                    } else {
                        return Err(AstLowerError::UnsupportedFeature {
                            dialect: self.target.version,
                            feature: "continue",
                            context: "continue statement",
                        });
                    }
                }
                HirStmt::Goto(goto_stmt) => {
                    if !self.target.caps.goto_label {
                        return Err(AstLowerError::UnsupportedFeature {
                            dialect: self.target.version,
                            feature: "goto",
                            context: "goto statement",
                        });
                    }
                    AstStmt::Goto(Box::new(AstGoto {
                        target: goto_stmt.target.into(),
                    }))
                }
                HirStmt::Label(label) => {
                    if !self.target.caps.goto_label {
                        return Err(AstLowerError::UnsupportedFeature {
                            dialect: self.target.version,
                            feature: "label",
                            context: "label statement",
                        });
                    }
                    AstStmt::Label(Box::new(AstLabel {
                        id: label.id.into(),
                    }))
                }
                HirStmt::Block(inner) => AstStmt::DoBlock(Box::new(self.lower_block(
                    proto_index,
                    inner,
                    None,
                    continue_target,
                )?)),
                HirStmt::Unstructured(_) => {
                    return Err(AstLowerError::ResidualHir {
                        proto: proto_index,
                        kind: "unstructured stmt",
                    });
                }
            };
            stmts.push(stmt);
            index += 1;
        }

        Ok(AstBlock { stmts })
    }

    fn lower_generic_for_stmt(
        &mut self,
        proto_index: usize,
        generic_for: &HirGenericFor,
        iterator_override: Option<&[crate::hir::HirExpr]>,
        continue_target: Option<AstLabelId>,
    ) -> Result<AstStmt, AstLowerError> {
        let loop_continue = self.loop_continue_label_if_needed(&generic_for.body);
        let mut body = self.lower_block(
            proto_index,
            &generic_for.body,
            None,
            loop_continue.or(continue_target),
        )?;
        if let Some(label) = loop_continue {
            body.stmts
                .push(AstStmt::Label(Box::new(AstLabel { id: label })));
        }
        let iterator = iterator_override.unwrap_or(&generic_for.iterator);
        Ok(AstStmt::GenericFor(Box::new(AstGenericFor {
            bindings: generic_for
                .bindings
                .iter()
                .copied()
                .map(AstBindingRef::Local)
                .collect(),
            iterator: iterator
                .iter()
                .map(|expr| self.lower_expr(proto_index, expr))
                .collect::<Result<Vec<_>, _>>()?,
            body,
        })))
    }

    fn loop_continue_label_if_needed(&mut self, body: &HirBlock) -> Option<AstLabelId> {
        if self.target.caps.continue_stmt
            || !self.target.caps.goto_label
            || !block_has_continue(body)
        {
            None
        } else {
            let label = AstLabelId(self.next_synthetic_label);
            self.next_synthetic_label += 1;
            Some(label)
        }
    }

    fn lower_local_binding(
        &self,
        proto_index: usize,
        binding: crate::hir::LocalId,
        attr: AstLocalAttr,
    ) -> AstLocalBinding {
        let proto = &self.module.protos[proto_index];
        let origin = if proto
            .local_debug_hints
            .get(binding.index())
            .is_some_and(|hint| hint.is_some())
        {
            AstLocalOrigin::DebugHinted
        } else {
            AstLocalOrigin::Recovered
        };
        AstLocalBinding {
            id: AstBindingRef::Local(binding),
            attr,
            origin,
        }
    }

    fn recovered_local_binding(
        &self,
        binding: AstBindingRef,
        attr: AstLocalAttr,
    ) -> AstLocalBinding {
        AstLocalBinding {
            id: binding,
            attr,
            origin: AstLocalOrigin::Recovered,
        }
    }
}
