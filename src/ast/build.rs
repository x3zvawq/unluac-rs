//! HIR -> AST build 阶段入口。

mod analysis;
mod exprs;
mod patterns;

use std::collections::BTreeSet;

use crate::generate::GenerateMode;
use crate::hir::{HirBlock, HirGenericFor, HirModule, HirStmt, TempId};

use self::analysis::{
    block_has_continue, collect_close_temps, collect_referenced_temps_in_encounter_order,
    max_hir_label_id,
};
use super::common::{
    AstAssign, AstBindingRef, AstBlock, AstCallStmt, AstExpr, AstGenericFor, AstGoto, AstIf,
    AstIndexAccess, AstLabel, AstLabelId, AstLocalAttr, AstLocalBinding, AstLocalDecl,
    AstLocalOrigin, AstModule, AstNumericFor, AstRepeat, AstReturn, AstStmt, AstTargetDialect,
    AstWhile,
};
use super::error::AstLowerError;

/// 对外的 AST lowering 入口。
///
/// `generate_mode` 控制错误恢复行为：`Strict` 下任何 lowering 错误都直接上抛，
/// 非严格模式下会把无法恢复的语句/表达式替换为 `AstStmt::Error` / `AstExpr::Error`
/// 占位节点，最终在 Generate 阶段输出为 Lua 注释。
pub fn lower_ast(
    module: &HirModule,
    target: AstTargetDialect,
    generate_mode: GenerateMode,
) -> Result<AstModule, AstLowerError> {
    let mut lowerer = AstLowerer::new(module, target, generate_mode);
    lowerer.lower_module()
}

struct AstLowerer<'a> {
    module: &'a HirModule,
    target: AstTargetDialect,
    generate_mode: GenerateMode,
    next_synthetic_label: usize,
}

impl<'a> AstLowerer<'a> {
    fn new(module: &'a HirModule, target: AstTargetDialect, generate_mode: GenerateMode) -> Self {
        Self {
            module,
            target,
            generate_mode,
            next_synthetic_label: max_hir_label_id(module) + 1,
        }
    }

    /// 仅 Permissive 模式允许用 Error 占位节点替代失败的 lowering；
    /// Strict 和 BestEffort 都会直接传播错误。
    fn should_recover_errors(&self) -> bool {
        self.generate_mode == GenerateMode::Permissive
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
        let mut stmts = Vec::new();
        if let Some(close_temps) = root_close_temps {
            let temp_bindings = collect_referenced_temps_in_encounter_order(block)
                .into_iter()
                .filter(|temp| !close_temps.contains(temp))
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
            match self.lower_stmts_at(proto_index, block, index, continue_target) {
                Ok((new_stmts, consumed)) => {
                    stmts.extend(new_stmts);
                    index += consumed;
                }
                Err(err) if self.should_recover_errors() => {
                    stmts.push(AstStmt::Error(err.to_string()));
                    index += 1;
                }
                Err(err) => return Err(err),
            }
        }

        Ok(AstBlock { stmts })
    }

    /// 尝试对 `index` 位置起始的语句（们）进行 lowering。
    ///
    /// 返回 `(产出的 AstStmt 列表, 消耗的 HIR 语句数量)`。
    fn lower_stmts_at(
        &mut self,
        proto_index: usize,
        block: &HirBlock,
        index: usize,
        continue_target: Option<AstLabelId>,
    ) -> Result<(Vec<AstStmt>, usize), AstLowerError> {
        if let Some((stmt, consumed)) =
            self.try_lower_global_decl(proto_index, &block.stmts, index)?
        {
            return Ok((vec![stmt], consumed));
        }

        if let Some((stmt, consumed)) =
            self.try_lower_local_close_decl(proto_index, &block.stmts, index)?
        {
            return Ok((vec![stmt], consumed));
        }

        if let Some((stmt, consumed)) =
            self.try_lower_generic_for_init(proto_index, &block.stmts, index, continue_target)?
        {
            return Ok((vec![stmt], consumed));
        }

        if let Some((stmt, consumed)) =
            self.try_lower_forwarded_multiret_call_stmt(proto_index, &block.stmts, index)?
        {
            return Ok((vec![stmt], consumed));
        }

        if let Some((stmt, consumed)) =
            self.try_lower_single_value_final_call_arg_stmt(proto_index, &block.stmts, index)?
        {
            return Ok((vec![stmt], consumed));
        }

        if let Some((stmt, consumed)) =
            self.try_lower_temp_close_decl(proto_index, &block.stmts, index)?
        {
            return Ok((vec![stmt], consumed));
        }

        match &block.stmts[index] {
            HirStmt::LocalDecl(local_decl) => Ok((
                vec![AstStmt::LocalDecl(Box::new(
                    self.lower_local_decl(proto_index, local_decl)?,
                ))],
                1,
            )),
            HirStmt::Assign(assign) => Ok((
                vec![AstStmt::Assign(Box::new(
                    self.lower_assign(proto_index, assign)?,
                ))],
                1,
            )),
            HirStmt::TableSetList(set_list) => {
                if set_list.trailing_multivalue.is_some() {
                    return Err(AstLowerError::UnsupportedSetListTrailingMultivalue {
                        proto: proto_index,
                    });
                }
                let base = self.lower_expr(proto_index, &set_list.base)?;
                let stmts = set_list
                    .values
                    .iter()
                    .enumerate()
                    .map(|(offset, value)| {
                        let index_value =
                            AstExpr::Integer(i64::from(set_list.start_index) + offset as i64);
                        let target =
                            super::common::AstLValue::IndexAccess(Box::new(AstIndexAccess {
                                base: base.clone(),
                                index: index_value,
                            }));
                        Ok(AstStmt::Assign(Box::new(AstAssign {
                            targets: vec![target],
                            values: vec![self.lower_expr(proto_index, value)?],
                        })))
                    })
                    .collect::<Result<Vec<_>, AstLowerError>>()?;
                Ok((stmts, 1))
            }
            HirStmt::ErrNil(_) => {
                Err(AstLowerError::InvalidGlobalDeclPattern { proto: proto_index })
            }
            HirStmt::ToBeClosed(_) => Err(AstLowerError::InvalidToBeClosed {
                proto: proto_index,
                reason: "standalone to-be-closed has no attachable declaration",
            }),
            HirStmt::Close(_) => Err(AstLowerError::UnsupportedClose { proto: proto_index }),
            HirStmt::CallStmt(call_stmt) => Ok((
                vec![AstStmt::CallStmt(Box::new(AstCallStmt {
                    call: self.lower_call(proto_index, &call_stmt.call)?,
                }))],
                1,
            )),
            HirStmt::Return(ret) => Ok((
                vec![AstStmt::Return(Box::new(AstReturn {
                    values: ret
                        .values
                        .iter()
                        .map(|value| self.lower_expr(proto_index, value))
                        .collect::<Result<Vec<_>, _>>()?,
                }))],
                1,
            )),
            HirStmt::If(if_stmt) => Ok((
                vec![AstStmt::If(Box::new(AstIf {
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
                }))],
                1,
            )),
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
                Ok((
                    vec![AstStmt::While(Box::new(AstWhile {
                        cond: self.lower_expr(proto_index, &while_stmt.cond)?,
                        body,
                    }))],
                    1,
                ))
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
                Ok((
                    vec![AstStmt::Repeat(Box::new(AstRepeat {
                        body,
                        cond: self.lower_expr(proto_index, &repeat_stmt.cond)?,
                    }))],
                    1,
                ))
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
                Ok((
                    vec![AstStmt::NumericFor(Box::new(AstNumericFor {
                        binding: AstBindingRef::Local(numeric_for.binding),
                        start: self.lower_expr(proto_index, &numeric_for.start)?,
                        limit: self.lower_expr(proto_index, &numeric_for.limit)?,
                        step: self.lower_expr(proto_index, &numeric_for.step)?,
                        body,
                    }))],
                    1,
                ))
            }
            HirStmt::GenericFor(generic_for) => Ok((
                vec![self.lower_generic_for_stmt(
                    proto_index,
                    generic_for,
                    None,
                    continue_target,
                )?],
                1,
            )),
            HirStmt::Break => Ok((vec![AstStmt::Break], 1)),
            HirStmt::Continue => {
                if self.target.caps.continue_stmt {
                    Ok((vec![AstStmt::Continue], 1))
                } else if let Some(label) = continue_target {
                    if !self.target.caps.goto_label {
                        return Err(AstLowerError::UnsupportedFeature {
                            dialect: self.target.version,
                            feature: "continue",
                            context: "continue statement",
                        });
                    }
                    Ok((vec![AstStmt::Goto(Box::new(AstGoto { target: label }))], 1))
                } else {
                    Err(AstLowerError::UnsupportedFeature {
                        dialect: self.target.version,
                        feature: "continue",
                        context: "continue statement",
                    })
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
                Ok((
                    vec![AstStmt::Goto(Box::new(AstGoto {
                        target: goto_stmt.target.into(),
                    }))],
                    1,
                ))
            }
            HirStmt::Label(label) => {
                if !self.target.caps.goto_label {
                    return Err(AstLowerError::UnsupportedFeature {
                        dialect: self.target.version,
                        feature: "label",
                        context: "label statement",
                    });
                }
                Ok((
                    vec![AstStmt::Label(Box::new(AstLabel {
                        id: label.id.into(),
                    }))],
                    1,
                ))
            }
            HirStmt::Block(inner) => Ok((
                vec![AstStmt::DoBlock(Box::new(
                    self.lower_block(proto_index, inner, None, continue_target)?,
                ))],
                1,
            )),
            HirStmt::Unstructured(_) => Err(AstLowerError::ResidualHir {
                proto: proto_index,
                kind: "unstructured stmt",
            }),
        }
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
