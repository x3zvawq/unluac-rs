//! HIR -> AST build 阶段入口。
//!
//! 这里调度合法语法模式与逐节点机械 lowering，依赖 HIR 已经完成控制结构、binding 和
//! value-pack 的语义恢复；前层退出要求也只读取 `HirProto::exit_requirements`，不会旁路访问
//! StructureFacts。这里不会通过相邻语句重组来补 HIR 丢失的多值或求值顺序事实，也不会把
//! 没有等价源码语义的残余 HIR 节点拆成表面合法的 AST。
//! LocalRootRelease 已由 HIR 证明只结束旧源码根，在此生成 local 清零，不回推 VM 覆写。
//! 单绑定闭包的引用自捕获必须生成 local function，使 binding 在初始化前可见；普通
//! `local f = function() ... end` 的 RHS 不在 f 的词法域内，不能留给可选 sugar 修正。

mod analysis;
mod exprs;
mod patterns;
mod proto_bodies;

use crate::decompile::{DecompileContext, DecompileError, DecompileState};
use crate::generate::GenerateMode;
use crate::hir::{
    HirBlock, HirClosureExpr, HirControlFlowFeature, HirExitRequirement, HirGenericFor,
    HirGlobalDecl, HirModule, HirStmt, TempId,
};

use self::analysis::block_has_continue;
use self::exprs::PackLoweringContext;
use super::common::{
    AstAssign, AstBindingRef, AstBlock, AstCallStmt, AstExpr, AstGenericFor, AstGlobalAttr,
    AstGlobalBinding, AstGlobalBindingTarget, AstGlobalDecl, AstGlobalName, AstGoto, AstIf,
    AstLValue, AstLabel, AstLabelId, AstLocalAttr, AstLocalBinding, AstLocalDecl,
    AstLocalFunctionDecl, AstLocalOrigin, AstModule, AstNameRef, AstNumericFor, AstRepeat,
    AstReturn, AstRewriteAuthority, AstStmt, AstTargetDialect, AstWhile,
};
use super::error::AstLowerError;

/// 对外的 AST lowering 入口。
pub fn lower_ast(
    module: &HirModule,
    target: AstTargetDialect,
    mode: GenerateMode,
) -> Result<AstModule, AstLowerError> {
    let exit_diagnostics = collect_exit_diagnostics(module, target);
    if mode == GenerateMode::Strict
        && let Some(diagnostic) = exit_diagnostics.first()
    {
        return Err(exit_diagnostic_error(*diagnostic, target.version));
    }
    let lowering_target = match mode {
        GenerateMode::Strict => target,
        GenerateMode::Permissive => AstTargetDialect::diagnostic_for_lowering(target.version),
    };
    let mut lowerer = AstLowerer::new(module, lowering_target, mode);
    let mut ast = lowerer.lower_module()?;
    if !exit_diagnostics.is_empty() {
        ast.body.stmts.insert(
            0,
            AstStmt::Error(format_exit_diagnostics(&exit_diagnostics)),
        );
    }
    Ok(ast)
}

/// 使用请求方言的真实语法能力执行 AST lowering。
///
pub(crate) fn lower_ast_for_generate(
    state: &mut DecompileState,
    context: &DecompileContext<'_>,
) -> Result<(), DecompileError> {
    let hir = state.require_hir()?;
    let ast = lower_ast(hir, context.requested_target, context.options.generate.mode)?;
    state.ast = Some(ast);
    Ok(())
}

fn exit_diagnostic_error(
    diagnostic: HirExitRequirement,
    dialect: crate::ast::DecompileDialect,
) -> AstLowerError {
    match diagnostic {
        HirExitRequirement::RequiredControlFlow { feature, .. } => {
            AstLowerError::UnsupportedFeature {
                dialect,
                feature: control_flow_feature_name(feature),
                context: "HIR exit diagnostics",
            }
        }
        HirExitRequirement::UnresolvedValue {
            source_proto,
            phi,
            block,
            register,
        } => AstLowerError::UnresolvedHirValue {
            proto: source_proto,
            phi,
            block,
            register,
        },
    }
}

fn collect_exit_diagnostics(
    module: &HirModule,
    target: AstTargetDialect,
) -> Vec<HirExitRequirement> {
    module
        .protos
        .iter()
        .flat_map(|proto| proto.exit_requirements.iter().copied())
        .filter(|requirement| match requirement {
            HirExitRequirement::RequiredControlFlow { feature, .. } => {
                !supports_control_flow_feature(target, *feature)
            }
            HirExitRequirement::UnresolvedValue { .. } => true,
        })
        .collect()
}

fn format_exit_diagnostics(diagnostics: &[HirExitRequirement]) -> String {
    let details = diagnostics
        .iter()
        .map(|diagnostic| match diagnostic {
            HirExitRequirement::RequiredControlFlow {
                source_proto,
                feature,
            } => format!(
                "proto#{source_proto} requires unavailable {}",
                control_flow_feature_name(*feature)
            ),
            HirExitRequirement::UnresolvedValue {
                source_proto,
                phi,
                block,
                register,
            } => {
                format!("proto#{source_proto} unresolved phi{phi} at #{block} register r{register}")
            }
        })
        .collect::<Vec<_>>()
        .join("; ");
    format!("HIR exit diagnostics: {details}")
}

const fn control_flow_feature_name(feature: HirControlFlowFeature) -> &'static str {
    match feature {
        HirControlFlowFeature::GotoLabel => "goto/label",
        HirControlFlowFeature::ContinueStatement => "continue",
    }
}

const fn supports_control_flow_feature(
    target: AstTargetDialect,
    feature: HirControlFlowFeature,
) -> bool {
    match feature {
        HirControlFlowFeature::GotoLabel => target.caps.goto_label,
        // AST can preserve `continue` either natively or with a loop-local goto/label pair.
        HirControlFlowFeature::ContinueStatement => {
            target.caps.continue_stmt || target.caps.goto_label
        }
    }
}

struct AstLowerer<'a> {
    module: &'a HirModule,
    target: AstTargetDialect,
    generate_mode: GenerateMode,
    next_synthetic_label: usize,
    proto_bodies: proto_bodies::ProtoBodies,
}

impl<'a> AstLowerer<'a> {
    fn new(module: &'a HirModule, target: AstTargetDialect, generate_mode: GenerateMode) -> Self {
        Self {
            module,
            target,
            generate_mode,
            next_synthetic_label: 0,
            proto_bodies: proto_bodies::ProtoBodies::default(),
        }
    }

    fn should_recover_errors(&self) -> bool {
        self.generate_mode == GenerateMode::Permissive
    }

    fn lower_module(&mut self) -> Result<AstModule, AstLowerError> {
        let entry = self.module.entry.index();
        if entry >= self.module.protos.len() {
            return Err(AstLowerError::MissingChildProto {
                proto: entry,
                child: entry,
            });
        }
        let (bodies, order) = proto_bodies::ProtoBodies::prepare(self.module);
        self.proto_bodies = bodies;
        for proto in order {
            let body = self.lower_proto_body(proto);
            self.proto_bodies.insert(proto, body);
        }
        let body = self.proto_bodies.take(entry)?;
        let module = AstModule {
            next_synthetic_local: 0,
            entry_function: self.module.entry,
            body,
        };
        super::capture_scope::verify_forward_local_captures(&module)?;
        Ok(module)
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
        let hoisted_temps = self.proto_bodies.take_hoisted_temps(proto_index);
        let mut body = self.lower_block(proto_index, &proto.body, Some(&hoisted_temps), None)?;
        if let Some(failure) = &proto.failure {
            if !self.should_recover_errors() {
                return Err(AstLowerError::ResidualHir {
                    proto: proto_index,
                    kind: "proto recovery failure",
                });
            }
            body.stmts.insert(0, AstStmt::Error(failure.diagnostic()));
            if !proto.detached_children.is_empty() {
                body.stmts.push(AstStmt::Error(format!(
                    "proto#{} failed before child closure placement and captures were recovered; direct child protos follow as detached diagnostic functions",
                    failure.proto,
                )));
            }
            for (binding, child) in &proto.detached_children {
                let function = self.lower_function_expr(
                    proto_index,
                    &HirClosureExpr {
                        source_site: None,
                        creation: None,
                        proto: *child,
                        captures: Vec::new(),
                    },
                )?;
                body.stmts.push(AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![self.detached_child_diagnostic_binding(*binding)],
                    values: vec![AstExpr::FunctionExpr(Box::new(function))],
                    initializer_merge_transaction: None,
                    initializer_root_profile: None,
                })));
            }
        }
        Ok(body)
    }

    fn lower_block(
        &mut self,
        proto_index: usize,
        block: &HirBlock,
        hoisted_temps: Option<&[TempId]>,
        continue_target: Option<AstLabelId>,
    ) -> Result<AstBlock, AstLowerError> {
        let mut stmts = Vec::new();
        if let Some(hoisted_temps) = hoisted_temps {
            let temp_bindings = hoisted_temps
                .iter()
                .map(|&temp| self.lower_temp_binding(proto_index, temp))
                .collect::<Vec<_>>();
            if !temp_bindings.is_empty() {
                stmts.push(AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: temp_bindings,
                    values: Vec::new(),
                    initializer_merge_transaction: None,
                    initializer_root_profile: None,
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
            self.try_lower_close_decl(proto_index, &block.stmts, index)?
        {
            return Ok((vec![stmt], consumed));
        }

        match &block.stmts[index] {
            HirStmt::LocalDecl(local_decl) => {
                let recursive = matches!(
                    (local_decl.bindings.as_slice(), local_decl.values.fixed.as_slice(), &local_decl.values.tail),
                    ([binding], [crate::hir::HirExpr::Closure(closure)], None)
                        if closure.captures.iter().any(|capture|
                            capture.binding == crate::hir::HirBinding::Local(*binding)
                                && capture.mode == crate::hir::HirCaptureMode::ByReference)
                );
                let mut lowered = self.lower_local_decl(proto_index, local_decl)?;
                let stmt = if recursive {
                    // 引用自捕获必须在初始化前进入词法域。这里是必需的源码语义，
                    // 不依赖可选 function-sugar，也不受 binding 的重写权限影响。
                    let binding = lowered.bindings.pop().expect("single recursive binding");
                    let AstExpr::FunctionExpr(function) =
                        lowered.values.pop().expect("recursive closure")
                    else {
                        unreachable!("HIR closure lowers to a function expression");
                    };
                    AstStmt::LocalFunctionDecl(Box::new(AstLocalFunctionDecl {
                        name: binding.id,
                        origin: binding.origin,
                        rewrite_authority: binding.rewrite_authority,
                        func: *function,
                    }))
                } else {
                    AstStmt::LocalDecl(Box::new(lowered))
                };
                Ok((vec![stmt], 1))
            }
            HirStmt::GlobalDecl(global_decl) => Ok((
                vec![AstStmt::GlobalDecl(Box::new(
                    self.lower_hir_global_decl(proto_index, global_decl)?,
                ))],
                1,
            )),
            HirStmt::Assign(assign) => Ok((self.lower_assign(proto_index, assign)?, 1)),
            HirStmt::LocalRootRelease(local) => Ok((
                vec![AstStmt::Assign(Box::new(AstAssign {
                    targets: vec![AstLValue::Name(AstNameRef::Local(*local))],
                    values: vec![AstExpr::Nil],
                    initializer_merge_transaction: None,
                    method_rewrite_transaction: None,
                }))],
                1,
            )),
            HirStmt::TableSetList(_) => Err(AstLowerError::ResidualHir {
                proto: proto_index,
                kind: "table-set-list",
            }),
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
                    values: self.lower_value_pack(
                        proto_index,
                        &ret.values,
                        PackLoweringContext::Ordinary,
                    )?,
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
                        lifetime: repeat_stmt.lifetime.clone(),
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
                vec![self.lower_generic_for_stmt(proto_index, generic_for, continue_target)?],
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
                vec![AstStmt::DoBlock(Box::new(self.lower_block(
                    proto_index,
                    inner,
                    None,
                    continue_target,
                )?))],
                1,
            )),
        }
    }

    fn lower_hir_global_decl(
        &mut self,
        proto_index: usize,
        global_decl: &HirGlobalDecl,
    ) -> Result<AstGlobalDecl, AstLowerError> {
        if !self.target.caps.global_decl {
            return Err(AstLowerError::UnsupportedFeature {
                dialect: self.target.version,
                feature: "global",
                context: "global declaration",
            });
        }
        let bindings = global_decl
            .names
            .iter()
            .map(|key| {
                let name = key
                    .as_utf8()
                    .filter(|name| self.target.version.is_identifier_name(name));
                name.map(|text| AstGlobalBinding {
                    target: AstGlobalBindingTarget::Name(AstGlobalName {
                        text: text.to_owned(),
                    }),
                    attr: AstGlobalAttr::None,
                })
                .ok_or_else(|| AstLowerError::InvalidGlobalDeclName {
                    proto: proto_index,
                    dialect: self.target.version,
                    name: key.debug_literal(),
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(AstGlobalDecl {
            bindings,
            values: self.lower_value_pack(
                proto_index,
                &global_decl.values,
                PackLoweringContext::TargetCounted(global_decl.names.len()),
            )?,
        })
    }

    fn lower_generic_for_stmt(
        &mut self,
        proto_index: usize,
        generic_for: &HirGenericFor,
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
        Ok(AstStmt::GenericFor(Box::new(AstGenericFor {
            bindings: generic_for
                .bindings
                .iter()
                .copied()
                .map(AstBindingRef::Local)
                .collect(),
            iterator: self.lower_value_pack(
                proto_index,
                &generic_for.iterator,
                PackLoweringContext::Ordinary,
            )?,
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
            let label = AstLabelId::Synthetic(self.next_synthetic_label);
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
        let debug_hinted = proto
            .local_debug_hints
            .get(binding.index())
            .is_some_and(|hint| hint.is_some());
        let physical_root = proto.physical_root_locals.contains(&binding);
        let origin = if debug_hinted && physical_root {
            AstLocalOrigin::DebugHintedPhysicalRoot
        } else if physical_root {
            AstLocalOrigin::PhysicalRoot
        } else if debug_hinted {
            AstLocalOrigin::DebugHinted
        } else {
            AstLocalOrigin::Recovered
        };
        AstLocalBinding {
            id: AstBindingRef::Local(binding),
            attr,
            origin,
            rewrite_authority: AstRewriteAuthority::Hir(
                proto.inline_dispositions.local(binding).clone(),
            ),
        }
    }

    fn lower_temp_binding(&self, proto_index: usize, temp: TempId) -> AstLocalBinding {
        let proto = &self.module.protos[proto_index];
        let debug_hinted = proto
            .temp_debug_locals
            .get(temp.index())
            .is_some_and(|hint| hint.is_some());
        let physical_root = proto.physical_root_temps.contains(&temp);
        let origin = if debug_hinted && physical_root {
            AstLocalOrigin::DebugHintedPhysicalRoot
        } else if physical_root {
            AstLocalOrigin::PhysicalRoot
        } else if debug_hinted {
            AstLocalOrigin::DebugHinted
        } else {
            AstLocalOrigin::Recovered
        };
        AstLocalBinding {
            id: AstBindingRef::Temp(temp),
            attr: AstLocalAttr::None,
            origin,
            rewrite_authority: AstRewriteAuthority::Hir(
                proto.inline_dispositions.temp(temp).clone(),
            ),
        }
    }

    /// 为失败 proto 的 detached child 构造仅用于诊断伪源码的 synthetic binding。
    ///
    /// 成功降低的 HIR binding 必须走 `lower_local_binding` / `lower_temp_binding`，
    /// 以免这里故意为空的 provenance 与 rewrite authority 覆盖前层结论。
    fn detached_child_diagnostic_binding(&self, binding: crate::hir::LocalId) -> AstLocalBinding {
        AstLocalBinding {
            id: AstBindingRef::Local(binding),
            attr: AstLocalAttr::None,
            origin: AstLocalOrigin::Recovered,
            rewrite_authority: AstRewriteAuthority::Hir(Default::default()),
        }
    }
}
