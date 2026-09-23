//! 将 HIR 表达式、左值和 value pack 降低为合法目标 AST。
//!
//! 消费 HIR 已分开的标量/pack tail、capture 及构造器分配事实，负责语法选择，
//! 不从 Call/VarArg 外形补多值语义，也不重建闭包根证明。
//! 例如可能暴露额外返回值的固定尾调用用 SingleValue 保持宽度，open tail 保持展开；
//! record key 则按目标方言选择命名字段或显式索引语法。

use std::collections::BTreeSet;

use crate::hir::{
    HirAssign, HirBinaryOpKind, HirCallExpr, HirCaptureMode, HirClosureExpr, HirExpr, HirLValue,
    HirLocalDecl, HirTableAccess, HirTableField, HirUnaryOpKind, HirValuePack, UpvalueId,
    initializer_root_profile,
};

use super::{AstLowerError, AstLowerer};
use crate::ast::DecompileDialect;
use crate::ast::common::{
    AstAssign, AstBinaryExpr, AstBinaryOpKind, AstCallExpr, AstCallKind, AstExpr, AstFieldAccess,
    AstFunctionExpr, AstGlobalName, AstIndexAccess, AstLValue, AstLocalDecl, AstLogicalExpr,
    AstMethodCallExpr, AstNameRef, AstStmt, AstTableConstructor, AstTableField, AstTableKey,
    AstUnaryExpr, AstUnaryOpKind,
};

impl<'a> AstLowerer<'a> {
    fn lower_native_if_expr(
        &mut self,
        proto: usize,
        decision: &crate::hir::HirDecisionExpr,
    ) -> Result<AstExpr, AstLowerError> {
        use crate::hir::HirDecisionTarget;
        let topology = crate::hir::decision::analyze_decision(decision);
        if topology.has_shared_nodes() {
            return Err(AstLowerError::ResidualHir {
                proto,
                kind: "shared native if expression",
            });
        }
        let mut values = vec![None; decision.nodes.len()];
        for node in topology.topological_nodes().rev() {
            let mut arm = |target: &HirDecisionTarget| -> Result<AstExpr, AstLowerError> {
                match target {
                    HirDecisionTarget::Expr(expr) => self.lower_expr(proto, expr),
                    HirDecisionTarget::Node(next) => Ok(values[next.index()]
                        .take()
                        .expect("native if child is built once before its parent")),
                    HirDecisionTarget::CurrentValue => Err(AstLowerError::ResidualHir {
                        proto,
                        kind: "native if reuses its condition value",
                    }),
                }
            };
            let then_expr = arm(&node.truthy)?;
            let else_expr = arm(&node.falsy)?;
            values[node.id.index()] = Some(AstExpr::IfExpr(Box::new(crate::ast::AstIfExpr {
                cond: self.lower_expr(proto, &node.test)?,
                then_expr,
                else_expr,
            })));
        }
        Ok(values[decision.entry.index()]
            .take()
            .expect("native if has an entry"))
    }

    pub(super) fn lower_value_pack(
        &mut self,
        proto_index: usize,
        pack: &HirValuePack,
        context: PackLoweringContext,
    ) -> Result<Vec<AstExpr>, AstLowerError> {
        let mut values = pack
            .fixed
            .iter()
            .map(|value| self.lower_expr(proto_index, value))
            .collect::<Result<Vec<_>, _>>()?;

        if let Some(tail) = &pack.tail {
            if let Some(exact_width) = tail.exact_width() {
                let PackLoweringContext::TargetCounted(target_count) = context else {
                    return Err(AstLowerError::ResidualHir {
                        proto: proto_index,
                        kind: "exact-width pack tail outside target-counted value list",
                    });
                };
                if target_count > pack.fixed.len().saturating_add(exact_width) {
                    return Err(AstLowerError::ResidualHir {
                        proto: proto_index,
                        kind: "exact-width pack tail cannot fill target-counted value list",
                    });
                }
            }
            values.push(self.lower_expr(proto_index, tail.as_expr())?);
        } else if matches!(pack.fixed.last(), Some(HirExpr::Call(_) | HirExpr::VarArg))
            && match context {
                PackLoweringContext::Ordinary => true,
                PackLoweringContext::TargetCounted(target_count) => target_count > pack.fixed.len(),
            }
        {
            let last = values
                .last_mut()
                .expect("non-empty fixed pack must lower to a final AST value");
            let value = std::mem::replace(last, AstExpr::Nil);
            *last = AstExpr::SingleValue(Box::new(value));
        }

        Ok(values)
    }

    pub(super) fn lower_function_expr(
        &mut self,
        owner_proto: usize,
        closure: &HirClosureExpr,
    ) -> Result<AstFunctionExpr, AstLowerError> {
        let child = self.module.protos.get(closure.proto.index()).ok_or(
            AstLowerError::MissingChildProto {
                proto: owner_proto,
                child: closure.proto.index(),
            },
        )?;
        let body = self.proto_bodies.take(closure.proto.index())?;
        let named_vararg =
            if child.signature.has_vararg_param_reg && !child.signature.legacy_arg_slot {
                let local =
                    child
                        .vararg_param_local
                        .ok_or(AstLowerError::MissingNamedVarargBinding {
                            proto: closure.proto.index(),
                        })?;
                self.proto_bodies
                    .named_vararg_is_referenced(closure.proto.index())
                    .then_some(crate::ast::common::AstBindingRef::Local(local))
            } else {
                None
            };
        let mut captured_bindings = BTreeSet::new();
        let mut captured_params = BTreeSet::new();
        let mut capture_write_names = BTreeSet::new();
        for (capture_index, capture) in closure.captures.iter().enumerate() {
            let name = self.lower_capture_name(owner_proto, capture.binding)?;
            match capture.binding {
                crate::hir::HirBinding::Param(param) => {
                    captured_params.insert(param);
                }
                crate::hir::HirBinding::Local(local) => {
                    captured_bindings.insert(crate::ast::common::AstBindingRef::Local(local));
                }
                crate::hir::HirBinding::Temp(temp) => {
                    captured_bindings.insert(crate::ast::common::AstBindingRef::Temp(temp));
                }
                crate::hir::HirBinding::Upvalue(_) => {}
            }
            if capture.mode == HirCaptureMode::ByReference
                && child.mutable_upvalues.contains(&UpvalueId(capture_index))
            {
                capture_write_names.insert(name);
            }
        }
        Ok(AstFunctionExpr {
            creation: closure.creation,
            function: closure.proto,
            params: child.params.clone(),
            allows_self_param: !child.params.is_empty()
                && child
                    .param_debug_hints
                    .first()
                    .and_then(Option::as_deref)
                    .is_none_or(|name| name == "self")
                && child
                    .upvalues
                    .iter()
                    .all(|upvalue| child.environment_upvalues.contains(upvalue)),
            is_vararg: child.signature.is_vararg,
            named_vararg,
            body,
            captured_bindings,
            captured_params,
            capture_write_names,
        })
    }

    pub(super) fn lower_local_decl(
        &mut self,
        proto_index: usize,
        local_decl: &HirLocalDecl,
    ) -> Result<AstLocalDecl, AstLowerError> {
        let initializer_root_profile = initializer_root_profile(
            self.target.version,
            &local_decl.values,
            local_decl.bindings.len(),
        );
        Ok(AstLocalDecl {
            bindings: local_decl
                .bindings
                .iter()
                .copied()
                .map(|binding| {
                    self.lower_local_binding(proto_index, binding, crate::ast::AstLocalAttr::None)
                })
                .collect(),
            values: self.lower_value_pack(
                proto_index,
                &local_decl.values,
                PackLoweringContext::TargetCounted(local_decl.bindings.len()),
            )?,
            initializer_merge_transaction: local_decl.initializer_merge_transaction,
            initializer_root_profile: Some(initializer_root_profile),
        })
    }

    pub(super) fn lower_assign(
        &mut self,
        proto_index: usize,
        assign: &HirAssign,
    ) -> Result<Vec<AstStmt>, AstLowerError> {
        let preserve_parallel_nil = assign.preserves_parallel_nil();
        let assign = AstAssign {
            targets: assign
                .targets
                .iter()
                .map(|target| self.lower_lvalue(proto_index, target))
                .collect::<Result<Vec<_>, _>>()?,
            values: self.lower_value_pack(
                proto_index,
                &assign.values,
                PackLoweringContext::TargetCounted(assign.targets.len()),
            )?,
            initializer_merge_transaction: assign.initializer_merge_transaction,
            luau_compound_global: assign.luau_compound_global,
            method_rewrite_transaction: assign.method_rewrite_transaction,
        };
        if assign.luau_compound_global {
            if self.target.version != DecompileDialect::Luau {
                return Err(AstLowerError::UnsupportedFeature {
                    dialect: self.target.version,
                    feature: "compound assignment",
                    context: "HIR assignment frame",
                });
            }
            if assign.compound_global_binary().is_none() {
                return Err(AstLowerError::ResidualHir {
                    proto: proto_index,
                    kind: "invalid compound assignment frame",
                });
            }
        }
        if !preserve_parallel_nil
            && assign.targets.len() > 1
            && assign.targets.len() == assign.values.len()
            && assign
                .values
                .iter()
                .all(|value| matches!(value, AstExpr::Nil))
            && assign.targets.iter().all(|target| {
                matches!(
                    target,
                    AstLValue::Name(
                        AstNameRef::Param(_) | AstNameRef::Local(_) | AstNameRef::Temp(_)
                    )
                )
            })
            && assign.initializer_merge_transaction.is_none()
            && assign.method_rewrite_transaction.is_none()
        {
            // 原范围清零没有并列 RHS 准备；HIR 已验证的完整赋值帧必须保留。
            // HIR 保留范围清零的共同覆盖端点；源码多值赋值却为整组 RHS 预留临时寄存器，
            // 128 个活跃 local 再接 128 个 nil 就不可重编译。标量本地清零直接写原槽，
            // 没有 RHS 读取、地址求值或 GC 观察点，不改变 binding/capture 的身份与释放点。
            return Ok(assign
                .targets
                .into_iter()
                .map(|target| {
                    AstStmt::Assign(Box::new(AstAssign {
                        targets: vec![target],
                        values: vec![AstExpr::Nil],
                        initializer_merge_transaction: None,
                        luau_compound_global: false,
                        method_rewrite_transaction: None,
                    }))
                })
                .collect());
        }
        Ok(vec![AstStmt::Assign(Box::new(assign))])
    }

    pub(super) fn lower_lvalue(
        &mut self,
        proto_index: usize,
        target: &HirLValue,
    ) -> Result<AstLValue, AstLowerError> {
        Ok(match target {
            HirLValue::Param(param) => AstLValue::Name(AstNameRef::Param(*param)),
            HirLValue::Temp(temp) => AstLValue::Name(AstNameRef::Temp(*temp)),
            HirLValue::Local(local) => AstLValue::Name(AstNameRef::Local(*local)),
            HirLValue::Upvalue(upvalue) => {
                AstLValue::Name(self.lower_upvalue_name(proto_index, *upvalue)?)
            }
            HirLValue::Global(global) => {
                lower_global_lvalue(proto_index, &global.key, self.target.version)?
            }
            HirLValue::TableAccess(access) => lower_access_expr(
                proto_index,
                access,
                self,
                |field| AstLValue::FieldAccess(Box::new(field)),
                |index| AstLValue::IndexAccess(Box::new(index)),
            )?,
        })
    }

    pub(super) fn lower_expr(
        &mut self,
        proto_index: usize,
        expr: &HirExpr,
    ) -> Result<AstExpr, AstLowerError> {
        Ok(match expr {
            HirExpr::Nil => AstExpr::Nil,
            HirExpr::Boolean(value) => AstExpr::Boolean(*value),
            HirExpr::Integer(value) => AstExpr::Integer(*value),
            HirExpr::Number(value) => AstExpr::Number(*value),
            HirExpr::String(value) => AstExpr::String(value.clone()),
            HirExpr::Int64(value) => AstExpr::Int64(*value),
            HirExpr::UInt64(value) => AstExpr::UInt64(*value),
            HirExpr::Complex { real, imag } => AstExpr::Complex {
                real: *real,
                imag: *imag,
            },
            HirExpr::Vector(vector) => AstExpr::Vector(*vector),
            HirExpr::ParamRef(param) => AstExpr::Var(AstNameRef::Param(*param)),
            HirExpr::LocalRef(local) => AstExpr::Var(AstNameRef::Local(*local)),
            HirExpr::UpvalueRef(upvalue) => {
                AstExpr::Var(self.lower_upvalue_name(proto_index, *upvalue)?)
            }
            HirExpr::TempRef(temp) => AstExpr::Var(AstNameRef::Temp(*temp)),
            HirExpr::GlobalRef(global) => {
                lower_global_expr(proto_index, &global.key, self.target.version)?
            }
            HirExpr::TableAccess(access) => lower_access_expr(
                proto_index,
                access,
                self,
                |field| AstExpr::FieldAccess(Box::new(field)),
                |index| AstExpr::IndexAccess(Box::new(index)),
            )?,
            HirExpr::Unary(_) | HirExpr::Binary(_) => {
                self.lower_operator_expr(proto_index, expr)?
            }
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical)
                if logical.preserves_boolean_prewrite =>
            {
                let value = Box::new(AstLogicalExpr {
                    lhs: self.lower_expr(proto_index, &logical.lhs)?,
                    rhs: self.lower_expr(proto_index, &logical.rhs)?,
                    preserves_boolean_prewrite: true,
                });
                if matches!(expr, HirExpr::LogicalAnd(_)) {
                    AstExpr::LogicalAnd(value)
                } else {
                    AstExpr::LogicalOr(value)
                }
            }
            HirExpr::LogicalAnd(_) => {
                self.lower_logical_chain(proto_index, expr, LogicalKind::And)?
            }
            HirExpr::LogicalOr(_) => {
                self.lower_logical_chain(proto_index, expr, LogicalKind::Or)?
            }
            HirExpr::Decision(decision)
                if decision.emit_as_luau_if && self.target.version == DecompileDialect::Luau =>
            {
                self.lower_native_if_expr(proto_index, decision)?
            }
            HirExpr::Decision(_) => {
                if !self.should_recover_errors() {
                    return Err(AstLowerError::ResidualHir {
                        proto: proto_index,
                        kind: "decision expr",
                    });
                }
                AstExpr::Error(
                    AstLowerError::ResidualHir {
                        proto: proto_index,
                        kind: "decision expr",
                    }
                    .to_string(),
                )
            }
            HirExpr::Call(call) => match self.lower_call(proto_index, call)? {
                AstCallKind::Call(call) => AstExpr::Call(call),
                AstCallKind::MethodCall(call) => AstExpr::MethodCall(call),
            },
            HirExpr::CaptureInitializer(value) => {
                if self.target.version != crate::decompile::DecompileDialect::Luau
                    || (matches!(value, crate::hir::HirCaptureInitializer::FirstVararg(_))
                        && !self.module.protos[proto_index].signature.is_vararg)
                {
                    return Err(AstLowerError::InvalidCaptureInitializer { proto: proto_index });
                }
                AstExpr::CaptureInitializer(*value)
            }
            HirExpr::VarArg => AstExpr::VarArg,
            HirExpr::TableConstructor(table) => {
                let mut fields = table
                    .fields
                    .iter()
                    .map(|field| match field {
                        HirTableField::Array(value) => {
                            Ok(AstTableField::Array(self.lower_expr(proto_index, value)?))
                        }
                        HirTableField::Record(record) => {
                            Ok(AstTableField::Record(crate::ast::common::AstRecordField {
                                key: if table.allocation.permits_named_record_keys()
                                    && let Some(name) =
                                        field_name_from_key(&record.key, self.target.version)
                                {
                                    AstTableKey::Name(name)
                                } else {
                                    AstTableKey::Expr(self.lower_expr(proto_index, &record.key)?)
                                },
                                value: self.lower_expr(proto_index, &record.value)?,
                            }))
                        }
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                if let Some(trailing) = &table.trailing_multivalue {
                    if trailing.exact_width().is_some() {
                        return Err(AstLowerError::ResidualHir {
                            proto: proto_index,
                            kind: "exact-width pack tail in table constructor",
                        });
                    }
                    // AST 不需要再区分“尾部多返回”这个语义槽位；
                    // 只要把它保留成最后一个数组字段，Lua 语法自身就会在运行时
                    // 按表构造器上下文处理多返回展开。
                    fields.push(AstTableField::Array(
                        self.lower_expr(proto_index, trailing.as_expr())?,
                    ));
                } else if matches!(
                    table.fields.last(),
                    Some(HirTableField::Array(HirExpr::Call(_) | HirExpr::VarArg))
                ) {
                    let Some(AstTableField::Array(last)) = fields.last_mut() else {
                        unreachable!("HIR and AST table fields must preserve their order and kind");
                    };
                    let value = std::mem::replace(last, AstExpr::Nil);
                    *last = AstExpr::SingleValue(Box::new(value));
                }
                AstExpr::TableConstructor(Box::new(AstTableConstructor {
                    fields,
                    allocation: table.allocation.clone(),
                }))
            }
            HirExpr::Closure(closure) => {
                AstExpr::FunctionExpr(Box::new(self.lower_function_expr(proto_index, closure)?))
            }
            HirExpr::Unresolved(unresolved) => {
                if !self.should_recover_errors() {
                    return Err(AstLowerError::ResidualHir {
                        proto: proto_index,
                        kind: "unresolved expr",
                    });
                }
                AstExpr::Error(format!("unresolved HIR expression: {}", unresolved.summary))
            }
        })
    }

    /// 运算节点按原来的左到右顺序降低，叶子仍使用相同 lowering 和错误路径。
    /// 显式后序栈避免深链耗尽调用栈；不能重结合算术树，否则会改变浮点或元方法结果。
    fn lower_operator_expr(
        &mut self,
        proto_index: usize,
        expr: &HirExpr,
    ) -> Result<AstExpr, AstLowerError> {
        enum Step<'hir> {
            Expr(&'hir HirExpr),
            Unary(AstUnaryOpKind, bool),
            Binary(AstBinaryOpKind, bool),
        }

        let mut pending = vec![Step::Expr(expr)];
        let mut values = Vec::new();
        while let Some(step) = pending.pop() {
            match step {
                Step::Expr(HirExpr::Unary(unary)) => {
                    pending.push(Step::Unary(
                        lower_unary_op(unary.op),
                        unary.source_site.is_some(),
                    ));
                    pending.push(Step::Expr(&unary.expr));
                }
                Step::Expr(HirExpr::Binary(binary)) => {
                    pending.push(Step::Binary(
                        lower_binary_op(binary.op),
                        binary.source_site.is_some(),
                    ));
                    pending.push(Step::Expr(&binary.rhs));
                    pending.push(Step::Expr(&binary.lhs));
                }
                Step::Expr(leaf) => values.push(self.lower_expr(proto_index, leaf)?),
                Step::Unary(op, original_operation) => {
                    let expr = values
                        .pop()
                        .expect("unary operand is lowered before its node");
                    values.push(AstExpr::Unary(Box::new(AstUnaryExpr {
                        op,
                        expr,
                        original_operation,
                    })));
                }
                Step::Binary(op, original_operation) => {
                    let rhs = values.pop().expect("binary rhs is lowered before its node");
                    let lhs = values.pop().expect("binary lhs is lowered before its node");
                    values.push(AstExpr::Binary(Box::new(AstBinaryExpr {
                        op,
                        lhs,
                        rhs,
                        original_operation,
                    })));
                }
            }
        }
        Ok(values.pop().expect("operator tree has one lowered root"))
    }

    /// 同类逻辑运算保持 operand 次序时可安全重结合；先迭代展平再平衡，避免长链把
    /// build 及后续 AST visitor 的调用栈变成 O(n)。
    fn lower_logical_chain(
        &mut self,
        proto_index: usize,
        root: &HirExpr,
        kind: LogicalKind,
    ) -> Result<AstExpr, AstLowerError> {
        let mut pending = vec![root];
        let mut operands = Vec::new();
        while let Some(expr) = pending.pop() {
            let logical = match (kind, expr) {
                (LogicalKind::And, HirExpr::LogicalAnd(logical))
                | (LogicalKind::Or, HirExpr::LogicalOr(logical))
                    if !logical.preserves_boolean_prewrite =>
                {
                    logical
                }
                _ => {
                    operands.push(self.lower_expr(proto_index, expr)?);
                    continue;
                }
            };
            pending.push(&logical.rhs);
            pending.push(&logical.lhs);
        }

        let len = operands.len();
        let mut operands = operands.into_iter();
        Ok(build_balanced_logical_expr(kind, &mut operands, len))
    }

    pub(super) fn lower_call(
        &mut self,
        proto_index: usize,
        call: &HirCallExpr,
    ) -> Result<AstCallKind, AstLowerError> {
        let method_name = call
            .method_receiver()
            .and_then(|(_, method_key)| identifier_from_lua_key(method_key, self.target.version))
            .or_else(|| {
                if !call.plain_method_syntax {
                    return None;
                }
                let HirExpr::TableAccess(access) = &call.callee else {
                    return None;
                };
                let HirExpr::String(key) = &access.key else {
                    return None;
                };
                (call.args.first() == Some(&access.base))
                    .then(|| identifier_from_lua_key(key, self.target.version))
                    .flatten()
            });
        if call.method == crate::hir::HirMethodCall::Implicit && method_name.is_none() {
            return Err(AstLowerError::InvalidMethodCallPattern {
                proto: proto_index,
                reason: "implicit receiver requires a paired method field valid in the target dialect",
            });
        }
        let mut args =
            self.lower_value_pack(proto_index, &call.args, PackLoweringContext::Ordinary)?;
        // HIR 已证明并消费原比较前的 Boolean 写。Luau 裸比较只在分支后写结果，
        // 合取 true / 析取 false 分别重发 false / true 预写；这里不再推断原槽。
        for &(index, initial_value) in &call.boolean_prewrite_arguments {
            let lhs = std::mem::replace(&mut args[index], AstExpr::Nil);
            let logical = Box::new(AstLogicalExpr {
                lhs,
                rhs: AstExpr::Boolean(!initial_value),
                preserves_boolean_prewrite: true,
            });
            args[index] = if initial_value {
                AstExpr::LogicalOr(logical)
            } else {
                AstExpr::LogicalAnd(logical)
            };
        }

        if let Some(method_name) = method_name {
            if call.method == crate::hir::HirMethodCall::Implicit {
                let (receiver, _) = call.method_receiver().expect("validated method receiver");
                return Ok(AstCallKind::MethodCall(Box::new(AstMethodCallExpr {
                    receiver: self.lower_expr(proto_index, receiver)?,
                    method: method_name,
                    args,
                })));
            }
            if args.is_empty() {
                return Err(AstLowerError::InvalidMethodCallPattern {
                    proto: proto_index,
                    reason: "method call must keep the implicit receiver as its first argument",
                });
            }
            let receiver = args.remove(0);
            return Ok(AstCallKind::MethodCall(Box::new(AstMethodCallExpr {
                receiver,
                method: method_name,
                args,
            })));
        }

        let callee = self.lower_expr(proto_index, &call.callee)?;

        if call.is_method() && call.method_key.is_none() {
            if args.is_empty() {
                return Err(AstLowerError::InvalidMethodCallPattern {
                    proto: proto_index,
                    reason: "method call must keep the implicit receiver as its first argument",
                });
            }
            if matches!(&callee, AstExpr::FieldAccess(access) if args.first() == Some(&access.base))
            {
                let AstExpr::FieldAccess(access) = callee else {
                    unreachable!("method fallback candidate must remain a field access");
                };
                args.remove(0);
                return Ok(AstCallKind::MethodCall(Box::new(AstMethodCallExpr {
                    receiver: access.base,
                    method: access.field,
                    args,
                })));
            }
        }

        Ok(AstCallKind::Call(Box::new(AstCallExpr {
            required_luau_inlining: call.required_luau_inlining,
            callee,
            args,
            method_key: call.method_key.clone(),
            callee_root_handoff: call.callee_root_handoff,
            method_rewrite_transaction: call.method_rewrite_transaction,
        })))
    }

    fn lower_upvalue_name(
        &self,
        proto_index: usize,
        upvalue: UpvalueId,
    ) -> Result<AstNameRef, AstLowerError> {
        let proto = &self.module.protos[proto_index];
        if !proto.environment_upvalues.contains(&upvalue) {
            return Ok(AstNameRef::Upvalue(upvalue));
        }
        if !dialect_has_lexical_environment(self.target.version) {
            return Err(AstLowerError::UnsupportedFeature {
                dialect: self.target.version,
                feature: "lexical environment",
                context: "HIR environment upvalue",
            });
        }
        Ok(AstNameRef::Environment)
    }

    fn lower_capture_name(
        &self,
        owner_proto: usize,
        binding: crate::hir::HirBinding,
    ) -> Result<AstNameRef, AstLowerError> {
        use crate::hir::HirBinding;
        Ok(match binding {
            HirBinding::Param(param) => AstNameRef::Param(param),
            HirBinding::Local(local) => AstNameRef::Local(local),
            HirBinding::Temp(temp) => AstNameRef::Temp(temp),
            HirBinding::Upvalue(upvalue) => self.lower_upvalue_name(owner_proto, upvalue)?,
        })
    }
}

#[derive(Clone, Copy)]
enum LogicalKind {
    And,
    Or,
}

fn build_balanced_logical_expr(
    kind: LogicalKind,
    operands: &mut std::vec::IntoIter<AstExpr>,
    len: usize,
) -> AstExpr {
    match len {
        0 => unreachable!("logical chain must contain at least one operand"),
        1 => {
            return operands
                .next()
                .expect("non-empty logical chain must retain its operand");
        }
        _ => {}
    }
    let left_len = len / 2;
    let lhs = build_balanced_logical_expr(kind, operands, left_len);
    let rhs = build_balanced_logical_expr(kind, operands, len - left_len);
    let logical = Box::new(AstLogicalExpr {
        lhs,
        rhs,
        preserves_boolean_prewrite: false,
    });
    match kind {
        LogicalKind::And => AstExpr::LogicalAnd(logical),
        LogicalKind::Or => AstExpr::LogicalOr(logical),
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum PackLoweringContext {
    Ordinary,
    TargetCounted(usize),
}

fn lower_access_expr<T, FField, FIndex>(
    proto_index: usize,
    access: &HirTableAccess,
    lowerer: &mut AstLowerer<'_>,
    make_field: FField,
    make_index: FIndex,
) -> Result<T, AstLowerError>
where
    FField: FnOnce(AstFieldAccess) -> T,
    FIndex: FnOnce(AstIndexAccess) -> T,
{
    let base = lowerer.lower_expr(proto_index, &access.base)?;
    if let Some(field_name) = field_name_from_key(&access.key, lowerer.target.version) {
        return Ok(make_field(AstFieldAccess {
            base,
            field: field_name,
        }));
    }
    Ok(make_index(AstIndexAccess {
        base,
        index: lowerer.lower_expr(proto_index, &access.key)?,
    }))
}

fn lower_unary_op(op: HirUnaryOpKind) -> AstUnaryOpKind {
    match op {
        HirUnaryOpKind::Not => AstUnaryOpKind::Not,
        HirUnaryOpKind::Neg => AstUnaryOpKind::Neg,
        HirUnaryOpKind::BitNot => AstUnaryOpKind::BitNot,
        HirUnaryOpKind::Length => AstUnaryOpKind::Length,
    }
}

fn lower_binary_op(op: HirBinaryOpKind) -> AstBinaryOpKind {
    match op {
        HirBinaryOpKind::Add => AstBinaryOpKind::Add,
        HirBinaryOpKind::Sub => AstBinaryOpKind::Sub,
        HirBinaryOpKind::Mul => AstBinaryOpKind::Mul,
        HirBinaryOpKind::Div => AstBinaryOpKind::Div,
        HirBinaryOpKind::FloorDiv => AstBinaryOpKind::FloorDiv,
        HirBinaryOpKind::Mod => AstBinaryOpKind::Mod,
        HirBinaryOpKind::Pow => AstBinaryOpKind::Pow,
        HirBinaryOpKind::BitAnd => AstBinaryOpKind::BitAnd,
        HirBinaryOpKind::BitOr => AstBinaryOpKind::BitOr,
        HirBinaryOpKind::BitXor => AstBinaryOpKind::BitXor,
        HirBinaryOpKind::Shl => AstBinaryOpKind::Shl,
        HirBinaryOpKind::Shr => AstBinaryOpKind::Shr,
        HirBinaryOpKind::Concat => AstBinaryOpKind::Concat,
        HirBinaryOpKind::Eq => AstBinaryOpKind::Eq,
        HirBinaryOpKind::Lt => AstBinaryOpKind::Lt,
        HirBinaryOpKind::Le => AstBinaryOpKind::Le,
        HirBinaryOpKind::Gt => AstBinaryOpKind::Gt,
        HirBinaryOpKind::Ge => AstBinaryOpKind::Ge,
    }
}

fn field_name_from_key(key: &HirExpr, dialect: DecompileDialect) -> Option<String> {
    match key {
        HirExpr::String(key) => identifier_from_lua_key(key, dialect),
        _ => None,
    }
}

fn identifier_from_lua_key(key: &crate::LuaString, dialect: DecompileDialect) -> Option<String> {
    let name = key.as_utf8()?;
    dialect.is_identifier_name(name).then(|| name.to_owned())
}

fn lower_global_expr(
    proto_index: usize,
    key: &crate::LuaString,
    dialect: DecompileDialect,
) -> Result<AstExpr, AstLowerError> {
    if let Some(text) = identifier_from_lua_key(key, dialect)
        && !(dialect_has_lexical_environment(dialect) && text == "_ENV")
    {
        return Ok(AstExpr::Var(AstNameRef::Global(AstGlobalName { text })));
    }
    if dialect_has_lexical_environment(dialect) {
        return Ok(AstExpr::IndexAccess(Box::new(environment_index(key))));
    }
    Err(invalid_global_name(proto_index, key, dialect))
}

fn lower_global_lvalue(
    proto_index: usize,
    key: &crate::LuaString,
    dialect: DecompileDialect,
) -> Result<AstLValue, AstLowerError> {
    if let Some(text) = identifier_from_lua_key(key, dialect)
        && !(dialect_has_lexical_environment(dialect) && text == "_ENV")
    {
        return Ok(AstLValue::Name(AstNameRef::Global(AstGlobalName { text })));
    }
    if dialect_has_lexical_environment(dialect) {
        return Ok(AstLValue::IndexAccess(Box::new(environment_index(key))));
    }
    Err(invalid_global_name(proto_index, key, dialect))
}

fn environment_index(key: &crate::LuaString) -> AstIndexAccess {
    AstIndexAccess {
        base: AstExpr::Var(AstNameRef::Environment),
        index: AstExpr::String(key.clone()),
    }
}

const fn dialect_has_lexical_environment(dialect: DecompileDialect) -> bool {
    matches!(
        dialect,
        DecompileDialect::Lua52
            | DecompileDialect::Lua53
            | DecompileDialect::Lua54
            | DecompileDialect::Lua55
    )
}

fn invalid_global_name(
    proto_index: usize,
    key: &crate::LuaString,
    dialect: DecompileDialect,
) -> AstLowerError {
    AstLowerError::InvalidGlobalName {
        proto: proto_index,
        dialect,
        key: key.debug_literal(),
    }
}
