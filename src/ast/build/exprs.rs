//! AST build：表达式、左值和 value pack 的机械 lowering。
//!
//! 这里依赖 HIR 已经把标量表达式与唯一可展开的 pack tail 分开，不再从 Call/VarArg
//! 形状猜多值语义。固定 pack 尾调用只在普通列表或目标槽位会暴露额外返回值时降成
//! `SingleValue`，open tail 则保持展开；非 target-counted 上下文若仍收到 exact tail，
//! 说明 HIR 物化尚未完成并直接报错。
//! 本地范围清零保留 HIR 的成组生命周期证明，在此落成无需整组 RHS 暂存槽的标量写入。
//! closure lowering 同时是 `capture_names_by_upvalue` 的唯一 producer：它按 HIR capture
//! 顺序保留 child UpvalueId 到父级 Param/Local/Temp/Upvalue 名字的对应，供后续精确分析。
//! 表构造器的 record key 同样只从 HIR 语义表达式降低：合法 UTF-8 identifier 在本层按
//! 目标方言写成命名字段，其余键保持显式索引表达式，HIR 不承载这项源码语法选择。

use std::collections::{BTreeMap, BTreeSet};

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
    AstUnaryExpr, AstUnaryOpKind, is_lua_identifier_name,
};

impl<'a> AstLowerer<'a> {
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
                super::analysis::local_is_referenced(&child.body, local)
                    .then_some(crate::ast::common::AstBindingRef::Local(local))
            } else {
                None
            };
        let mut captured_bindings = BTreeSet::new();
        let mut captured_params = BTreeSet::new();
        let mut capture_names_by_upvalue = BTreeMap::new();
        let mut capture_write_names = BTreeSet::new();
        for (capture_index, capture) in closure.captures.iter().enumerate() {
            if let Some(name) = self.capture_name_from_hir_expr(owner_proto, &capture.value)? {
                capture_names_by_upvalue.insert(UpvalueId(capture_index), name);
            }
            match &capture.value {
                HirExpr::ParamRef(param) => {
                    captured_params.insert(*param);
                }
                value => {
                    if let Some(binding) = capture_binding_from_hir_expr(value) {
                        captured_bindings.insert(binding);
                    }
                }
            }
            if capture.mode == HirCaptureMode::ByReference
                && child.mutable_upvalues.contains(&UpvalueId(capture_index))
                && let Some(name) = self.capture_name_from_hir_expr(owner_proto, &capture.value)?
            {
                capture_write_names.insert(name);
            }
        }
        Ok(AstFunctionExpr {
            function: closure.proto,
            params: child.params.clone(),
            is_vararg: child.signature.is_vararg,
            named_vararg,
            body,
            captured_bindings,
            captured_params,
            capture_names_by_upvalue,
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
            method_rewrite_transaction: assign.method_rewrite_transaction,
        };
        if assign.targets.len() > 1
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
            HirExpr::Unary(unary) => AstExpr::Unary(Box::new(AstUnaryExpr {
                op: lower_unary_op(unary.op),
                expr: self.lower_expr(proto_index, &unary.expr)?,
            })),
            HirExpr::Binary(binary) => AstExpr::Binary(Box::new(AstBinaryExpr {
                op: lower_binary_op(binary.op),
                lhs: self.lower_expr(proto_index, &binary.lhs)?,
                rhs: self.lower_expr(proto_index, &binary.rhs)?,
            })),
            HirExpr::LogicalAnd(_) => {
                self.lower_logical_chain(proto_index, expr, LogicalKind::And)?
            }
            HirExpr::LogicalOr(_) => {
                self.lower_logical_chain(proto_index, expr, LogicalKind::Or)?
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
                                key: if let Some(name) =
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
                | (LogicalKind::Or, HirExpr::LogicalOr(logical)) => logical,
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
            .and_then(|(_, method_key)| identifier_from_lua_key(method_key, self.target.version));
        let mut args =
            self.lower_value_pack(proto_index, &call.args, PackLoweringContext::Ordinary)?;

        if let Some(method_name) = method_name {
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

        if call.method && call.method_key.is_none() {
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

    fn capture_name_from_hir_expr(
        &self,
        owner_proto: usize,
        expr: &HirExpr,
    ) -> Result<Option<AstNameRef>, AstLowerError> {
        Ok(match expr {
            HirExpr::ParamRef(param) => Some(AstNameRef::Param(*param)),
            HirExpr::LocalRef(local) => Some(AstNameRef::Local(*local)),
            HirExpr::TempRef(temp) => Some(AstNameRef::Temp(*temp)),
            HirExpr::UpvalueRef(upvalue) => Some(self.lower_upvalue_name(owner_proto, *upvalue)?),
            _ => None,
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
    let logical = Box::new(AstLogicalExpr { lhs, rhs });
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

fn capture_binding_from_hir_expr(expr: &HirExpr) -> Option<crate::ast::common::AstBindingRef> {
    match expr {
        HirExpr::LocalRef(local) => Some(crate::ast::common::AstBindingRef::Local(*local)),
        HirExpr::TempRef(temp) => Some(crate::ast::common::AstBindingRef::Temp(*temp)),
        _ => None,
    }
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
    is_lua_identifier_name(name, dialect).then(|| name.to_owned())
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
