//! AST build：表达式、左值和 value pack 的机械 lowering。
//!
//! 这里依赖 HIR 已经把标量表达式与唯一可展开的 pack tail 分开，不再从 Call/VarArg
//! 形状猜多值语义。固定 pack 尾调用只在普通列表或目标槽位会暴露额外返回值时降成
//! `SingleValue`，open tail 则保持展开；非 target-counted 上下文若仍收到 exact tail，
//! 说明 HIR 物化尚未完成并直接报错。

use std::collections::BTreeSet;

use crate::hir::{
    HirAssign, HirBinaryOpKind, HirCallExpr, HirClosureExpr, HirExpr, HirLValue, HirLocalDecl,
    HirTableAccess, HirTableField, HirTableKey, HirUnaryOpKind, HirValuePack,
};

use super::{AstLowerError, AstLowerer};
use crate::ast::DecompileDialect;
use crate::ast::common::{
    AstAssign, AstBinaryExpr, AstBinaryOpKind, AstCallExpr, AstCallKind, AstExpr, AstFieldAccess,
    AstFunctionExpr, AstGlobalName, AstIndexAccess, AstLValue, AstLocalDecl, AstLogicalExpr,
    AstMethodCallExpr, AstNameRef, AstTableConstructor, AstTableField, AstTableKey, AstUnaryExpr,
    AstUnaryOpKind, is_lua_identifier_name,
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

    fn lower_function_expr(
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
        let body = self.lower_proto_body(closure.proto.index())?;
        let named_vararg =
            if child.signature.has_vararg_param_reg && !child.signature.legacy_arg_slot {
                let local = child.locals.first().copied().ok_or(
                    AstLowerError::MissingNamedVarargBinding {
                        proto: closure.proto.index(),
                    },
                )?;
                (super::analysis::count_local_uses_in_block(&child.body, local) != 0)
                    .then_some(crate::ast::common::AstBindingRef::Local(local))
            } else {
                None
            };
        let mut captured_bindings = BTreeSet::new();
        let mut captured_params = BTreeSet::new();
        for capture in &closure.captures {
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
        }
        Ok(AstFunctionExpr {
            function: closure.proto,
            params: child.params.clone(),
            is_vararg: child.signature.is_vararg,
            named_vararg,
            body,
            captured_bindings,
            captured_params,
        })
    }

    pub(super) fn lower_local_decl(
        &mut self,
        proto_index: usize,
        local_decl: &HirLocalDecl,
    ) -> Result<AstLocalDecl, AstLowerError> {
        let _ = proto_index;
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
        })
    }

    pub(super) fn lower_assign(
        &mut self,
        proto_index: usize,
        assign: &HirAssign,
    ) -> Result<AstAssign, AstLowerError> {
        Ok(AstAssign {
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
        })
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
            HirLValue::Upvalue(upvalue) => AstLValue::Name(AstNameRef::Upvalue(*upvalue)),
            HirLValue::Global(global) => AstLValue::Name(AstNameRef::Global(AstGlobalName {
                text: global.name.clone(),
            })),
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
            HirExpr::UpvalueRef(upvalue) => AstExpr::Var(AstNameRef::Upvalue(*upvalue)),
            HirExpr::TempRef(temp) => AstExpr::Var(AstNameRef::Temp(*temp)),
            HirExpr::GlobalRef(global) => AstExpr::Var(AstNameRef::Global(AstGlobalName {
                text: global.name.clone(),
            })),
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
            HirExpr::LogicalAnd(logical) => AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
                lhs: self.lower_expr(proto_index, &logical.lhs)?,
                rhs: self.lower_expr(proto_index, &logical.rhs)?,
            })),
            HirExpr::LogicalOr(logical) => AstExpr::LogicalOr(Box::new(AstLogicalExpr {
                lhs: self.lower_expr(proto_index, &logical.lhs)?,
                rhs: self.lower_expr(proto_index, &logical.rhs)?,
            })),
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
                                key: match &record.key {
                                    HirTableKey::Name(name) => AstTableKey::Name(name.clone()),
                                    HirTableKey::Expr(expr) => {
                                        AstTableKey::Expr(self.lower_expr(proto_index, expr)?)
                                    }
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
                AstExpr::TableConstructor(Box::new(AstTableConstructor { fields }))
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

    pub(super) fn lower_call(
        &mut self,
        proto_index: usize,
        call: &HirCallExpr,
    ) -> Result<AstCallKind, AstLowerError> {
        let mut args =
            self.lower_value_pack(proto_index, &call.args, PackLoweringContext::Ordinary)?;

        if call.method
            && let Some(method_name) = &call.method_name
        {
            if args.is_empty() {
                return Err(AstLowerError::InvalidMethodCallPattern {
                    proto: proto_index,
                    reason: "method call must keep the implicit receiver as its first argument",
                });
            }
            // 这里优先信任前层 `SELF/NAMECALL` 留下的结构事实，而不是再从 callee
            // 形状反推 method sugar。这样即使中途出现 `local f = obj.pick; f(obj, 4)`
            // 这样的 alias scaffolding，也能稳定回收到 `obj:pick(4)`。
            let receiver = args.remove(0);
            return Ok(AstCallKind::MethodCall(Box::new(AstMethodCallExpr {
                receiver,
                method: method_name.clone(),
                args,
            })));
        }

        let callee = self.lower_expr(proto_index, &call.callee)?;

        if call.method
            && let AstExpr::FieldAccess(access) = callee
        {
            if args.is_empty() {
                return Err(AstLowerError::InvalidMethodCallPattern {
                    proto: proto_index,
                    reason: "method call must keep the implicit receiver as its first argument",
                });
            }
            args.remove(0);
            return Ok(AstCallKind::MethodCall(Box::new(AstMethodCallExpr {
                receiver: access.base,
                method: access.field,
                args,
            })));
        }

        Ok(AstCallKind::Call(Box::new(AstCallExpr { callee, args })))
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
        HirExpr::String(name) => {
            let name = name.as_utf8()?;
            is_lua_identifier_name(name, dialect).then(|| name.to_owned())
        }
        _ => None,
    }
}
