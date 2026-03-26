//! AST build：表达式和常规语句 lowering。

use crate::hir::{
    HirAssign, HirBinaryOpKind, HirCallExpr, HirClosureExpr, HirExpr, HirLValue, HirLocalDecl,
    HirTableAccess, HirTableField, HirTableKey, HirUnaryOpKind,
};

use super::{AstLowerError, AstLowerer};
use crate::ast::common::{
    AstAssign, AstBinaryExpr, AstBinaryOpKind, AstCallExpr, AstCallKind, AstExpr, AstFieldAccess,
    AstFunctionExpr, AstGlobalName, AstIndexAccess, AstLValue, AstLocalAttr, AstLocalBinding,
    AstLocalDecl, AstLogicalExpr, AstMethodCallExpr, AstNameRef, AstTableConstructor,
    AstTableField, AstTableKey, AstUnaryExpr, AstUnaryOpKind,
};

impl<'a> AstLowerer<'a> {
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
        Ok(AstFunctionExpr {
            params: child.params.clone(),
            is_vararg: child.signature.is_vararg,
            body,
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
                .map(|binding| AstLocalBinding {
                    id: crate::ast::common::AstBindingRef::Local(binding),
                    attr: AstLocalAttr::None,
                })
                .collect(),
            values: local_decl
                .values
                .iter()
                .map(|value| self.lower_expr(proto_index, value))
                .collect::<Result<Vec<_>, _>>()?,
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
            values: assign
                .values
                .iter()
                .map(|value| self.lower_expr(proto_index, value))
                .collect::<Result<Vec<_>, _>>()?,
        })
    }

    pub(super) fn lower_lvalue(
        &mut self,
        proto_index: usize,
        target: &HirLValue,
    ) -> Result<AstLValue, AstLowerError> {
        Ok(match target {
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
                return Err(AstLowerError::ResidualHir {
                    proto: proto_index,
                    kind: "decision expr",
                });
            }
            HirExpr::Call(call) => match self.lower_call(proto_index, call)? {
                AstCallKind::Call(call) => AstExpr::Call(call),
                AstCallKind::MethodCall(call) => AstExpr::MethodCall(call),
            },
            HirExpr::VarArg => AstExpr::VarArg,
            HirExpr::TableConstructor(table) => {
                AstExpr::TableConstructor(Box::new(AstTableConstructor {
                    fields: table
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
                        .collect::<Result<Vec<_>, _>>()?,
                }))
            }
            HirExpr::Closure(closure) => {
                AstExpr::FunctionExpr(Box::new(self.lower_function_expr(proto_index, closure)?))
            }
            HirExpr::Unresolved(_) => {
                return Err(AstLowerError::ResidualHir {
                    proto: proto_index,
                    kind: "unresolved expr",
                });
            }
        })
    }

    pub(super) fn lower_call(
        &mut self,
        proto_index: usize,
        call: &HirCallExpr,
    ) -> Result<AstCallKind, AstLowerError> {
        let callee = self.lower_expr(proto_index, &call.callee)?;
        let args = call
            .args
            .iter()
            .map(|arg| self.lower_expr(proto_index, arg))
            .collect::<Result<Vec<_>, _>>()?;

        if call.method
            && let AstExpr::FieldAccess(access) = callee
        {
            return Ok(AstCallKind::MethodCall(Box::new(AstMethodCallExpr {
                receiver: access.base,
                method: access.field,
                args,
            })));
        }

        Ok(AstCallKind::Call(Box::new(AstCallExpr { callee, args })))
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
    if let Some(field_name) = field_name_from_key(&access.key) {
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

fn field_name_from_key(key: &HirExpr) -> Option<String> {
    match key {
        HirExpr::String(name) if is_lua_identifier(name) => Some(name.clone()),
        _ => None,
    }
}

fn is_lua_identifier(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !(first == '_' || first.is_ascii_alphabetic()) {
        return false;
    }
    if !chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric()) {
        return false;
    }
    !matches!(
        name,
        "and"
            | "break"
            | "do"
            | "else"
            | "elseif"
            | "end"
            | "false"
            | "for"
            | "function"
            | "goto"
            | "if"
            | "in"
            | "local"
            | "nil"
            | "not"
            | "or"
            | "repeat"
            | "return"
            | "then"
            | "true"
            | "until"
            | "while"
            | "global"
    )
}
