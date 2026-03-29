//! 这个子模块负责把 AST 表达式序列化成目标 Lua 源码片段。
//!
//! 它依赖 AST 已经保真的表达式形状、precedence helper 和 naming 结果，只负责发射语法，
//! 不会在这里再猜补缺失的 sugar。
//! 例如：`AstExpr::SingleValue(call)` 会在这里带括号输出成单值调用表达式。

use crate::ast::pretty::{preferred_negated_relational_render, preferred_relational_render};
use crate::ast::{
    AstCallExpr, AstCallKind, AstExpr, AstFieldAccess, AstFunctionExpr, AstFunctionName,
    AstIndexAccess, AstLValue, AstMethodCallExpr, AstNamePath, AstNameRef, AstRecordField,
    AstTableConstructor, AstTableField, AstTableKey, AstUnaryOpKind,
};
use crate::generate::doc::Doc;
use crate::hir::HirProtoRef;

use super::super::common::TableStyle;
use super::super::error::GenerateError;
use super::syntax::{
    binary_meta, format_complex_literal, format_number, format_string_literal, maybe_parenthesize,
};
use super::{
    Assoc, Emitter, ExprSide, PREC_AND, PREC_COMPARE, PREC_LITERAL, PREC_OR, PREC_PREFIX,
    PREC_UNARY,
};

impl<'a> Emitter<'a> {
    pub(super) fn emit_call_kind(
        &self,
        call: &AstCallKind,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        match call {
            AstCallKind::Call(call) => self.emit_call_expr(call, function),
            AstCallKind::MethodCall(call) => self.emit_method_call_expr(call, function),
        }
    }

    fn emit_call_expr(
        &self,
        call: &AstCallExpr,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        let callee = self.emit_expr(&call.callee, function, PREC_PREFIX, ExprSide::Left)?;
        let args = call
            .args
            .iter()
            .map(|arg| self.emit_expr(arg, function, 0, ExprSide::Standalone))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Doc::concat([callee, self.emit_parenthesized_list(args)]))
    }

    fn emit_method_call_expr(
        &self,
        call: &AstMethodCallExpr,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        let receiver = self.emit_expr(&call.receiver, function, PREC_PREFIX, ExprSide::Left)?;
        let args = call
            .args
            .iter()
            .map(|arg| self.emit_expr(arg, function, 0, ExprSide::Standalone))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Doc::concat([
            receiver,
            Doc::text(format!(":{}", call.method)),
            self.emit_parenthesized_list(args),
        ]))
    }

    pub(super) fn emit_lvalue(
        &self,
        lvalue: &AstLValue,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        match lvalue {
            AstLValue::Name(name) => self.emit_name_ref(name, function),
            AstLValue::FieldAccess(access) => self.emit_field_access(access, function),
            AstLValue::IndexAccess(access) => self.emit_index_access(access, function),
        }
    }

    pub(super) fn emit_expr(
        &self,
        expr: &AstExpr,
        function: HirProtoRef,
        parent_prec: u8,
        side: ExprSide,
    ) -> Result<Doc, GenerateError> {
        let (doc, prec, assoc) = match expr {
            AstExpr::Nil => (Doc::text("nil"), PREC_LITERAL, Assoc::Non),
            AstExpr::Boolean(value) => (
                Doc::text(if *value { "true" } else { "false" }),
                PREC_LITERAL,
                Assoc::Non,
            ),
            AstExpr::Integer(value) => (Doc::text(value.to_string()), PREC_LITERAL, Assoc::Non),
            AstExpr::Number(value) => (Doc::text(format_number(*value)), PREC_LITERAL, Assoc::Non),
            AstExpr::String(value) => (
                Doc::text(format_string_literal(value, self.options.quote_style)),
                PREC_LITERAL,
                Assoc::Non,
            ),
            AstExpr::Int64(value) => (Doc::text(format!("{value}LL")), PREC_LITERAL, Assoc::Non),
            AstExpr::UInt64(value) => (Doc::text(format!("{value}ULL")), PREC_LITERAL, Assoc::Non),
            AstExpr::Complex { real, imag } => (
                Doc::text(format_complex_literal(*real, *imag)),
                PREC_LITERAL,
                Assoc::Non,
            ),
            AstExpr::Var(name) => (
                self.emit_name_ref(name, function)?,
                PREC_PREFIX,
                Assoc::Left,
            ),
            AstExpr::FieldAccess(access) => (
                self.emit_field_access(access, function)?,
                PREC_PREFIX,
                Assoc::Left,
            ),
            AstExpr::IndexAccess(access) => (
                self.emit_index_access(access, function)?,
                PREC_PREFIX,
                Assoc::Left,
            ),
            AstExpr::Unary(unary) => {
                if let Some(preferred) = preferred_negated_relational_render(unary) {
                    let prec = PREC_COMPARE;
                    let lhs = self.emit_expr(preferred.lhs, function, prec, ExprSide::Left)?;
                    let rhs = self.emit_expr(preferred.rhs, function, prec, ExprSide::Right)?;
                    (
                        Doc::concat([
                            lhs,
                            Doc::text(" "),
                            Doc::text(preferred.op_text),
                            Doc::text(" "),
                            rhs,
                        ]),
                        prec,
                        Assoc::Non,
                    )
                } else {
                    let prec = PREC_UNARY;
                    let inner = self.emit_expr(&unary.expr, function, prec, ExprSide::Right)?;
                    let op = match unary.op {
                        AstUnaryOpKind::Not => "not ",
                        AstUnaryOpKind::Neg => "-",
                        AstUnaryOpKind::BitNot => "~",
                        AstUnaryOpKind::Length => "#",
                    };
                    (Doc::concat([Doc::text(op), inner]), prec, Assoc::Right)
                }
            }
            AstExpr::Binary(binary) => {
                let (prec, assoc, op) = binary_meta(binary.op);
                let (lhs_expr, op_text, rhs_expr) =
                    if let Some(preferred) = preferred_relational_render(binary) {
                        (preferred.lhs, preferred.op_text, preferred.rhs)
                    } else {
                        (&binary.lhs, op, &binary.rhs)
                    };
                let lhs = self.emit_expr(lhs_expr, function, prec, ExprSide::Left)?;
                let rhs = self.emit_expr(rhs_expr, function, prec, ExprSide::Right)?;
                (
                    Doc::concat([lhs, Doc::text(" "), Doc::text(op_text), Doc::text(" "), rhs]),
                    prec,
                    assoc,
                )
            }
            AstExpr::LogicalAnd(logical) => {
                let lhs = self.emit_expr(&logical.lhs, function, PREC_AND, ExprSide::Left)?;
                let rhs = self.emit_expr(&logical.rhs, function, PREC_AND, ExprSide::Right)?;
                (
                    Doc::concat([lhs, Doc::text(" and "), rhs]),
                    PREC_AND,
                    Assoc::Left,
                )
            }
            AstExpr::LogicalOr(logical) => {
                let lhs = self.emit_expr(&logical.lhs, function, PREC_OR, ExprSide::Left)?;
                let rhs = self.emit_expr(&logical.rhs, function, PREC_OR, ExprSide::Right)?;
                (
                    Doc::concat([lhs, Doc::text(" or "), rhs]),
                    PREC_OR,
                    Assoc::Left,
                )
            }
            AstExpr::Call(call) => (
                self.emit_call_expr(call, function)?,
                PREC_PREFIX,
                Assoc::Left,
            ),
            AstExpr::MethodCall(call) => (
                self.emit_method_call_expr(call, function)?,
                PREC_PREFIX,
                Assoc::Left,
            ),
            AstExpr::SingleValue(expr) => (
                Doc::concat([
                    Doc::text("("),
                    self.emit_expr(expr, function, 0, ExprSide::Standalone)?,
                    Doc::text(")"),
                ]),
                PREC_LITERAL,
                Assoc::Non,
            ),
            AstExpr::VarArg => (Doc::text("..."), PREC_LITERAL, Assoc::Non),
            AstExpr::TableConstructor(table) => (
                self.emit_table_constructor(table, function)?,
                PREC_LITERAL,
                Assoc::Non,
            ),
            AstExpr::FunctionExpr(func) => {
                (self.emit_function_expr(func)?, PREC_LITERAL, Assoc::Non)
            }
        };
        Ok(maybe_parenthesize(doc, prec, parent_prec, side, assoc))
    }

    pub(super) fn emit_name_ref(
        &self,
        name: &AstNameRef,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        Ok(Doc::text(self.names.resolve_name_ref(function, name)?))
    }

    fn emit_field_access(
        &self,
        access: &AstFieldAccess,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        let base = self.emit_expr(&access.base, function, PREC_PREFIX, ExprSide::Left)?;
        Ok(Doc::concat([base, Doc::text(format!(".{}", access.field))]))
    }

    fn emit_index_access(
        &self,
        access: &AstIndexAccess,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        let base = self.emit_expr(&access.base, function, PREC_PREFIX, ExprSide::Left)?;
        let index = self.emit_expr(&access.index, function, 0, ExprSide::Standalone)?;
        Ok(Doc::concat([base, Doc::text("["), index, Doc::text("]")]))
    }

    fn emit_table_constructor(
        &self,
        table: &AstTableConstructor,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        if table.fields.is_empty() {
            return Ok(Doc::text("{}"));
        }
        let field_docs = table
            .fields
            .iter()
            .map(|field| self.emit_table_field(field, function))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(match self.options.table_style {
            TableStyle::Expanded => Doc::concat([
                Doc::text("{"),
                Doc::line(),
                Doc::indent(Doc::join(
                    field_docs,
                    Doc::concat([Doc::text(","), Doc::line()]),
                )),
                Doc::line(),
                Doc::text("}"),
            ]),
            TableStyle::Compact | TableStyle::Balanced => {
                let separator = Doc::concat([Doc::text(","), Doc::soft_line()]);
                Doc::group(Doc::concat([
                    Doc::text("{"),
                    Doc::indent(Doc::concat([
                        Doc::soft_line(),
                        Doc::join(field_docs, separator),
                    ])),
                    Doc::soft_line(),
                    Doc::text("}"),
                ]))
            }
        })
    }

    fn emit_table_field(
        &self,
        field: &AstTableField,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        match field {
            AstTableField::Array(expr) => self.emit_expr(expr, function, 0, ExprSide::Standalone),
            AstTableField::Record(record) => self.emit_record_field(record, function),
        }
    }

    fn emit_record_field(
        &self,
        record: &AstRecordField,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        let key = match &record.key {
            AstTableKey::Name(name) => Doc::text(name.clone()),
            AstTableKey::Expr(expr) => Doc::concat([
                Doc::text("["),
                self.emit_expr(expr, function, 0, ExprSide::Standalone)?,
                Doc::text("]"),
            ]),
        };
        let value = self.emit_expr(&record.value, function, 0, ExprSide::Standalone)?;
        Ok(Doc::concat([key, Doc::text(" = "), value]))
    }

    fn emit_function_expr(&self, func: &AstFunctionExpr) -> Result<Doc, GenerateError> {
        self.emit_function_with_header(func, Doc::text("function"))
    }

    pub(super) fn emit_function_name(
        &self,
        function_name: &AstFunctionName,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        match function_name {
            AstFunctionName::Plain(path) => self.emit_name_path(path, function),
            AstFunctionName::Method(path, method) => Ok(Doc::concat([
                self.emit_name_path(path, function)?,
                Doc::text(format!(":{method}")),
            ])),
        }
    }

    fn emit_name_path(
        &self,
        path: &AstNamePath,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        let mut parts = vec![self.emit_name_ref(&path.root, function)?];
        for field in &path.fields {
            parts.push(Doc::text(format!(".{field}")));
        }
        Ok(Doc::concat(parts))
    }

    pub(super) fn emit_function_with_header(
        &self,
        func: &AstFunctionExpr,
        header: Doc,
    ) -> Result<Doc, GenerateError> {
        let params = self.emit_decl_param_list(func, false)?;
        self.emit_function_with_header_and_params(func, header, params)
    }

    pub(super) fn emit_function_with_header_and_params(
        &self,
        func: &AstFunctionExpr,
        header: Doc,
        params: Doc,
    ) -> Result<Doc, GenerateError> {
        let body = self.emit_block(&func.body, func.function)?;
        let mut parts = vec![header, params, self.emit_indented_body(&func.body, body)];
        parts.push(Doc::line());
        parts.push(Doc::text("end"));
        Ok(Doc::concat(parts))
    }

    pub(super) fn emit_decl_param_list(
        &self,
        func: &AstFunctionExpr,
        implicit_self: bool,
    ) -> Result<Doc, GenerateError> {
        let mut params = func
            .params
            .iter()
            .skip(usize::from(implicit_self))
            .map(|param| {
                self.names
                    .resolve_name_ref(func.function, &AstNameRef::Param(*param))
                    .map(Doc::text)
            })
            .collect::<Result<Vec<_>, _>>()?;
        if func.is_vararg {
            let vararg = if let Some(binding) = func.named_vararg {
                Doc::text(format!(
                    "...{}",
                    self.names.resolve_binding_ref(func.function, &binding)?
                ))
            } else {
                Doc::text("...")
            };
            params.push(vararg);
        }
        Ok(self.emit_parenthesized_list(params))
    }
}
