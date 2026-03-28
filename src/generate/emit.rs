//! AST -> Doc lowering。
//!
//! 这里采用外部 emitter，而不是把“生成字符串”的方法塞回 AST 节点本身。
//! 这样 AST 仍保持纯语法数据，Generate 只在这一层处理名字解析、括号优先级和布局意图。

use crate::ast::pretty::preferred_relational_render;
use crate::ast::{
    AstAssign, AstBindingRef, AstBlock, AstCallExpr, AstCallKind, AstCallStmt, AstExpr,
    AstFieldAccess, AstFunctionDecl, AstFunctionExpr, AstFunctionName, AstGenericFor,
    AstGlobalAttr, AstGlobalBinding, AstGlobalBindingTarget, AstGlobalDecl, AstIf, AstIndexAccess,
    AstLValue, AstLabel, AstLocalAttr, AstLocalBinding, AstLocalDecl, AstLocalFunctionDecl,
    AstMethodCallExpr, AstModule, AstNamePath, AstNameRef, AstNumericFor, AstRecordField,
    AstRepeat, AstReturn, AstStmt, AstTableConstructor, AstTableField, AstTableKey,
    AstTargetDialect, AstUnaryOpKind, AstWhile,
};
use crate::generate::doc::Doc;
use crate::hir::HirProtoRef;
use crate::naming::NameMap;

use super::common::{GenerateOptions, GeneratedChunk, QuoteStyle, TableStyle};
use super::error::GenerateError;
use super::render::render_doc;

const PREC_OR: u8 = 1;
const PREC_AND: u8 = 2;
const PREC_COMPARE: u8 = 3;
const PREC_BIT_OR: u8 = 4;
const PREC_BIT_XOR: u8 = 5;
const PREC_BIT_AND: u8 = 6;
const PREC_SHIFT: u8 = 7;
const PREC_CONCAT: u8 = 8;
const PREC_ADD: u8 = 9;
const PREC_MUL: u8 = 10;
const PREC_UNARY: u8 = 11;
const PREC_POW: u8 = 12;
const PREC_LITERAL: u8 = 13;
const PREC_PREFIX: u8 = 14;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Assoc {
    Left,
    Right,
    Non,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExprSide {
    Standalone,
    Left,
    Right,
}

/// Generate 对外入口。
pub fn generate_chunk(
    module: &AstModule,
    names: &NameMap,
    target: AstTargetDialect,
    options: GenerateOptions,
) -> Result<GeneratedChunk, GenerateError> {
    let emitter = Emitter {
        names,
        target,
        options,
    };
    let doc = emitter.emit_module(module)?;
    Ok(GeneratedChunk {
        source: render_doc(&doc, options),
    })
}

struct Emitter<'a> {
    names: &'a NameMap,
    target: AstTargetDialect,
    options: GenerateOptions,
}

impl<'a> Emitter<'a> {
    fn emit_module(&self, module: &AstModule) -> Result<Doc, GenerateError> {
        self.emit_block(&module.body, module.entry_function)
    }

    fn emit_block(&self, block: &AstBlock, function: HirProtoRef) -> Result<Doc, GenerateError> {
        let docs = block
            .stmts
            .iter()
            .map(|stmt| self.emit_stmt(stmt, function))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Doc::join(docs, Doc::line()))
    }

    fn emit_stmt(&self, stmt: &AstStmt, function: HirProtoRef) -> Result<Doc, GenerateError> {
        match stmt {
            AstStmt::LocalDecl(local_decl) => self.emit_local_decl(local_decl, function),
            AstStmt::GlobalDecl(global_decl) => self.emit_global_decl(global_decl, function),
            AstStmt::Assign(assign) => self.emit_assign(assign, function),
            AstStmt::CallStmt(call_stmt) => self.emit_call_stmt(call_stmt, function),
            AstStmt::Return(ret) => self.emit_return(ret, function),
            AstStmt::If(ast_if) => self.emit_if(ast_if, function),
            AstStmt::While(ast_while) => self.emit_while(ast_while, function),
            AstStmt::Repeat(ast_repeat) => self.emit_repeat(ast_repeat, function),
            AstStmt::NumericFor(numeric_for) => self.emit_numeric_for(numeric_for, function),
            AstStmt::GenericFor(generic_for) => self.emit_generic_for(generic_for, function),
            AstStmt::Break => Ok(Doc::text("break")),
            AstStmt::Continue => {
                if !self.target.caps.continue_stmt {
                    return Err(GenerateError::UnsupportedFeature {
                        dialect: self.target.version,
                        feature: "continue",
                    });
                }
                Ok(Doc::text("continue"))
            }
            AstStmt::Goto(ast_goto) => {
                if !self.target.caps.goto_label {
                    return Err(GenerateError::UnsupportedFeature {
                        dialect: self.target.version,
                        feature: "goto",
                    });
                }
                Ok(Doc::text(format!(
                    "goto {}",
                    format_label_name(ast_goto.target)
                )))
            }
            AstStmt::Label(label) => self.emit_label(label),
            AstStmt::DoBlock(block) => self.emit_do_block(block, function),
            AstStmt::FunctionDecl(function_decl) => {
                self.emit_function_decl(function_decl, function)
            }
            AstStmt::LocalFunctionDecl(local_function_decl) => {
                self.emit_local_function_decl(local_function_decl, function)
            }
        }
    }

    fn emit_local_decl(
        &self,
        local_decl: &AstLocalDecl,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        let bindings = local_decl
            .bindings
            .iter()
            .map(|binding| self.emit_local_binding(binding, function))
            .collect::<Result<Vec<_>, _>>()?;
        let mut parts = vec![Doc::text("local "), Doc::join(bindings, Doc::text(", "))];
        if !local_decl.values.is_empty() {
            parts.push(Doc::text(" = "));
            parts.push(self.emit_value_list(&local_decl.values, function)?);
        }
        Ok(Doc::concat(parts))
    }

    fn emit_local_binding(
        &self,
        binding: &AstLocalBinding,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        let name = self.resolve_binding_ref(function, &binding.id)?;
        let text = match binding.attr {
            AstLocalAttr::None => name,
            AstLocalAttr::Const => format!("{name} <const>"),
            AstLocalAttr::Close => format!("{name} <close>"),
        };
        Ok(Doc::text(text))
    }

    fn emit_global_decl(
        &self,
        global_decl: &AstGlobalDecl,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        if !self.target.caps.global_decl {
            return Err(GenerateError::UnsupportedFeature {
                dialect: self.target.version,
                feature: "global",
            });
        }

        let attr = common_global_attr(global_decl.bindings.as_slice()).ok_or(
            GenerateError::MixedGlobalAttrs {
                function: function.index(),
            },
        )?;
        if matches!(attr, AstGlobalAttr::Const) && !self.target.caps.global_const {
            return Err(GenerateError::UnsupportedFeature {
                dialect: self.target.version,
                feature: "global<const>",
            });
        }

        let keyword = match attr {
            AstGlobalAttr::None => "global",
            AstGlobalAttr::Const => "global<const>",
        };
        let bindings = global_decl
            .bindings
            .iter()
            .map(Self::emit_global_binding_target)
            .collect::<Vec<_>>();
        let mut parts = vec![
            Doc::text(keyword),
            Doc::text(" "),
            Doc::join(bindings, Doc::text(", ")),
        ];
        if !global_decl.values.is_empty() {
            parts.push(Doc::text(" = "));
            parts.push(self.emit_value_list(&global_decl.values, function)?);
        }
        Ok(Doc::concat(parts))
    }

    fn emit_global_binding_target(binding: &AstGlobalBinding) -> Doc {
        match &binding.target {
            AstGlobalBindingTarget::Name(name) => Doc::text(name.text.clone()),
            AstGlobalBindingTarget::Wildcard => Doc::text("*"),
        }
    }

    fn emit_assign(&self, assign: &AstAssign, function: HirProtoRef) -> Result<Doc, GenerateError> {
        let targets = assign
            .targets
            .iter()
            .map(|target| self.emit_lvalue(target, function))
            .collect::<Result<Vec<_>, _>>()?;
        let values = self.emit_value_list(&assign.values, function)?;
        Ok(Doc::concat([
            Doc::join(targets, Doc::text(", ")),
            Doc::text(" = "),
            values,
        ]))
    }

    fn emit_call_stmt(
        &self,
        call_stmt: &AstCallStmt,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        self.emit_call_kind(&call_stmt.call, function)
    }

    fn emit_return(&self, ret: &AstReturn, function: HirProtoRef) -> Result<Doc, GenerateError> {
        if ret.values.is_empty() {
            return Ok(Doc::text("return"));
        }
        Ok(Doc::concat([
            Doc::text("return "),
            self.emit_value_list(&ret.values, function)?,
        ]))
    }

    fn emit_if(&self, ast_if: &AstIf, function: HirProtoRef) -> Result<Doc, GenerateError> {
        let cond = self.emit_expr(&ast_if.cond, function, 0, ExprSide::Standalone)?;
        let then_body = self.emit_block(&ast_if.then_block, function)?;
        let mut parts = vec![
            Doc::text("if "),
            cond,
            Doc::text(" then"),
            self.emit_indented_body(&ast_if.then_block, then_body),
        ];
        self.emit_if_else_chain(ast_if.else_block.as_ref(), function, &mut parts)?;
        parts.push(Doc::line());
        parts.push(Doc::text("end"));
        Ok(Doc::concat(parts))
    }

    fn emit_if_else_chain(
        &self,
        else_block: Option<&AstBlock>,
        function: HirProtoRef,
        parts: &mut Vec<Doc>,
    ) -> Result<(), GenerateError> {
        let Some(else_block) = else_block else {
            return Ok(());
        };

        if let [AstStmt::If(else_if)] = else_block.stmts.as_slice() {
            let cond = self.emit_expr(&else_if.cond, function, 0, ExprSide::Standalone)?;
            let then_body = self.emit_block(&else_if.then_block, function)?;
            parts.push(Doc::line());
            parts.push(Doc::text("elseif "));
            parts.push(cond);
            parts.push(Doc::text(" then"));
            parts.push(self.emit_indented_body(&else_if.then_block, then_body));
            return self.emit_if_else_chain(else_if.else_block.as_ref(), function, parts);
        }

        parts.push(Doc::line());
        parts.push(Doc::text("else"));
        parts.push(self.emit_indented_body(else_block, self.emit_block(else_block, function)?));
        Ok(())
    }

    fn emit_while(
        &self,
        ast_while: &AstWhile,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        let cond = self.emit_expr(&ast_while.cond, function, 0, ExprSide::Standalone)?;
        let body = self.emit_block(&ast_while.body, function)?;
        Ok(self.emit_block_stmt(
            Doc::concat([Doc::text("while "), cond, Doc::text(" do")]),
            &ast_while.body,
            body,
        ))
    }

    fn emit_repeat(
        &self,
        ast_repeat: &AstRepeat,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        let body = self.emit_block(&ast_repeat.body, function)?;
        let cond = self.emit_expr(&ast_repeat.cond, function, 0, ExprSide::Standalone)?;
        let mut parts = vec![
            Doc::text("repeat"),
            self.emit_indented_body(&ast_repeat.body, body),
        ];
        parts.push(Doc::line());
        parts.push(Doc::text("until "));
        parts.push(cond);
        Ok(Doc::concat(parts))
    }

    fn emit_numeric_for(
        &self,
        numeric_for: &AstNumericFor,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        let binding = self.resolve_binding_ref(function, &numeric_for.binding)?;
        let start = self.emit_expr(&numeric_for.start, function, 0, ExprSide::Standalone)?;
        let limit = self.emit_expr(&numeric_for.limit, function, 0, ExprSide::Standalone)?;
        let step = self.emit_expr(&numeric_for.step, function, 0, ExprSide::Standalone)?;
        let header = Doc::concat([
            Doc::text("for "),
            Doc::text(binding),
            Doc::text(" = "),
            start,
            Doc::text(", "),
            limit,
            Doc::text(", "),
            step,
            Doc::text(" do"),
        ]);
        let body = self.emit_block(&numeric_for.body, function)?;
        Ok(self.emit_block_stmt(header, &numeric_for.body, body))
    }

    fn emit_generic_for(
        &self,
        generic_for: &AstGenericFor,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        let bindings = generic_for
            .bindings
            .iter()
            .map(|binding| self.resolve_binding_ref(function, binding).map(Doc::text))
            .collect::<Result<Vec<_>, _>>()?;
        let header = Doc::concat([
            Doc::text("for "),
            Doc::join(bindings, Doc::text(", ")),
            Doc::text(" in "),
            self.emit_value_list(&generic_for.iterator, function)?,
            Doc::text(" do"),
        ]);
        let body = self.emit_block(&generic_for.body, function)?;
        Ok(self.emit_block_stmt(header, &generic_for.body, body))
    }

    fn emit_label(&self, label: &AstLabel) -> Result<Doc, GenerateError> {
        if !self.target.caps.goto_label {
            return Err(GenerateError::UnsupportedFeature {
                dialect: self.target.version,
                feature: "label",
            });
        }
        Ok(Doc::text(format!("::{}::", format_label_name(label.id))))
    }

    fn emit_do_block(&self, block: &AstBlock, function: HirProtoRef) -> Result<Doc, GenerateError> {
        let body = self.emit_block(block, function)?;
        Ok(self.emit_block_stmt(Doc::text("do"), block, body))
    }

    fn emit_function_decl(
        &self,
        function_decl: &AstFunctionDecl,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        let target = self.emit_function_name(&function_decl.target, function)?;
        let header = Doc::concat([
            Doc::text(if self.function_decl_is_global(function_decl) {
                "global function "
            } else {
                "function "
            }),
            target,
        ]);
        let params = self.emit_decl_param_list(
            &function_decl.func,
            matches!(function_decl.target, AstFunctionName::Method(_, _)),
        )?;
        self.emit_function_with_header_and_params(&function_decl.func, header, params)
    }

    fn emit_local_function_decl(
        &self,
        local_function_decl: &AstLocalFunctionDecl,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        let name = self.resolve_binding_ref(function, &local_function_decl.name)?;
        let header = Doc::concat([Doc::text("local function "), Doc::text(name)]);
        self.emit_function_with_header(&local_function_decl.func, header)
    }

    fn emit_function_with_header(
        &self,
        func: &AstFunctionExpr,
        header: Doc,
    ) -> Result<Doc, GenerateError> {
        let params = self.emit_decl_param_list(func, false)?;
        self.emit_function_with_header_and_params(func, header, params)
    }

    fn emit_function_with_header_and_params(
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

    fn emit_decl_param_list(
        &self,
        func: &AstFunctionExpr,
        implicit_self: bool,
    ) -> Result<Doc, GenerateError> {
        let mut params = func
            .params
            .iter()
            .skip(usize::from(implicit_self))
            .map(|param| {
                self.resolve_name_ref(func.function, &AstNameRef::Param(*param))
                    .map(Doc::text)
            })
            .collect::<Result<Vec<_>, _>>()?;
        if func.is_vararg {
            let vararg = if let Some(binding) = func.named_vararg {
                Doc::text(format!(
                    "...{}",
                    self.resolve_binding_ref(func.function, &binding)?
                ))
            } else {
                Doc::text("...")
            };
            params.push(vararg);
        }
        Ok(self.emit_parenthesized_list(params))
    }

    fn emit_value_list(
        &self,
        values: &[AstExpr],
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        let docs = values
            .iter()
            .map(|expr| self.emit_expr(expr, function, 0, ExprSide::Standalone))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Doc::join(docs, Doc::text(", ")))
    }

    fn emit_parenthesized_list(&self, items: Vec<Doc>) -> Doc {
        Doc::concat([
            Doc::text("("),
            Doc::join(items, Doc::text(", ")),
            Doc::text(")"),
        ])
    }

    fn emit_block_stmt(&self, header: Doc, block: &AstBlock, body: Doc) -> Doc {
        Doc::concat([
            header,
            self.emit_indented_body(block, body),
            Doc::line(),
            Doc::text("end"),
        ])
    }

    fn emit_indented_body(&self, block: &AstBlock, body: Doc) -> Doc {
        if block.stmts.is_empty() {
            Doc::line()
        } else {
            self.emit_indented_body_nonempty(body)
        }
    }

    fn emit_indented_body_nonempty(&self, body: Doc) -> Doc {
        Doc::indent(Doc::concat([Doc::line(), body]))
    }

    fn emit_call_kind(
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

    fn emit_lvalue(&self, lvalue: &AstLValue, function: HirProtoRef) -> Result<Doc, GenerateError> {
        match lvalue {
            AstLValue::Name(name) => self.emit_name_ref(name, function),
            AstLValue::FieldAccess(access) => self.emit_field_access(access, function),
            AstLValue::IndexAccess(access) => self.emit_index_access(access, function),
        }
    }

    fn emit_expr(
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

    fn emit_name_ref(
        &self,
        name: &AstNameRef,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        Ok(Doc::text(self.resolve_name_ref(function, name)?))
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

    fn emit_function_name(
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

    fn function_decl_is_global(&self, function_decl: &AstFunctionDecl) -> bool {
        self.target.caps.global_decl
            && matches!(
                &function_decl.target,
                AstFunctionName::Plain(path) | AstFunctionName::Method(path, _)
                    if matches!(path.root, AstNameRef::Global(_))
            )
    }

    fn resolve_name_ref(
        &self,
        function: HirProtoRef,
        name: &AstNameRef,
    ) -> Result<String, GenerateError> {
        match name {
            AstNameRef::Global(global) => Ok(global.text.clone()),
            AstNameRef::Temp(_) => Err(GenerateError::ResidualTempName {
                function: function.index(),
                name: name.clone(),
            }),
            _ => {
                let function_names = self
                    .names
                    .function(function)
                    .ok_or_else(|| GenerateError::missing_function_names(function))?;
                let text = match name {
                    AstNameRef::Param(id) => function_names
                        .params
                        .get(id.index())
                        .map(|info| info.text.clone()),
                    AstNameRef::Local(id) => function_names
                        .locals
                        .get(id.index())
                        .map(|info| info.text.clone()),
                    AstNameRef::SyntheticLocal(id) => function_names
                        .synthetic_locals
                        .get(id)
                        .map(|info| info.text.clone()),
                    AstNameRef::Upvalue(id) => function_names
                        .upvalues
                        .get(id.index())
                        .map(|info| info.text.clone()),
                    AstNameRef::Global(_) | AstNameRef::Temp(_) => unreachable!(),
                };
                text.ok_or_else(|| GenerateError::MissingName {
                    function: function.index(),
                    name: name.clone(),
                })
            }
        }
    }

    fn resolve_binding_ref(
        &self,
        function: HirProtoRef,
        binding: &AstBindingRef,
    ) -> Result<String, GenerateError> {
        match binding {
            AstBindingRef::Temp(_) => Err(GenerateError::ResidualTempBinding {
                function: function.index(),
                binding: *binding,
            }),
            _ => {
                let function_names = self
                    .names
                    .function(function)
                    .ok_or_else(|| GenerateError::missing_function_names(function))?;
                let text = match binding {
                    AstBindingRef::Local(id) => function_names
                        .locals
                        .get(id.index())
                        .map(|info| info.text.clone()),
                    AstBindingRef::SyntheticLocal(id) => function_names
                        .synthetic_locals
                        .get(id)
                        .map(|info| info.text.clone()),
                    AstBindingRef::Temp(_) => unreachable!(),
                };
                text.ok_or_else(|| GenerateError::MissingBindingName {
                    function: function.index(),
                    binding: *binding,
                })
            }
        }
    }
}

fn maybe_parenthesize(
    doc: Doc,
    expr_prec: u8,
    parent_prec: u8,
    side: ExprSide,
    assoc: Assoc,
) -> Doc {
    let needs_parens = if expr_prec < parent_prec {
        true
    } else if expr_prec > parent_prec {
        false
    } else {
        match assoc {
            Assoc::Left => matches!(side, ExprSide::Right),
            Assoc::Right => matches!(side, ExprSide::Left),
            Assoc::Non => !matches!(side, ExprSide::Standalone),
        }
    };
    if needs_parens {
        Doc::concat([Doc::text("("), doc, Doc::text(")")])
    } else {
        doc
    }
}

fn binary_meta(op: crate::ast::AstBinaryOpKind) -> (u8, Assoc, &'static str) {
    use crate::ast::AstBinaryOpKind as Op;

    match op {
        Op::Add => (PREC_ADD, Assoc::Left, "+"),
        Op::Sub => (PREC_ADD, Assoc::Left, "-"),
        Op::Mul => (PREC_MUL, Assoc::Left, "*"),
        Op::Div => (PREC_MUL, Assoc::Left, "/"),
        Op::FloorDiv => (PREC_MUL, Assoc::Left, "//"),
        Op::Mod => (PREC_MUL, Assoc::Left, "%"),
        Op::Pow => (PREC_POW, Assoc::Right, "^"),
        Op::BitAnd => (PREC_BIT_AND, Assoc::Left, "&"),
        Op::BitOr => (PREC_BIT_OR, Assoc::Left, "|"),
        Op::BitXor => (PREC_BIT_XOR, Assoc::Left, "~"),
        Op::Shl => (PREC_SHIFT, Assoc::Left, "<<"),
        Op::Shr => (PREC_SHIFT, Assoc::Left, ">>"),
        Op::Concat => (PREC_CONCAT, Assoc::Right, ".."),
        Op::Eq => (PREC_COMPARE, Assoc::Non, "=="),
        Op::Lt => (PREC_COMPARE, Assoc::Non, "<"),
        Op::Le => (PREC_COMPARE, Assoc::Non, "<="),
    }
}

fn common_global_attr(bindings: &[AstGlobalBinding]) -> Option<AstGlobalAttr> {
    let first = bindings
        .first()
        .map(|binding| binding.attr)
        .unwrap_or(AstGlobalAttr::None);
    bindings
        .iter()
        .all(|binding| binding.attr == first)
        .then_some(first)
}

fn format_label_name(label: crate::ast::AstLabelId) -> String {
    format!("L{}", label.index())
}

fn format_number(value: f64) -> String {
    if value.is_nan() {
        return "(0/0)".to_owned();
    }
    if value.is_infinite() {
        return if value.is_sign_negative() {
            "(-1/0)".to_owned()
        } else {
            "(1/0)".to_owned()
        };
    }
    value.to_string()
}

fn format_complex_literal(real: f64, imag: f64) -> String {
    if real == 0.0 {
        return format!("{}i", format_number(imag));
    }
    let imag_abs = format_number(imag.abs());
    let imag_sign = if imag.is_sign_negative() { "-" } else { "+" };
    format!("({} {} {}i)", format_number(real), imag_sign, imag_abs)
}

fn format_string_literal(value: &str, quote_style: QuoteStyle) -> String {
    let candidates = match quote_style {
        QuoteStyle::PreferDouble => ['"', '\''],
        QuoteStyle::PreferSingle => ['\'', '"'],
        QuoteStyle::MinEscape => ['"', '\''],
    };
    let preferred = if matches!(quote_style, QuoteStyle::MinEscape) {
        if escape_cost(value, '"') <= escape_cost(value, '\'') {
            '"'
        } else {
            '\''
        }
    } else {
        candidates[0]
    };
    let mut rendered = String::new();
    rendered.push(preferred);
    for ch in value.chars() {
        match ch {
            '\n' => rendered.push_str("\\n"),
            '\r' => rendered.push_str("\\r"),
            '\t' => rendered.push_str("\\t"),
            '\\' => rendered.push_str("\\\\"),
            c if c == preferred => {
                rendered.push('\\');
                rendered.push(c);
            }
            c if c.is_control() => {
                rendered.push_str(&format!("\\{:03}", c as u32));
            }
            c => rendered.push(c),
        }
    }
    rendered.push(preferred);
    rendered
}

fn escape_cost(value: &str, quote: char) -> usize {
    value
        .chars()
        .map(|ch| match ch {
            '\n' | '\r' | '\t' | '\\' => 2,
            c if c == quote => 2,
            c if c.is_control() => 4,
            _ => 1,
        })
        .sum()
}
