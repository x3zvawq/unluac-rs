//! 这个子模块负责把 AST 语句序列化成目标 Lua 源码片段。
//!
//! 它依赖 AST build/Readability/Naming 已经把语句形状和名字准备好，只负责逐类发射，
//! 不会在这里补猜缺失的 global/function sugar。
//! 例如：`AstStmt::GlobalDecl` 只有 AST 上确实存在时才会在这里输出对应声明。

use crate::ast::{
    AstAssign, AstBlock, AstCallStmt, AstFunctionDecl, AstGenericFor, AstGlobalDecl, AstIf,
    AstLabel, AstLocalDecl, AstLocalFunctionDecl, AstNumericFor, AstRepeat, AstReturn, AstStmt,
    AstWhile,
};
use crate::generate::doc::Doc;
use crate::hir::HirProtoRef;

use super::super::error::GenerateError;
use super::syntax::format_label_name;
use super::{Emitter, ExprSide};

impl<'a> Emitter<'a> {
    pub(super) fn emit_stmt(
        &self,
        stmt: &AstStmt,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
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

    fn emit_global_decl(
        &self,
        global_decl: &AstGlobalDecl,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        // Generate 只序列化 AST 上已经存在的 global decl，不替前层补猜缺失声明。
        if !self.target.caps.global_decl {
            return Err(GenerateError::UnsupportedFeature {
                dialect: self.target.version,
                feature: "global",
            });
        }

        let attr = super::syntax::common_global_attr(global_decl.bindings.as_slice()).ok_or(
            GenerateError::MixedGlobalAttrs {
                function: function.index(),
            },
        )?;
        if matches!(attr, crate::ast::AstGlobalAttr::Const) && !self.target.caps.global_const {
            return Err(GenerateError::UnsupportedFeature {
                dialect: self.target.version,
                feature: "global<const>",
            });
        }

        let keyword = match attr {
            crate::ast::AstGlobalAttr::None => "global",
            crate::ast::AstGlobalAttr::Const => "global<const>",
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
        let binding = self
            .names
            .resolve_binding_ref(function, &numeric_for.binding)?;
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
            .map(|binding| {
                self.names
                    .resolve_binding_ref(function, binding)
                    .map(Doc::text)
            })
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
            matches!(
                function_decl.target,
                crate::ast::AstFunctionName::Method(_, _)
            ),
        )?;
        self.emit_function_with_header_and_params(&function_decl.func, header, params)
    }

    fn emit_local_function_decl(
        &self,
        local_function_decl: &AstLocalFunctionDecl,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        let name = self
            .names
            .resolve_binding_ref(function, &local_function_decl.name)?;
        let header = Doc::concat([Doc::text("local function "), Doc::text(name)]);
        self.emit_function_with_header(&local_function_decl.func, header)
    }

    fn emit_value_list(
        &self,
        values: &[crate::ast::AstExpr],
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        let docs = values
            .iter()
            .map(|expr| self.emit_expr(expr, function, 0, ExprSide::Standalone))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Doc::join(docs, Doc::text(", ")))
    }

    pub(super) fn emit_parenthesized_list(&self, items: Vec<Doc>) -> Doc {
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

    pub(super) fn emit_indented_body(&self, block: &AstBlock, body: Doc) -> Doc {
        if block.stmts.is_empty() {
            Doc::line()
        } else {
            self.emit_indented_body_nonempty(body)
        }
    }

    fn emit_indented_body_nonempty(&self, body: Doc) -> Doc {
        Doc::indent(Doc::concat([Doc::line(), body]))
    }
}
