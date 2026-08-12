//! AST -> Doc lowering。
//!
//! 这里采用外部 emitter，而不是把“生成字符串”的方法塞回 AST 节点本身。
//! 这样 AST 仍保持纯语法数据，Generate 只在这一层处理名字解析、括号优先级、
//! 布局意图，以及基于稳定 metadata 的可选注释输出。

mod expr;
mod names;
mod stmt;
mod syntax;

use crate::ast::{AstBlock, AstFeature, AstModule, AstTargetDialect, collect_ast_features};
use crate::decompile::{DecompileContext, DecompileError, DecompileState};
use crate::generate::doc::Doc;
use crate::hir::HirProtoRef;
use names::NameResolver;

use super::common::{
    GenerateCommentMetadata, GenerateMode, GenerateOptions, GeneratedChunk, GeneratedChunkKind,
};
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
    /// 完全关联：`a op (b op c)` == `(a op b) op c`，同优先级时
    /// 两侧都不需要括号。
    Full,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExprSide {
    Standalone,
    Left,
    Right,
}

/// Generate 对外入口。
pub(crate) fn generate_chunk(
    state: &mut DecompileState,
    context: &DecompileContext<'_>,
) -> Result<(), DecompileError> {
    let options = &context.options.generate;
    let hir = state.require_hir()?;
    let module = state.require_readability()?;
    let names = state.require_naming()?;
    let metadata = if options.comment {
        Some(GenerateCommentMetadata::from_hir(
            hir,
            context.options.parse.string_encoding.as_str(),
        ))
    } else {
        None
    };
    let (features, has_errors) = collect_ast_features(module);
    let unsupported = features
        .into_iter()
        .filter(|feature| !context.requested_target.supports_feature(*feature))
        .collect::<Vec<_>>();
    let diagnostic = has_errors || !unsupported.is_empty();
    let generated = {
        let emitter = Emitter {
            names: NameResolver::new(names),
            target: context.requested_target,
            metadata: metadata.as_ref(),
            options,
        };
        let mut doc = emitter.emit_module(module)?;
        if diagnostic {
            let features = format_ast_features(&unsupported);
            let reason = match (unsupported.is_empty(), has_errors) {
                (false, true) => format!("unsupported {features} and recovery errors"),
                (false, false) => format!("unsupported {features}"),
                (true, true) => "recovery errors".to_owned(),
                (true, false) => unreachable!("diagnostic output must have a reason"),
            };
            doc = Doc::concat([
                Doc::text(format!(
                    "-- [unluac error] diagnostic pseudocode: {reason}; output may not recompile or preserve behavior"
                )),
                Doc::line(),
                Doc::line(),
                doc,
            ]);
        }
        GeneratedChunk {
            dialect: context.requested_target.version,
            kind: if diagnostic {
                GeneratedChunkKind::DiagnosticPseudocode
            } else {
                GeneratedChunkKind::Source
            },
            source: render_doc(&doc, options),
        }
    };
    state.generated = Some(generated);
    Ok(())
}

fn format_ast_features(features: &[AstFeature]) -> String {
    features
        .iter()
        .map(|feature| <&'static str>::from(*feature))
        .collect::<Vec<_>>()
        .join(", ")
}

struct Emitter<'a> {
    names: NameResolver<'a>,
    target: AstTargetDialect,
    metadata: Option<&'a GenerateCommentMetadata>,
    options: &'a GenerateOptions,
}

impl<'a> Emitter<'a> {
    fn allows_feature(&self, feature: AstFeature) -> bool {
        self.target.supports_feature(feature)
            || (self.options.mode == GenerateMode::Permissive && feature == AstFeature::GotoLabel)
    }

    fn emit_module(&self, module: &AstModule) -> Result<Doc, GenerateError> {
        let body = self.emit_block(&module.body, module.entry_function)?;
        let Some(header) = self.emit_chunk_comment() else {
            return Ok(body);
        };

        if module.body.stmts.is_empty() {
            return Ok(header);
        }

        Ok(Doc::concat([header, Doc::line(), Doc::line(), body]))
    }

    fn emit_block(&self, block: &AstBlock, function: HirProtoRef) -> Result<Doc, GenerateError> {
        let docs = block
            .stmts
            .iter()
            .map(|stmt| self.emit_stmt(stmt, function))
            .collect::<Result<Vec<_>, _>>()?;
        let Some((first, rest)) = docs.split_first() else {
            return Ok(Doc::concat([]));
        };

        let mut parts = vec![first.clone()];
        for (index, doc) in rest.iter().enumerate() {
            parts.push(self.emit_stmt_separator(&block.stmts[index], &block.stmts[index + 1]));
            parts.push(doc.clone());
        }
        Ok(Doc::concat(parts))
    }

    fn emit_chunk_comment(&self) -> Option<Doc> {
        if !self.options.comment {
            return None;
        }

        let encoding = self
            .metadata
            .map(|metadata| metadata.chunk.encoding.as_str())
            .unwrap_or("unknown");
        let mut comments = Vec::with_capacity(4);
        if let Some(file_name) = self
            .metadata
            .and_then(|metadata| metadata.chunk.file_name.as_deref())
        {
            comments.push(Doc::text(format!(
                "-- file: {}",
                sanitize_comment_text(file_name)
            )));
        }
        comments.extend([
            Doc::text(format!(
                "-- dialect: {}",
                <&'static str>::from(self.target.version)
            )),
            Doc::text(format!("-- encoding: {encoding}")),
            Doc::text("-- decompiled by unluac-rs (https://github.com/x3zvawq/unluac-rs)"),
        ]);
        Some(Doc::join(comments, Doc::line()))
    }

    fn emit_function_comment(&self, function: HirProtoRef) -> Option<Doc> {
        if !self.options.comment {
            return None;
        }

        let metadata = self.metadata?.function(function)?;
        let mut proto_meta = format!(
            "-- proto#{} params={} locals={} upvalues={} vararg={}",
            metadata.function.index(),
            metadata.signature.num_params,
            metadata.local_count,
            metadata.upvalue_count,
            metadata.signature.is_vararg,
        );
        if metadata.signature.named_vararg_table {
            proto_meta.push_str(" named_vararg=true");
        }
        if metadata.signature.has_vararg_param_reg {
            proto_meta.push_str(" vararg_reg=true");
        }
        if let Some(source) = metadata.source.as_deref() {
            proto_meta.push_str(" source=");
            proto_meta.push_str(&sanitize_comment_text(source));
        }

        let mut comments = Vec::with_capacity(2);
        if metadata.line_range.defined_start != 0 || metadata.line_range.defined_end != 0 {
            comments.push(Doc::text(format!(
                "-- line {}-{}",
                metadata.line_range.defined_start, metadata.line_range.defined_end
            )));
        }
        comments.push(Doc::text(proto_meta));
        Some(Doc::join(comments, Doc::line()))
    }

    fn emit_stmt_separator(&self, prev: &crate::ast::AstStmt, next: &crate::ast::AstStmt) -> Doc {
        if stmt_can_absorb_call_suffix(prev) && stmt_starts_with_parenthesized_call(next) {
            Doc::concat([Doc::text(";"), Doc::line()])
        } else if is_function_stmt(prev) || is_function_stmt(next) {
            Doc::concat([Doc::line(), Doc::line()])
        } else {
            Doc::line()
        }
    }
}

fn sanitize_comment_text(text: &str) -> String {
    text.replace("\r\n", "\\n")
        .replace(['\n', '\r'], "\\n")
        .replace('\t', "\\t")
}

fn is_function_stmt(stmt: &crate::ast::AstStmt) -> bool {
    matches!(
        stmt,
        crate::ast::AstStmt::FunctionDecl(_) | crate::ast::AstStmt::LocalFunctionDecl(_)
    )
}

fn stmt_can_absorb_call_suffix(stmt: &crate::ast::AstStmt) -> bool {
    match stmt {
        crate::ast::AstStmt::LocalDecl(decl) => !decl.values.is_empty(),
        crate::ast::AstStmt::GlobalDecl(decl) => !decl.values.is_empty(),
        crate::ast::AstStmt::Assign(_) | crate::ast::AstStmt::CallStmt(_) => true,
        crate::ast::AstStmt::Return(ret) => !ret.values.is_empty(),
        _ => false,
    }
}

fn stmt_starts_with_parenthesized_call(stmt: &crate::ast::AstStmt) -> bool {
    let crate::ast::AstStmt::CallStmt(call) = stmt else {
        return false;
    };
    match &call.call {
        crate::ast::AstCallKind::Call(call) => prefix_expr_starts_with_parenthesis(&call.callee),
        crate::ast::AstCallKind::MethodCall(call) => {
            prefix_expr_starts_with_parenthesis(&call.receiver)
        }
    }
}

fn prefix_expr_starts_with_parenthesis(expr: &crate::ast::AstExpr) -> bool {
    match expr {
        crate::ast::AstExpr::Var(_) => false,
        crate::ast::AstExpr::FieldAccess(access) => {
            prefix_expr_starts_with_parenthesis(&access.base)
        }
        crate::ast::AstExpr::IndexAccess(access) => {
            prefix_expr_starts_with_parenthesis(&access.base)
        }
        crate::ast::AstExpr::Call(call) => prefix_expr_starts_with_parenthesis(&call.callee),
        crate::ast::AstExpr::MethodCall(call) => {
            prefix_expr_starts_with_parenthesis(&call.receiver)
        }
        _ => true,
    }
}
