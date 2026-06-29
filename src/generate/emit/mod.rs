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
use crate::generate::GenerateMode;
use crate::generate::doc::Doc;
use crate::hir::HirProtoRef;
use names::NameResolver;

use super::common::{GenerateCommentMetadata, GenerateOptions, GeneratedChunk};
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
    let options = context.options.generate;
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
    let generated = {
        let emitter = Emitter {
            names: NameResolver::new(names),
            target: context.requested_target,
            metadata: metadata.as_ref(),
            options,
        };
        let doc = emitter.emit_module(module)?;
        GeneratedChunk {
            dialect: context.requested_target.version,
            source: render_doc(&doc, options),
            warnings: permissive_output_warnings(module, context.requested_target, options.mode),
        }
    };
    state.generated = Some(generated);
    Ok(())
}

fn permissive_output_warnings(
    module: &AstModule,
    target: AstTargetDialect,
    mode: GenerateMode,
) -> Vec<String> {
    if mode != GenerateMode::Permissive {
        return Vec::new();
    }

    let unsupported = collect_ast_features(module)
        .into_iter()
        .filter(|feature| !target.supports_feature(*feature))
        .collect::<Vec<_>>();
    if unsupported.is_empty() {
        return Vec::new();
    }

    vec![format!(
        "requested target dialect `{}` does not support feature(s) {}; emitting permissive output.",
        target.version,
        format_ast_features(&unsupported)
    )]
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
    options: GenerateOptions,
}

impl<'a> Emitter<'a> {
    fn allows_feature(&self, feature: AstFeature) -> bool {
        self.target.supports_feature(feature) || self.options.mode != GenerateMode::Strict
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

        let file_name = self
            .metadata
            .and_then(|metadata| metadata.chunk.file_name.as_deref())
            .map(sanitize_comment_text)
            .unwrap_or_else(|| "<unknown>".to_owned());
        let encoding = self
            .metadata
            .map(|metadata| metadata.chunk.encoding.as_str())
            .unwrap_or("unknown");
        Some(Doc::join(
            [
                Doc::text(format!("-- file: {file_name}")),
                Doc::text(format!(
                    "-- dialect: {}",
                    <&'static str>::from(self.target.version)
                )),
                Doc::text(format!("-- encoding: {encoding}")),
                Doc::text("-- decompiled by unluac-rs"),
            ],
            Doc::line(),
        ))
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

        Some(Doc::join(
            [
                Doc::text(format!(
                    "-- line {}-{}",
                    metadata.line_range.defined_start, metadata.line_range.defined_end
                )),
                Doc::text(proto_meta),
            ],
            Doc::line(),
        ))
    }

    fn emit_stmt_separator(&self, prev: &crate::ast::AstStmt, next: &crate::ast::AstStmt) -> Doc {
        if is_function_stmt(prev) || is_function_stmt(next) {
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
