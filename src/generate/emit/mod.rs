//! AST -> Doc lowering。
//!
//! 这里采用外部 emitter，而不是把“生成字符串”的方法塞回 AST 节点本身。
//! 这样 AST 仍保持纯语法数据，Generate 只在这一层处理名字解析、括号优先级和布局意图。

mod expr;
mod names;
mod stmt;
mod syntax;

use crate::ast::{AstBlock, AstModule, AstTargetDialect};
use crate::generate::doc::Doc;
use crate::hir::HirProtoRef;
use crate::naming::NameMap;
use names::NameResolver;

use super::common::{GenerateOptions, GeneratedChunk};
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
        names: NameResolver::new(names),
        target,
        options,
    };
    let doc = emitter.emit_module(module)?;
    Ok(GeneratedChunk {
        source: render_doc(&doc, options),
    })
}

struct Emitter<'a> {
    names: NameResolver<'a>,
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
}
