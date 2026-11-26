//! AST -> Doc lowering。
//!
//! 这里采用外部 emitter，而不是把“生成字符串”的方法塞回 AST 节点本身。
//! 这样 AST 仍保持纯语法数据，Generate 只在这一层处理名字解析、括号优先级、
//! 布局意图，以及基于稳定 metadata 的可选注释输出。

mod expr;
mod names;
mod stmt;
mod syntax;

use crate::ast::{
    AstBlock, AstExpr, AstFeature, AstFunctionDecl, AstFunctionExpr, AstLocalFunctionDecl,
    AstModule, AstStmt, AstTargetDialect, ProtoId, collect_ast_features,
};
use crate::decompile::{DecompileContext, DecompileError, DecompileResult, DecompileState};
use crate::generate::doc::Doc;
use names::NameResolver;

use super::common::{
    CommentStyle, GenerateCommentMetadata, GenerateMode, GenerateOptions, GeneratedChunk,
    GeneratedChunkKind,
};
use super::error::GenerateError;
use super::render::{render_doc, render_doc_with_proto_spans};

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
    let number_is_f32 = state
        .require_raw_chunk()?
        .header
        .puc_lua_layout()
        .is_some_and(|layout| !layout.integral_number && layout.number_size == 4);
    let module = state.require_ast()?;
    let names = state.require_naming()?;
    let metadata = if options.comment.is_enabled() {
        Some(GenerateCommentMetadata::from_ast(
            module,
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
            number_is_f32,
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
                (true, false) => String::new(),
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
        let (source, mut proto_line_spans) = render_doc_with_proto_spans(&doc, options);
        let total_lines = source.lines().count().max(1);
        proto_line_spans
            .entry(module.entry_function.index())
            .or_insert((1, total_lines));
        GeneratedChunk {
            dialect: context.requested_target.version,
            kind: if diagnostic {
                GeneratedChunkKind::DiagnosticPseudocode
            } else {
                GeneratedChunkKind::Source
            },
            source,
            proto_line_spans,
        }
    };
    state.generated = Some(generated);
    Ok(())
}

/// 收集 AST 中包含 `AstStmt::Error` 或 `AstExpr::Error` 恢复占位符的 proto 序号列表（升序去重）。
pub fn collect_error_protos(module: &AstModule) -> Vec<usize> {
    let mut protos = std::collections::BTreeSet::new();
    collect_error_protos_in_block(&module.body, module.entry_function, &mut protos);
    protos.into_iter().collect()
}

fn collect_error_protos_in_block(
    block: &AstBlock,
    function: ProtoId,
    out: &mut std::collections::BTreeSet<usize>,
) {
    for stmt in &block.stmts {
        match stmt {
            AstStmt::Error(_) => {
                out.insert(function.index());
            }
            AstStmt::LocalDecl(d) => {
                for v in &d.values {
                    collect_error_protos_in_expr(v, function, out);
                }
            }
            AstStmt::GlobalDecl(d) => {
                for v in &d.values {
                    collect_error_protos_in_expr(v, function, out);
                }
            }
            AstStmt::Assign(a) => {
                for t in &a.targets {
                    match t {
                        crate::ast::AstLValue::Name(_) => {}
                        crate::ast::AstLValue::FieldAccess(f) => {
                            collect_error_protos_in_expr(&f.base, function, out);
                        }
                        crate::ast::AstLValue::IndexAccess(ia) => {
                            collect_error_protos_in_expr(&ia.base, function, out);
                            collect_error_protos_in_expr(&ia.index, function, out);
                        }
                    }
                }
                for v in &a.values {
                    collect_error_protos_in_expr(v, function, out);
                }
            }
            AstStmt::CallStmt(c) => match &c.call {
                crate::ast::AstCallKind::Call(call) => {
                    collect_error_protos_in_expr(&call.callee, function, out);
                    for a in &call.args {
                        collect_error_protos_in_expr(a, function, out);
                    }
                }
                crate::ast::AstCallKind::MethodCall(m) => {
                    collect_error_protos_in_expr(&m.receiver, function, out);
                    for a in &m.args {
                        collect_error_protos_in_expr(a, function, out);
                    }
                }
            },
            AstStmt::Return(r) => {
                for v in &r.values {
                    collect_error_protos_in_expr(v, function, out);
                }
            }
            AstStmt::If(i) => {
                collect_error_protos_in_expr(&i.cond, function, out);
                collect_error_protos_in_block(&i.then_block, function, out);
                if let Some(eb) = &i.else_block {
                    collect_error_protos_in_block(eb, function, out);
                }
            }
            AstStmt::While(w) => {
                collect_error_protos_in_expr(&w.cond, function, out);
                collect_error_protos_in_block(&w.body, function, out);
            }
            AstStmt::Repeat(r) => {
                collect_error_protos_in_block(&r.body, function, out);
                collect_error_protos_in_expr(&r.cond, function, out);
            }
            AstStmt::NumericFor(nf) => {
                collect_error_protos_in_expr(&nf.start, function, out);
                collect_error_protos_in_expr(&nf.limit, function, out);
                collect_error_protos_in_expr(&nf.step, function, out);
                collect_error_protos_in_block(&nf.body, function, out);
            }
            AstStmt::GenericFor(gf) => {
                for e in &gf.iterator {
                    collect_error_protos_in_expr(e, function, out);
                }
                collect_error_protos_in_block(&gf.body, function, out);
            }
            AstStmt::DoBlock(b) => collect_error_protos_in_block(b, function, out),
            AstStmt::FunctionDecl(decl) => {
                collect_error_protos_in_block(&decl.func.body, decl.func.function, out);
            }
            AstStmt::LocalFunctionDecl(decl) => {
                collect_error_protos_in_block(&decl.func.body, decl.func.function, out);
            }
            AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => {}
        }
    }
}

fn collect_error_protos_in_expr(
    expr: &AstExpr,
    function: ProtoId,
    out: &mut std::collections::BTreeSet<usize>,
) {
    match expr {
        AstExpr::Error(_) => {
            out.insert(function.index());
        }
        AstExpr::FunctionExpr(func) => {
            collect_error_protos_in_block(&func.body, func.function, out);
        }
        AstExpr::Unary(u) => collect_error_protos_in_expr(&u.expr, function, out),
        AstExpr::Binary(b) => {
            collect_error_protos_in_expr(&b.lhs, function, out);
            collect_error_protos_in_expr(&b.rhs, function, out);
        }
        AstExpr::LogicalAnd(l) | AstExpr::LogicalOr(l) => {
            collect_error_protos_in_expr(&l.lhs, function, out);
            collect_error_protos_in_expr(&l.rhs, function, out);
        }
        AstExpr::FieldAccess(f) => collect_error_protos_in_expr(&f.base, function, out),
        AstExpr::IndexAccess(ia) => {
            collect_error_protos_in_expr(&ia.base, function, out);
            collect_error_protos_in_expr(&ia.index, function, out);
        }
        AstExpr::Call(c) => {
            collect_error_protos_in_expr(&c.callee, function, out);
            for a in &c.args {
                collect_error_protos_in_expr(a, function, out);
            }
        }
        AstExpr::MethodCall(m) => {
            collect_error_protos_in_expr(&m.receiver, function, out);
            for a in &m.args {
                collect_error_protos_in_expr(a, function, out);
            }
        }
        AstExpr::TableConstructor(t) => {
            for field in &t.fields {
                match field {
                    crate::ast::AstTableField::Array(e) => {
                        collect_error_protos_in_expr(e, function, out);
                    }
                    crate::ast::AstTableField::Record(r) => {
                        if let crate::ast::AstTableKey::Expr(k) = &r.key {
                            collect_error_protos_in_expr(k, function, out);
                        }
                        collect_error_protos_in_expr(&r.value, function, out);
                    }
                }
            }
        }
        AstExpr::SingleValue(inner) => collect_error_protos_in_expr(inner, function, out),
        AstExpr::IfExpr(ie) => {
            collect_error_protos_in_expr(&ie.cond, function, out);
            collect_error_protos_in_expr(&ie.then_expr, function, out);
            collect_error_protos_in_expr(&ie.else_expr, function, out);
        }
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Complex { .. }
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Vector(_)
        | AstExpr::Var(_)
        | AstExpr::VarArg => {}
    }
}

enum FoundProtoNode<'a> {
    FunctionDecl(&'a AstFunctionDecl, ProtoId),
    LocalFunctionDecl(&'a AstLocalFunctionDecl, ProtoId),
    FunctionExpr(&'a AstFunctionExpr),
}

/// 仅针对已反编译结果中的单个 `proto_id` 生成独立可读源码，完整保留模块级命名与上值解析。
pub fn generate_proto_source(
    result: &DecompileResult,
    proto_id: usize,
    options: &GenerateOptions,
    encoding: &str,
) -> Result<Option<String>, GenerateError> {
    let Some(module) = result.state.ast.as_ref() else {
        return Ok(None);
    };
    let Some(names) = result.state.naming.as_ref() else {
        return Ok(None);
    };
    if proto_id >= module.protos.len() {
        return Ok(None);
    }
    if proto_id == module.entry_function.index() {
        return Ok(result.state.generated.as_ref().map(|g| g.source.clone()));
    }
    let Some(found) = find_proto_node_in_block(&module.body, module.entry_function, ProtoId(proto_id))
    else {
        return Ok(None);
    };
    let number_is_f32 = result
        .state
        .raw_chunk
        .as_ref()
        .and_then(|c| c.header.puc_lua_layout())
        .is_some_and(|layout| !layout.integral_number && layout.number_size == 4);
    let target = AstTargetDialect::new(result.state.dialect);
    let metadata = if options.comment.is_enabled() {
        Some(GenerateCommentMetadata::from_ast(module, encoding))
    } else {
        None
    };
    let emitter = Emitter {
        number_is_f32,
        names: NameResolver::new(names),
        target,
        metadata: metadata.as_ref(),
        options,
    };
    let body_doc = match found {
        FoundProtoNode::FunctionDecl(decl, parent) => emitter.emit_function_decl(decl, parent)?,
        FoundProtoNode::LocalFunctionDecl(decl, parent) => {
            emitter.emit_local_function_decl(decl, parent)?
        }
        FoundProtoNode::FunctionExpr(func) => {
            emitter.emit_function_with_header(func, Doc::text("function"))?
        }
    };
    let doc = if options.comment.is_enabled() {
        let header = Doc::text(format!(
            "-- proto#{} | dialect: {} | decompiled by unluac-rs v{}",
            proto_id,
            <&'static str>::from(target.version),
            env!("CARGO_PKG_VERSION"),
        ));
        Doc::concat([header, Doc::line(), Doc::line(), body_doc])
    } else {
        body_doc
    };
    Ok(Some(render_doc(&doc, options)))
}

fn find_proto_node_in_block<'a>(
    block: &'a AstBlock,
    parent: ProtoId,
    target: ProtoId,
) -> Option<FoundProtoNode<'a>> {
    for stmt in &block.stmts {
        match stmt {
            AstStmt::FunctionDecl(decl) => {
                if decl.func.function == target {
                    return Some(FoundProtoNode::FunctionDecl(decl, parent));
                }
                if let Some(found) =
                    find_proto_node_in_block(&decl.func.body, decl.func.function, target)
                {
                    return Some(found);
                }
            }
            AstStmt::LocalFunctionDecl(decl) => {
                if decl.func.function == target {
                    return Some(FoundProtoNode::LocalFunctionDecl(decl, parent));
                }
                if let Some(found) =
                    find_proto_node_in_block(&decl.func.body, decl.func.function, target)
                {
                    return Some(found);
                }
            }
            AstStmt::LocalDecl(d) => {
                for v in &d.values {
                    if let Some(found) = find_proto_node_in_expr(v, target) {
                        return Some(found);
                    }
                }
            }
            AstStmt::GlobalDecl(d) => {
                for v in &d.values {
                    if let Some(found) = find_proto_node_in_expr(v, target) {
                        return Some(found);
                    }
                }
            }
            AstStmt::Assign(a) => {
                for t in &a.targets {
                    match t {
                        crate::ast::AstLValue::Name(_) => {}
                        crate::ast::AstLValue::FieldAccess(f) => {
                            if let Some(found) = find_proto_node_in_expr(&f.base, target) {
                                return Some(found);
                            }
                        }
                        crate::ast::AstLValue::IndexAccess(ia) => {
                            if let Some(found) = find_proto_node_in_expr(&ia.base, target)
                                .or_else(|| find_proto_node_in_expr(&ia.index, target))
                            {
                                return Some(found);
                            }
                        }
                    }
                }
                for v in &a.values {
                    if let Some(found) = find_proto_node_in_expr(v, target) {
                        return Some(found);
                    }
                }
            }
            AstStmt::CallStmt(c) => match &c.call {
                crate::ast::AstCallKind::Call(call) => {
                    if let Some(found) = find_proto_node_in_expr(&call.callee, target) {
                        return Some(found);
                    }
                    for a in &call.args {
                        if let Some(found) = find_proto_node_in_expr(a, target) {
                            return Some(found);
                        }
                    }
                }
                crate::ast::AstCallKind::MethodCall(m) => {
                    if let Some(found) = find_proto_node_in_expr(&m.receiver, target) {
                        return Some(found);
                    }
                    for a in &m.args {
                        if let Some(found) = find_proto_node_in_expr(a, target) {
                            return Some(found);
                        }
                    }
                }
            },
            AstStmt::Return(r) => {
                for v in &r.values {
                    if let Some(found) = find_proto_node_in_expr(v, target) {
                        return Some(found);
                    }
                }
            }
            AstStmt::If(i) => {
                if let Some(found) = find_proto_node_in_expr(&i.cond, target)
                    .or_else(|| find_proto_node_in_block(&i.then_block, parent, target))
                {
                    return Some(found);
                }
                if let Some(eb) = &i.else_block
                    && let Some(found) = find_proto_node_in_block(eb, parent, target)
                {
                    return Some(found);
                }
            }
            AstStmt::While(w) => {
                if let Some(found) = find_proto_node_in_expr(&w.cond, target)
                    .or_else(|| find_proto_node_in_block(&w.body, parent, target))
                {
                    return Some(found);
                }
            }
            AstStmt::Repeat(r) => {
                if let Some(found) = find_proto_node_in_block(&r.body, parent, target)
                    .or_else(|| find_proto_node_in_expr(&r.cond, target))
                {
                    return Some(found);
                }
            }
            AstStmt::NumericFor(nf) => {
                if let Some(found) = find_proto_node_in_expr(&nf.start, target)
                    .or_else(|| find_proto_node_in_expr(&nf.limit, target))
                    .or_else(|| find_proto_node_in_expr(&nf.step, target))
                    .or_else(|| find_proto_node_in_block(&nf.body, parent, target))
                {
                    return Some(found);
                }
            }
            AstStmt::GenericFor(gf) => {
                for e in &gf.iterator {
                    if let Some(found) = find_proto_node_in_expr(e, target) {
                        return Some(found);
                    }
                }
                if let Some(found) = find_proto_node_in_block(&gf.body, parent, target) {
                    return Some(found);
                }
            }
            AstStmt::DoBlock(b) => {
                if let Some(found) = find_proto_node_in_block(b, parent, target) {
                    return Some(found);
                }
            }
            AstStmt::Break
            | AstStmt::Continue
            | AstStmt::Goto(_)
            | AstStmt::Label(_)
            | AstStmt::Error(_) => {}
        }
    }
    None
}

fn find_proto_node_in_expr<'a>(expr: &'a AstExpr, target: ProtoId) -> Option<FoundProtoNode<'a>> {
    match expr {
        AstExpr::FunctionExpr(func) => {
            if func.function == target {
                return Some(FoundProtoNode::FunctionExpr(func));
            }
            find_proto_node_in_block(&func.body, func.function, target)
        }
        AstExpr::Unary(u) => find_proto_node_in_expr(&u.expr, target),
        AstExpr::Binary(b) => {
            find_proto_node_in_expr(&b.lhs, target).or_else(|| find_proto_node_in_expr(&b.rhs, target))
        }
        AstExpr::LogicalAnd(l) | AstExpr::LogicalOr(l) => {
            find_proto_node_in_expr(&l.lhs, target).or_else(|| find_proto_node_in_expr(&l.rhs, target))
        }
        AstExpr::FieldAccess(f) => find_proto_node_in_expr(&f.base, target),
        AstExpr::IndexAccess(ia) => find_proto_node_in_expr(&ia.base, target)
            .or_else(|| find_proto_node_in_expr(&ia.index, target)),
        AstExpr::Call(c) => {
            if let Some(found) = find_proto_node_in_expr(&c.callee, target) {
                return Some(found);
            }
            for a in &c.args {
                if let Some(found) = find_proto_node_in_expr(a, target) {
                    return Some(found);
                }
            }
            None
        }
        AstExpr::MethodCall(m) => {
            if let Some(found) = find_proto_node_in_expr(&m.receiver, target) {
                return Some(found);
            }
            for a in &m.args {
                if let Some(found) = find_proto_node_in_expr(a, target) {
                    return Some(found);
                }
            }
            None
        }
        AstExpr::TableConstructor(t) => {
            for field in &t.fields {
                match field {
                    crate::ast::AstTableField::Array(e) => {
                        if let Some(found) = find_proto_node_in_expr(e, target) {
                            return Some(found);
                        }
                    }
                    crate::ast::AstTableField::Record(r) => {
                        if let crate::ast::AstTableKey::Expr(k) = &r.key
                            && let Some(found) = find_proto_node_in_expr(k, target)
                        {
                            return Some(found);
                        }
                        if let Some(found) = find_proto_node_in_expr(&r.value, target) {
                            return Some(found);
                        }
                    }
                }
            }
            None
        }
        AstExpr::SingleValue(inner) => find_proto_node_in_expr(inner, target),
        AstExpr::IfExpr(ie) => find_proto_node_in_expr(&ie.cond, target)
            .or_else(|| find_proto_node_in_expr(&ie.then_expr, target))
            .or_else(|| find_proto_node_in_expr(&ie.else_expr, target)),
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Complex { .. }
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Vector(_)
        | AstExpr::Var(_)
        | AstExpr::VarArg
        | AstExpr::Error(_) => None,
    }
}

fn format_ast_features(features: &[AstFeature]) -> String {
    features
        .iter()
        .map(|feature| <&'static str>::from(*feature))
        .collect::<Vec<_>>()
        .join(", ")
}

struct Emitter<'a> {
    /// 数字模型来自原 chunk 的 header，与可关闭的展示 metadata 无关。
    number_is_f32: bool,
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

    fn emit_block(&self, block: &AstBlock, function: ProtoId) -> Result<Doc, GenerateError> {
        let mut docs = block
            .stmts
            .iter()
            .map(|stmt| self.emit_stmt(stmt, function));
        let Some(first) = docs.next().transpose()? else {
            return Ok(Doc::concat([]));
        };

        let mut parts = vec![first];
        for (index, doc) in docs.enumerate() {
            let doc = doc?;
            parts.push(self.emit_stmt_separator(&block.stmts[index], &block.stmts[index + 1]));
            parts.push(doc);
        }
        Ok(Doc::concat(parts))
    }

    fn emit_chunk_comment(&self) -> Option<Doc> {
        if !self.options.comment.is_enabled() {
            return None;
        }

        let encoding = self
            .metadata
            .map(|metadata| metadata.chunk.encoding.as_str())
            .unwrap_or("unknown");
        let mut comments = Vec::with_capacity(4);
        if let Some(file_name) = self
            .metadata
            .and_then(|metadata| metadata.chunk.file_name.as_ref())
        {
            let mut comment = String::from("-- file: ");
            push_comment_text(&mut comment, &file_name.display_text());
            comments.push(Doc::text(comment));
        }
        comments.extend([
            Doc::text(format!(
                "-- dialect: {}",
                <&'static str>::from(self.target.version)
            )),
            Doc::text(format!("-- encoding: {encoding}")),
            Doc::text(format!(
                "-- decompiled by unluac-rs v{} (https://github.com/x3zvawq/unluac-rs)",
                env!("CARGO_PKG_VERSION")
            )),
        ]);
        Some(Doc::join(comments, Doc::line()))
    }

    fn emit_function_comment(&self, function: ProtoId) -> Option<Doc> {
        let metadata = self.metadata?.function(function)?;
        match self.options.comment {
            CommentStyle::None => None,
            CommentStyle::Minimal => {
                let has_lines = metadata.line_range.defined_start != 0
                    || metadata.line_range.defined_end != 0;
                let distinct_source = metadata.source.as_ref().filter(|src| {
                    self.metadata
                        .and_then(|m| m.chunk.file_name.as_ref())
                        .is_none_or(|chunk_file| chunk_file != *src)
                });
                if !has_lines && distinct_source.is_none() {
                    return None;
                }
                let mut text = String::from("--");
                if let Some(source) = distinct_source {
                    text.push_str(" source=");
                    push_comment_text(&mut text, &source.display_text());
                }
                if has_lines {
                    text.push_str(&format!(
                        " lines={}-{}",
                        metadata.line_range.defined_start, metadata.line_range.defined_end
                    ));
                }
                Some(Doc::text(text))
            }
            CommentStyle::Full => {
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
                if let Some(source) = metadata.source.as_ref() {
                    proto_meta.push_str(" source=");
                    push_comment_text(&mut proto_meta, &source.display_text());
                }

                if metadata.line_range.defined_start != 0 || metadata.line_range.defined_end != 0 {
                    proto_meta.push_str(&format!(
                        " lines={}-{}",
                        metadata.line_range.defined_start, metadata.line_range.defined_end
                    ));
                }
                Some(Doc::text(proto_meta))
            }
        }
    }

    fn emit_stmt_separator(&self, prev: &crate::ast::AstStmt, next: &crate::ast::AstStmt) -> Doc {
        if stmt_can_absorb_call_suffix(prev) && stmt_starts_with_parenthesis(next) {
            Doc::concat([Doc::text(";"), Doc::line()])
        } else if is_function_stmt(prev) || is_function_stmt(next) {
            Doc::concat([Doc::line(), Doc::line()])
        } else {
            Doc::line()
        }
    }
}

fn push_comment_text(output: &mut String, text: &str) {
    output.reserve(text.len());
    let mut chars = text.chars().peekable();
    while let Some(ch) = chars.next() {
        match ch {
            '\r' => {
                chars.next_if_eq(&'\n');
                output.push_str("\\n");
            }
            '\n' => output.push_str("\\n"),
            '\t' => output.push_str("\\t"),
            _ => output.push(ch),
        }
    }
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
        // repeat 以 until 表达式结束，下一行的括号仍可能成为其调用后缀。
        crate::ast::AstStmt::Repeat(_) => true,
        _ => false,
    }
}

fn stmt_starts_with_parenthesis(stmt: &crate::ast::AstStmt) -> bool {
    match stmt {
        crate::ast::AstStmt::CallStmt(call) => match &call.call {
            crate::ast::AstCallKind::Call(call) => {
                prefix_expr_starts_with_parenthesis(&call.callee)
            }
            crate::ast::AstCallKind::MethodCall(call) => {
                prefix_expr_starts_with_parenthesis(&call.receiver)
            }
        },
        // 左值的首个前缀也可能以括号开头；换行不能阻止它接到上一条 CALL 上。
        crate::ast::AstStmt::Assign(assign) => match assign.targets.first() {
            Some(crate::ast::AstLValue::FieldAccess(access)) => {
                prefix_expr_starts_with_parenthesis(&access.base)
            }
            Some(crate::ast::AstLValue::IndexAccess(access)) => {
                prefix_expr_starts_with_parenthesis(&access.base)
            }
            _ => false,
        },
        _ => false,
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
