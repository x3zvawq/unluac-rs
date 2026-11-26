//! WASM 桥接层的结构化返回类型与转换。
//!
//! 从 DecompileResult 投影 proto 元数据、CFG 和生成源码，序列化为前端使用的 JSON；
//! 核心库不承担这些展示 DTO 或 serde 依赖。

use std::collections::{BTreeMap, BTreeSet};

use serde::Serialize;

use unluac::analysis::{BlockKind, CfgGraph, EdgeKind};
use unluac::ast::{
    AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionName, AstLValue, AstModule,
    AstNameRef, AstStmt, NameMap, ProtoId,
};
use unluac::decompile::{DecompileResult, collect_error_protos};
use unluac::parser::{RawLiteralConst, RawProto, RawString, format_raw_instr};
use unluac::transformer::{LoweredProto, RawInstrRef, format_low_instr};

// ── 顶层结果 ──────────────────────────────────────────────

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct WasmRichResult<'a> {
    /// 反编译生成的源码或诊断伪源码
    pub source: &'a str,
    /// 识别到的方言
    pub dialect: &'static str,
    /// `source` 或 `diagnostic-pseudocode`
    pub kind: &'static str,
    /// 宽容模式下产生诊断错误占位符的 proto ID 列表
    pub failed_protos: Vec<usize>,
    /// proto 元数据（DFS 序展平）
    pub protos: Vec<WasmProtoMeta>,
    /// 每个 proto 的 CFG（与 protos 平行数组，index 一致）
    pub cfgs: Vec<WasmProtoCfg>,
}

// ── Proto 元数据 ──────────────────────────────────────────

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct WasmProtoMeta {
    /// DFS 遍历序号（0 = 主 proto）
    pub id: usize,
    /// 函数声明名（从 AST 声明或 Luau debug_name 提取；根 proto 回退到源文件名）
    pub name: Option<String>,
    pub line_start: u32,
    pub line_end: u32,
    /// 该 proto 在生成源码中的 1-based 起始行
    pub generated_line_start: Option<usize>,
    /// 该 proto 在生成源码中的 1-based 结束行
    pub generated_line_end: Option<usize>,
    pub num_params: u8,
    pub is_vararg: bool,
    pub num_upvalues: usize,
    pub num_constants: usize,
    pub num_instructions: usize,
    /// 常量池的字面量列表（人类可读形式）
    pub constants: Vec<WasmConstant>,
    /// 子 proto 的 DFS ID 列表
    pub children: Vec<usize>,
}

/// 单个常量的可序列化投影。
#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct WasmConstant {
    /// 常量在池中的索引（0-based）
    pub index: usize,
    /// 类型标签：nil / boolean / integer / number / string / int64 / uint64 / complex
    #[serde(rename = "type")]
    pub ty: &'static str,
    /// 人类可读的值表示
    pub display: String,
}

// ── CFG ──────────────────────────────────────────────────

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct WasmProtoCfg {
    pub proto_id: usize,
    pub blocks: Vec<WasmCfgBlock>,
    pub edges: Vec<WasmCfgEdge>,
    pub entry_block: usize,
    pub exit_block: usize,
    /// 拓扑序 block ID 列表
    pub block_order: Vec<usize>,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct WasmCfgBlock {
    pub id: usize,
    pub kind: &'static str,
    /// 人类可读的 Low-IR 指令行
    pub instructions: Vec<String>,
    /// 对应的原始字节码指令行（通过 LoweringMap 映射）
    pub raw_instructions: Vec<String>,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct WasmCfgEdge {
    pub from: usize,
    pub to: usize,
    pub kind: &'static str,
}

// ── 投影逻辑 ────────────────────────────────────────────

/// 从 `DecompileResult` 提取前端所需的结构化数据。
pub fn project_rich_result(result: &DecompileResult) -> WasmRichResult<'_> {
    let (source, dialect, kind, line_spans) = result
        .state
        .generated
        .as_ref()
        .map(|g| {
            (
                g.source.as_str(),
                <&'static str>::from(g.dialect),
                <&'static str>::from(g.kind),
                Some(&g.proto_line_spans),
            )
        })
        .unwrap_or_else(|| ("", <&'static str>::from(result.state.dialect), "source", None));

    let failed_protos = result
        .state
        .ast
        .as_ref()
        .map(collect_error_protos)
        .unwrap_or_default();

    let mut decl_names: BTreeMap<usize, String> = BTreeMap::new();
    if let (Some(ast), Some(names)) = (&result.state.ast, &result.state.naming) {
        collect_ast_decl_names(&ast.body, ast.entry_function, names, &mut decl_names);
    }

    let mut lowered_debug_names: Vec<Option<String>> = Vec::new();
    if let Some(lowered) = &result.state.lowered {
        collect_lowered_debug_names(&lowered.main, &mut lowered_debug_names);
    }

    let mut protos = Vec::new();
    let mut cfgs = Vec::new();

    // 从 raw_chunk 提取 proto 元数据（DFS 序）
    if let Some(raw_chunk) = &result.state.raw_chunk {
        collect_proto_meta(
            &raw_chunk.main,
            &decl_names,
            &lowered_debug_names,
            line_spans,
            &mut protos,
        );
    }

    // 从 lowered + analysis + raw_chunk 提取 CFG 数据
    if let (Some(lowered), Some(analysis)) = (&result.state.lowered, &result.state.analysis) {
        let raw_main = result.state.raw_chunk.as_ref().map(|c| &c.main);
        collect_cfgs(&lowered.main, raw_main, &analysis.cfg_graph, &mut cfgs);
    }

    WasmRichResult {
        source,
        dialect,
        kind,
        failed_protos,
        protos,
        cfgs,
    }
}

pub(crate) fn filter_subtree_errors(
    module: &AstModule,
    target: usize,
    all_failed: &[usize],
) -> Vec<usize> {
    if all_failed.is_empty() || target >= module.protos.len() {
        return Vec::new();
    }
    let mut subtree = BTreeSet::new();
    subtree.insert(target);
    let mut changed = true;
    while changed {
        changed = false;
        for proto in &module.protos {
            if let Some((parent, _)) = &proto.parent_captures
                && subtree.contains(&parent.index())
                && subtree.insert(proto.id.index())
            {
                changed = true;
            }
        }
    }
    all_failed
        .iter()
        .copied()
        .filter(|id| subtree.contains(id))
        .collect()
}

fn collect_lowered_debug_names(proto: &LoweredProto, out: &mut Vec<Option<String>>) {
    let mut pending = vec![proto];
    while let Some(cur) = pending.pop() {
        out.push(
            cur.debug_name
                .as_ref()
                .map(raw_string_to_string)
                .filter(|s| !s.is_empty()),
        );
        for child in cur.children.iter().rev() {
            pending.push(child.as_ref());
        }
    }
}

fn resolve_name_ref(names: &NameMap, function: ProtoId, name: &AstNameRef) -> Option<String> {
    let fmap = names.functions.get(function.index())?;
    match name {
        AstNameRef::Global(g) => Some(g.text.clone()),
        AstNameRef::Environment => Some("_ENV".to_owned()),
        AstNameRef::Param(p) => fmap.params.get(p.index()).map(|n| n.text.clone()),
        AstNameRef::Local(l) => fmap.locals.get(l.index()).map(|n| n.text.clone()),
        AstNameRef::SyntheticLocal(s) => fmap.synthetic_locals.get(s).map(|n| n.text.clone()),
        AstNameRef::Upvalue(u) => fmap.upvalues.get(u.index()).map(|n| n.text.clone()),
    }
}

fn resolve_binding_ref(
    names: &NameMap,
    function: ProtoId,
    binding: AstBindingRef,
) -> Option<String> {
    let fmap = names.functions.get(function.index())?;
    match binding {
        AstBindingRef::Local(l) => fmap.locals.get(l.index()).map(|n| n.text.clone()),
        AstBindingRef::SyntheticLocal(s) => fmap.synthetic_locals.get(&s).map(|n| n.text.clone()),
    }
}

fn format_ast_function_name(
    target: &AstFunctionName,
    function: ProtoId,
    names: &NameMap,
) -> Option<String> {
    match target {
        AstFunctionName::Plain(path) => {
            let mut text = resolve_name_ref(names, function, &path.root)?;
            for field in &path.fields {
                text.push('.');
                text.push_str(field);
            }
            Some(text)
        }
        AstFunctionName::Method(path, method) => {
            let mut text = resolve_name_ref(names, function, &path.root)?;
            for field in &path.fields {
                text.push('.');
                text.push_str(field);
            }
            text.push(':');
            text.push_str(method);
            Some(text)
        }
    }
}

fn collect_ast_decl_names(
    block: &AstBlock,
    function: ProtoId,
    names: &NameMap,
    out: &mut BTreeMap<usize, String>,
) {
    for stmt in &block.stmts {
        match stmt {
            AstStmt::FunctionDecl(decl) => {
                if let Some(name) = format_ast_function_name(&decl.target, function, names) {
                    out.entry(decl.func.function.index()).or_insert(name);
                }
                collect_ast_decl_names(&decl.func.body, decl.func.function, names, out);
            }
            AstStmt::LocalFunctionDecl(decl) => {
                if let Some(name) = resolve_binding_ref(names, function, decl.name) {
                    out.entry(decl.func.function.index()).or_insert(name);
                }
                collect_ast_decl_names(&decl.func.body, decl.func.function, names, out);
            }
            AstStmt::LocalDecl(decl) => {
                for (idx, val) in decl.values.iter().enumerate() {
                    if let AstExpr::FunctionExpr(func) = val
                        && let Some(binding) = decl.bindings.get(idx)
                        && let Some(name) = resolve_binding_ref(names, function, binding.id)
                    {
                        out.entry(func.function.index()).or_insert(name);
                    }
                    collect_ast_decl_names_expr(val, names, out);
                }
            }
            AstStmt::GlobalDecl(decl) => {
                for val in &decl.values {
                    collect_ast_decl_names_expr(val, names, out);
                }
            }
            AstStmt::Assign(assign) => {
                for (idx, val) in assign.values.iter().enumerate() {
                    if let AstExpr::FunctionExpr(func) = val
                        && let Some(target) = assign.targets.get(idx)
                    {
                        let label = match target {
                            AstLValue::Name(n) => resolve_name_ref(names, function, n),
                            AstLValue::FieldAccess(fa) => {
                                if let AstExpr::Var(root) = &fa.base {
                                    resolve_name_ref(names, function, root)
                                        .map(|r| format!("{r}.{}", fa.field))
                                } else {
                                    Some(fa.field.clone())
                                }
                            }
                            AstLValue::IndexAccess(_) => None,
                        };
                        if let Some(label) = label {
                            out.entry(func.function.index()).or_insert(label);
                        }
                    }
                    collect_ast_decl_names_expr(val, names, out);
                }
            }
            AstStmt::CallStmt(call) => match &call.call {
                AstCallKind::Call(c) => {
                    collect_ast_decl_names_expr(&c.callee, names, out);
                    for a in &c.args {
                        collect_ast_decl_names_expr(a, names, out);
                    }
                }
                AstCallKind::MethodCall(m) => {
                    collect_ast_decl_names_expr(&m.receiver, names, out);
                    for a in &m.args {
                        collect_ast_decl_names_expr(a, names, out);
                    }
                }
            },
            AstStmt::Return(r) => {
                for v in &r.values {
                    collect_ast_decl_names_expr(v, names, out);
                }
            }
            AstStmt::If(i) => {
                collect_ast_decl_names_expr(&i.cond, names, out);
                collect_ast_decl_names(&i.then_block, function, names, out);
                if let Some(eb) = &i.else_block {
                    collect_ast_decl_names(eb, function, names, out);
                }
            }
            AstStmt::While(w) => {
                collect_ast_decl_names_expr(&w.cond, names, out);
                collect_ast_decl_names(&w.body, function, names, out);
            }
            AstStmt::Repeat(r) => {
                collect_ast_decl_names(&r.body, function, names, out);
                collect_ast_decl_names_expr(&r.cond, names, out);
            }
            AstStmt::NumericFor(nf) => {
                collect_ast_decl_names(&nf.body, function, names, out);
            }
            AstStmt::GenericFor(gf) => {
                collect_ast_decl_names(&gf.body, function, names, out);
            }
            AstStmt::DoBlock(b) => collect_ast_decl_names(b, function, names, out),
            AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) | AstStmt::Error(_) => {}
        }
    }
}

fn collect_ast_decl_names_expr(
    expr: &AstExpr,
    names: &NameMap,
    out: &mut BTreeMap<usize, String>,
) {
    match expr {
        AstExpr::FunctionExpr(func) => {
            collect_ast_decl_names(&func.body, func.function, names, out);
        }
        AstExpr::TableConstructor(tc) => {
            for field in &tc.fields {
                match field {
                    unluac::ast::AstTableField::Array(v) => {
                        collect_ast_decl_names_expr(v, names, out);
                    }
                    unluac::ast::AstTableField::Record(r) => {
                        if let AstExpr::FunctionExpr(func) = &r.value {
                            let key_name = match &r.key {
                                unluac::ast::AstTableKey::Name(k) => Some(k.clone()),
                                unluac::ast::AstTableKey::Expr(AstExpr::String(s)) => {
                                    s.as_utf8().map(ToOwned::to_owned)
                                }
                                _ => None,
                            };
                            if let Some(k) = key_name {
                                out.entry(func.function.index()).or_insert(k);
                            }
                        }
                        collect_ast_decl_names_expr(&r.value, names, out);
                    }
                }
            }
        }
        AstExpr::Call(c) => {
            collect_ast_decl_names_expr(&c.callee, names, out);
            for a in &c.args {
                collect_ast_decl_names_expr(a, names, out);
            }
        }
        AstExpr::MethodCall(m) => {
            collect_ast_decl_names_expr(&m.receiver, names, out);
            for a in &m.args {
                collect_ast_decl_names_expr(a, names, out);
            }
        }
        AstExpr::Binary(b) => {
            collect_ast_decl_names_expr(&b.lhs, names, out);
            collect_ast_decl_names_expr(&b.rhs, names, out);
        }
        AstExpr::LogicalAnd(l) | AstExpr::LogicalOr(l) => {
            collect_ast_decl_names_expr(&l.lhs, names, out);
            collect_ast_decl_names_expr(&l.rhs, names, out);
        }
        AstExpr::Unary(u) => collect_ast_decl_names_expr(&u.expr, names, out),
        AstExpr::SingleValue(inner) => collect_ast_decl_names_expr(inner, names, out),
        AstExpr::IfExpr(ie) => {
            collect_ast_decl_names_expr(&ie.cond, names, out);
            collect_ast_decl_names_expr(&ie.then_expr, names, out);
            collect_ast_decl_names_expr(&ie.else_expr, names, out);
        }
        _ => {}
    }
}

/// DFS 收集 proto 元数据，已发布行数就是当前先序 ID。
fn collect_proto_meta(
    proto: &RawProto,
    decl_names: &BTreeMap<usize, String>,
    lowered_debug_names: &[Option<String>],
    line_spans: Option<&BTreeMap<usize, (usize, usize)>>,
    out: &mut Vec<WasmProtoMeta>,
) {
    // 显式栈避免深 Luau proto 链耗尽 WASM 调用栈；子 ID 在实际出栈时回填父行。
    let mut pending: Vec<(&RawProto, Option<usize>)> = vec![(proto, None)];
    while let Some((proto, parent)) = pending.pop() {
        let my_id = out.len();

        if let Some(parent) = parent {
            out[parent].children.push(my_id);
        }

        let name = if my_id == 0 {
            proto.common.source.as_ref().map(raw_string_to_string)
        } else {
            decl_names
                .get(&my_id)
                .cloned()
                .or_else(|| lowered_debug_names.get(my_id).cloned().flatten())
        };
        let (generated_line_start, generated_line_end) = line_spans
            .and_then(|spans| spans.get(&my_id).copied())
            .map_or((None, None), |(s, e)| (Some(s), Some(e)));

        out.push(WasmProtoMeta {
            id: my_id,
            name,
            line_start: proto.common.line_range.defined_start,
            line_end: proto.common.line_range.defined_end,
            generated_line_start,
            generated_line_end,
            num_params: proto.common.signature.num_params,
            is_vararg: proto.common.signature.is_vararg,
            num_upvalues: proto.common.upvalues.common.count as usize,
            num_constants: proto.common.constants.common.literals.len(),
            num_instructions: proto.common.instructions.len(),
            constants: proto
                .common
                .constants
                .common
                .literals
                .iter()
                .enumerate()
                .map(|(i, lit)| project_constant(i, lit))
                .collect(),
            children: Vec::with_capacity(proto.common.children.len()),
        });

        // 逆序压栈保持源码子节点顺序，此时子节点尚未发布。
        for child in proto.common.children.iter().rev() {
            pending.push((child.as_ref(), Some(my_id)));
        }
    }
}

/// DFS 收集每个 proto 的 CFG。
///
/// `raw_proto` 为 `Some` 时会通过 `LoweringMap` 将每条 Low-IR 指令
/// 映射回原始字节码并格式化为 `raw_instructions`；否则留空。
fn collect_cfgs(
    lowered: &LoweredProto,
    raw_proto: Option<&RawProto>,
    cfg_graph: &CfgGraph,
    out: &mut Vec<WasmProtoCfg>,
) {
    struct Frame<'a> {
        lowered: &'a LoweredProto,
        raw: Option<&'a RawProto>,
        cfg_graph: &'a CfgGraph,
    }

    let mut pending = vec![Frame {
        lowered,
        raw: raw_proto,
        cfg_graph,
    }];
    while let Some(frame) = pending.pop() {
        let proto_id = out.len();

        let raw_instrs = frame.raw.map(|p| &p.common.instructions);
        let cfg = &frame.cfg_graph.cfg;
        let blocks: Vec<WasmCfgBlock> = cfg
            .blocks
            .iter()
            .enumerate()
            .map(|(i, block)| {
                let mut instructions = Vec::new();
                let mut raw_instructions = Vec::new();

                for offset in 0..block.instrs.len {
                    let idx = block.instrs.start.index() + offset;
                    if let Some(low_instr) = frame.lowered.instrs.get(idx) {
                        instructions.push(format_low_instr(low_instr));

                        // 通过 lowering_map 找到对应的原始指令
                        if let Some(raw_vec) = raw_instrs {
                            let raw_refs = frame.lowered.lowering_map.low_to_raw.get(idx);
                            let raw_text: Vec<String> = raw_refs
                                .map(|refs| {
                                    refs.iter()
                                        .filter_map(|RawInstrRef(raw_idx)| {
                                            raw_vec.get(*raw_idx).map(format_raw_instr)
                                        })
                                        .collect()
                                })
                                .unwrap_or_default();
                            raw_instructions.push(raw_text.join("; "));
                        }
                    }
                }

                WasmCfgBlock {
                    id: i,
                    kind: block_kind_str(block.kind),
                    instructions,
                    raw_instructions,
                }
            })
            .collect();

        let edges: Vec<WasmCfgEdge> = cfg
            .edges
            .iter()
            .map(|edge| WasmCfgEdge {
                from: edge.from.index(),
                to: edge.to.index(),
                kind: edge_kind_str(edge.kind),
            })
            .collect();

        out.push(WasmProtoCfg {
            proto_id,
            blocks,
            edges,
            entry_block: cfg.entry_block.index(),
            exit_block: cfg.exit_block.index(),
            block_order: cfg.block_order.iter().map(|b| b.index()).collect(),
        });

        // 与元数据投影保持相同的源码先序。
        let child_count = frame
            .lowered
            .children
            .len()
            .min(frame.cfg_graph.children.len())
            .min(
                frame
                    .raw
                    .map_or(usize::MAX, |raw| raw.common.children.len()),
            );
        for index in (0..child_count).rev() {
            pending.push(Frame {
                lowered: &frame.lowered.children[index],
                raw: frame
                    .raw
                    .and_then(|raw| raw.common.children.get(index).map(|child| child.as_ref())),
                cfg_graph: &frame.cfg_graph.children[index],
            });
        }
    }
}

fn block_kind_str(kind: BlockKind) -> &'static str {
    match kind {
        BlockKind::Entry | BlockKind::Normal => "normal",
        BlockKind::Exit => "synthetic-exit",
    }
}

fn edge_kind_str(kind: EdgeKind) -> &'static str {
    match kind {
        EdgeKind::Fallthrough => "fallthrough",
        EdgeKind::Jump => "jump",
        EdgeKind::BranchTrue => "branch-true",
        EdgeKind::BranchFalse => "branch-false",
        EdgeKind::LoopBody => "loop-body",
        EdgeKind::LoopExit => "loop-exit",
        EdgeKind::Return => "return",
        EdgeKind::TailCall => "tail-call",
    }
}

fn raw_string_to_string(s: &RawString) -> String {
    // 优先使用已解码文本，否则 lossy UTF-8
    if let Some(decoded) = &s.text {
        decoded.value.to_string()
    } else {
        String::from_utf8_lossy(&s.bytes).into_owned()
    }
}

fn project_constant(index: usize, lit: &RawLiteralConst) -> WasmConstant {
    let (ty, display) = match lit {
        RawLiteralConst::Nil => ("nil", "nil".to_owned()),
        RawLiteralConst::Boolean(b) => ("boolean", b.to_string()),
        RawLiteralConst::Integer(n) => ("integer", n.to_string()),
        RawLiteralConst::Number(n) => ("number", format!("{n}")),
        RawLiteralConst::String(s) => ("string", format!("\"{}\"", raw_string_to_string(s))),
        RawLiteralConst::Int64(n) => ("int64", format!("{n}LL")),
        RawLiteralConst::UInt64(n) => ("uint64", format!("{n}ULL")),
        RawLiteralConst::Complex { real, imag } => ("complex", format!("{real}+{imag}i")),
        RawLiteralConst::Vector(vector) => {
            let [x, y, z, w] = vector.components.map(f32::from_bits);
            ("vector", format!("vector({x},{y},{z},{w})"))
        }
    };
    WasmConstant { index, ty, display }
}
