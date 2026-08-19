//! AST 层的人类可读 dump。
//!
//! 聚焦策略：AST 已经把闭包内联成 `AstFunctionExpr` 表达式，天然是一棵嵌套的
//! 函数树。我们把每个 `AstFunctionExpr.function.0`（= HirProtoRef 内部的 proto
//! DFS id）当作该函数在聚焦语义里的稳定 id，模块本身等同 `module.entry_function`
//! 对应的 proto，因此 `--proto`、`--proto-depth` 在 AST/Readability 层直接复用
//! parser / HIR 一路沿用的 proto 编号。
//!
//! 实现上：
//! - 先 DFS 收集本模块可见的 `(proto_id, parent_proto_id)` 对，交给
//!   `src/debug/focus.rs::compute_focus_plan` 得到 `FocusPlan`。
//! - 把 "可见 / elided" 的 proto id 塞进 thread-local，避免把一个 `&FocusPlan`
//!   参数沿着十几层 `format_*` helper 往下传。thread-local 在 WASM 单线程模型下
//!   行为与普通 static 一致，同时被 guard 对象限定在一次 dump 调用里。
//! - `format_function_expr` 以及 `write_block` 里直接渲染 FunctionDecl 的两条
//!   分支，统一在渲染 body 前查询 thread-local：不可见的函数退化为一行
//!   `function(...) --[[ body elided proto#K ]] end` 占位。
//!
//! stage dump 入口直接从主 pipeline state 读取 AST / Readability / Naming 产物并
//! 拼成一个 AST 层输出。选择不在 generate 层做 elision 的原因：generate 层产出的是最终 Lua 源码，
//! 对它做局部截断会输出非法语法。对于"只看某个函数最终长什么样"的需求，用
//! `--stop-after ast --proto N` 得到的函数形状已足够；generate 层改为整文件直出。

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use crate::ast::traverse::{
    traverse_call_children, traverse_expr_children, traverse_lvalue_children,
    traverse_stmt_children,
};
use crate::debug::{
    DebugColorMode, DebugDetail, DebugFilters, FocusPlan, FocusRequest, ProtoNode,
    build_proto_nodes, colorize_debug_text, compute_focus_plan, define_stage_dump,
    format_breadcrumb,
};
use crate::decompile::{DebugOptions, DecompileState};
use crate::hir::LocalId;

use super::common::{
    AstBindingRef, AstBlock, AstCallExpr, AstCallKind, AstExpr, AstFunctionExpr, AstFunctionName,
    AstLValue, AstMethodCallExpr, AstModule, AstNamePath, AstNameRef, AstStmt, AstSyntheticLocalId,
    AstTableField,
};
use super::pretty::{
    is_default_numeric_for_step, preferred_negated_relational_render, preferred_relational_render,
};

mod expressions;
mod operators;
mod render_names;
mod statements;

use expressions::*;
use operators::*;
use render_names::*;
use statements::*;

#[derive(Debug, Default)]
struct FunctionRenderNames {
    synthetic_locals: BTreeMap<AstSyntheticLocalId, usize>,
}

/// 由 `--proto` / `--proto-depth` 计算出的 AST 层聚焦信息。
///
/// `focus_proto_id = None` 表示用户指定的 proto 不在本 AST 里（大概率是被
/// HIR/readability 消掉的辅助 proto），调用方应打印 `<no proto matched filters>`。
#[derive(Debug, Default, Clone)]
struct AstFocusState {
    focus_proto_id: Option<usize>,
    visible_proto_ids: BTreeSet<usize>,
}

thread_local! {
    /// dump 期间共享的聚焦状态。WASM 只有单线程，行为与普通 static 一致；
    /// `AstFocusGuard` 保证每次 dump 结束后被清空，避免影响后续调用。
    static AST_FOCUS: RefCell<AstFocusState> = RefCell::new(AstFocusState::default());
}

struct AstFocusGuard;

impl Drop for AstFocusGuard {
    fn drop(&mut self) {
        AST_FOCUS.with(|s| *s.borrow_mut() = AstFocusState::default());
    }
}

fn install_ast_focus(state: AstFocusState) -> AstFocusGuard {
    AST_FOCUS.with(|s| *s.borrow_mut() = state);
    AstFocusGuard
}

define_stage_dump! {
    /// AST 阶段的调试导出。
    pub fn dump_ast(state, options) => Ast,
        dump_ast_stage(state, options)?;
}

fn dump_ast_stage(
    state: &DecompileState,
    options: &DebugOptions,
) -> Result<String, crate::decompile::DecompileError> {
    let mut output = String::new();

    append_section(
        &mut output,
        dump_ast_module(
            state.require_ast()?,
            options.detail,
            &options.filters,
            options.color,
        ),
    );
    append_section(
        &mut output,
        dump_readability_module(
            state.require_readability()?,
            options.detail,
            &options.filters,
            options.color,
        ),
    );
    append_section(
        &mut output,
        super::naming::dump_name_map(
            state.require_naming()?,
            options.detail,
            &options.filters,
            options.color,
        ),
    );

    Ok(output)
}

fn append_section(output: &mut String, section: String) {
    if !output.is_empty() {
        output.push('\n');
    }
    output.push_str(&section);
    if !output.ends_with('\n') {
        output.push('\n');
    }
}

/// 查询某个 proto 是否应渲染完整 body。默认（thread-local 尚未装载）视作可见，
/// 兼容 `dump_ast_snapshot` 这种不走聚焦流程的 caller。
fn ast_focus_is_visible(proto_id: usize) -> bool {
    AST_FOCUS.with(|s| {
        let s = s.borrow();
        if s.focus_proto_id.is_none() && s.visible_proto_ids.is_empty() {
            true
        } else {
            s.visible_proto_ids.contains(&proto_id)
        }
    })
}

/// 输出 AST 的调试文本。
fn dump_ast_module(
    module: &AstModule,
    detail: DebugDetail,
    filters: &DebugFilters,
    color: DebugColorMode,
) -> String {
    dump_module(module, detail, "AST", "ast", filters, color)
}

/// 输出 Readability 阶段的调试文本。
fn dump_readability_module(
    module: &AstModule,
    detail: DebugDetail,
    filters: &DebugFilters,
    color: DebugColorMode,
) -> String {
    dump_module(module, detail, "Readability", "readability", filters, color)
}

/// 输出 AST module 的不着色快照文本，用于 pass dump 的 before/after 对比。
///
/// 快照不走 `--proto` 聚焦：pass dump 在 HIR 层已经过滤过 proto，AST 快照只需
/// 如实记录当前 module。保留默认的 thread-local（空状态）即可让所有函数都完整渲染。
pub(crate) fn dump_ast_snapshot(module: &AstModule) -> String {
    let mut output = String::new();
    let names = collect_function_render_names(&module.body);
    write_block(&mut output, "", &module.body, &names);
    output
}

fn dump_module(
    module: &AstModule,
    detail: DebugDetail,
    stage_title: &str,
    stage_label: &str,
    filters: &DebugFilters,
    color: DebugColorMode,
) -> String {
    let (proto_ids, nodes, id_to_local) = collect_ast_proto_tree(module);
    let focus_local = filters
        .proto
        .and_then(|user_proto| id_to_local.get(&user_proto).copied());
    let plan = compute_focus_plan(
        &nodes,
        &FocusRequest {
            proto: focus_local,
            depth: filters.proto_depth,
        },
    );

    let focus_state = state_from_plan(&proto_ids, &plan);
    let _guard = install_ast_focus(focus_state.clone());

    let mut output = String::new();
    let _ = writeln!(output, "===== Dump {stage_title} =====");
    let _ = writeln!(
        output,
        "{stage_label} detail={detail} entry=proto#{} functions={}",
        module.entry_function.0,
        proto_ids.len(),
    );
    if let Some(proto_id) = filters.proto {
        let _ = writeln!(output, "filters proto=proto#{proto_id}");
    }
    let _ = writeln!(output, "filters proto_depth={}", filters.proto_depth);
    if let Some(breadcrumb) = format_breadcrumb(&plan) {
        let translated = translate_breadcrumb(&breadcrumb, &proto_ids);
        let _ = writeln!(output, "focus {translated}");
    }
    let _ = writeln!(output);

    if focus_state.focus_proto_id.is_none() {
        let _ = writeln!(output, "<no proto matched filters>");
        return colorize_debug_text(&output, color);
    }

    let focus_id = focus_state.focus_proto_id.unwrap();
    if focus_id == module.entry_function.0 {
        let names = collect_function_render_names(&module.body);
        write_block(&mut output, "", &module.body, &names);
    } else if let Some(func) = find_function_by_proto(module, focus_id) {
        let names = collect_function_render_names(&func.body);
        let params = format_decl_params(func, false, &names);
        let _ = writeln!(output, "-- focus proto#{focus_id}");
        let _ = writeln!(output, "function({params})");
        write_block(&mut output, "  ", &func.body, &names);
        let _ = writeln!(output, "end");
    } else {
        // 节点在聚焦计划里但实际找不到：理论上不会发生，留一行提示便于排查。
        let _ = writeln!(output, "<proto#{focus_id} not found in AST>");
    }

    colorize_debug_text(&output, color)
}

/// 把 `FocusPlan` 的 local-index breadcrumb 翻译回用户侧的 proto id。
fn translate_breadcrumb(breadcrumb: &str, proto_ids: &[usize]) -> String {
    // `format_breadcrumb` 输出形如 `proto#0 path=proto#0->proto#1`，这里的数字是
    // local index，需要替换为真实 proto id 才能和用户的 `--proto` 对齐。
    let mut out = String::new();
    let mut rest = breadcrumb;
    while let Some(start) = rest.find("proto#") {
        out.push_str(&rest[..start]);
        let after = &rest[start + "proto#".len()..];
        let digit_end = after
            .find(|c: char| !c.is_ascii_digit())
            .unwrap_or(after.len());
        let (digits, tail) = after.split_at(digit_end);
        if let Ok(local) = digits.parse::<usize>()
            && let Some(real) = proto_ids.get(local)
        {
            let _ = write!(out, "proto#{real}");
        } else {
            out.push_str("proto#");
            out.push_str(digits);
        }
        rest = tail;
    }
    out.push_str(rest);
    out
}

fn state_from_plan(proto_ids: &[usize], plan: &FocusPlan) -> AstFocusState {
    let visible = plan
        .visible
        .iter()
        .filter_map(|local| proto_ids.get(*local).copied())
        .collect();
    let focus = plan.focus.and_then(|local| proto_ids.get(local).copied());
    AstFocusState {
        focus_proto_id: focus,
        visible_proto_ids: visible,
    }
}

/// DFS 收集模块内所有 `AstFunctionExpr` 的 proto id 以及它们的父子关系。
///
/// 返回 `(proto_ids, nodes, id_to_local)`：
/// - `proto_ids[local]` = 该 local index 对应的真实 proto id；
/// - `nodes` 是 `compute_focus_plan` 需要的线性化节点；
/// - `id_to_local` 帮助把用户传的 `--proto` 翻译回 local index。
fn collect_ast_proto_tree(
    module: &AstModule,
) -> (Vec<usize>, Vec<ProtoNode>, BTreeMap<usize, usize>) {
    let mut proto_ids: Vec<usize> = Vec::new();
    let mut parents_local: Vec<Option<usize>> = Vec::new();
    let mut id_to_local: BTreeMap<usize, usize> = BTreeMap::new();

    let root = module.entry_function.0;
    id_to_local.insert(root, 0);
    proto_ids.push(root);
    parents_local.push(None);

    let mut pairs: Vec<(usize, usize)> = Vec::new();
    walk_block_protos(&module.body, root, &mut pairs);

    for (proto, parent) in pairs {
        if id_to_local.contains_key(&proto) {
            continue;
        }
        let parent_local = id_to_local.get(&parent).copied();
        let local = proto_ids.len();
        id_to_local.insert(proto, local);
        proto_ids.push(proto);
        parents_local.push(parent_local);
    }

    let nodes = build_proto_nodes(&parents_local);
    (proto_ids, nodes, id_to_local)
}

fn walk_block_protos(block: &AstBlock, parent_proto: usize, pairs: &mut Vec<(usize, usize)>) {
    for stmt in &block.stmts {
        walk_stmt_protos(stmt, parent_proto, pairs);
    }
}

fn walk_stmt_protos(stmt: &AstStmt, parent_proto: usize, pairs: &mut Vec<(usize, usize)>) {
    traverse_stmt_children! {
        stmt,
        iter = iter,
        opt = as_ref,
        borrow = [&],
        expr(e) => { walk_expr_protos(e, parent_proto, pairs); },
        lvalue(l) => { walk_lvalue_protos(l, parent_proto, pairs); },
        block(b) => { walk_block_protos(b, parent_proto, pairs); },
        function(f) => { walk_function_expr_protos(f, parent_proto, pairs); },
        condition(c) => { walk_expr_protos(c, parent_proto, pairs); },
        call(c) => { walk_call_protos(c, parent_proto, pairs); }
    }
}

fn walk_expr_protos(expr: &AstExpr, parent_proto: usize, pairs: &mut Vec<(usize, usize)>) {
    traverse_expr_children! {
        expr,
        iter = iter,
        borrow = [&],
        expr(e) => { walk_expr_protos(e, parent_proto, pairs); },
        function(f) => { walk_function_expr_protos(f, parent_proto, pairs); }
    }
}

fn walk_lvalue_protos(lvalue: &AstLValue, parent_proto: usize, pairs: &mut Vec<(usize, usize)>) {
    traverse_lvalue_children! {
        lvalue,
        borrow = [&],
        expr(e) => { walk_expr_protos(e, parent_proto, pairs); }
    }
}

fn walk_call_protos(call: &AstCallKind, parent_proto: usize, pairs: &mut Vec<(usize, usize)>) {
    traverse_call_children! {
        call,
        iter = iter,
        borrow = [&],
        expr(e) => { walk_expr_protos(e, parent_proto, pairs); }
    }
}

fn walk_function_expr_protos(
    func: &AstFunctionExpr,
    parent_proto: usize,
    pairs: &mut Vec<(usize, usize)>,
) {
    let proto_id = func.function.0;
    pairs.push((proto_id, parent_proto));
    walk_block_protos(&func.body, proto_id, pairs);
}

fn find_function_by_proto(module: &AstModule, proto_id: usize) -> Option<&AstFunctionExpr> {
    find_function_in_block(&module.body, proto_id)
}

fn find_function_in_block(block: &AstBlock, proto_id: usize) -> Option<&AstFunctionExpr> {
    for stmt in &block.stmts {
        if let Some(found) = find_function_in_stmt(stmt, proto_id) {
            return Some(found);
        }
    }
    None
}

fn find_function_in_stmt<'a>(stmt: &'a AstStmt, proto_id: usize) -> Option<&'a AstFunctionExpr> {
    let mut result: Option<&'a AstFunctionExpr> = None;
    traverse_stmt_children! {
        stmt,
        iter = iter,
        opt = as_ref,
        borrow = [&],
        expr(e) => {
            if result.is_none() { result = find_function_in_expr(e, proto_id); }
        },
        lvalue(l) => {
            if result.is_none() { result = find_function_in_lvalue(l, proto_id); }
        },
        block(b) => {
            if result.is_none() { result = find_function_in_block(b, proto_id); }
        },
        function(f) => {
            if result.is_none() { result = find_function_in_function_expr(f, proto_id); }
        },
        condition(c) => {
            if result.is_none() { result = find_function_in_expr(c, proto_id); }
        },
        call(c) => {
            if result.is_none() { result = find_function_in_call(c, proto_id); }
        }
    }
    result
}

fn find_function_in_expr<'a>(expr: &'a AstExpr, proto_id: usize) -> Option<&'a AstFunctionExpr> {
    let mut result: Option<&'a AstFunctionExpr> = None;
    traverse_expr_children! {
        expr,
        iter = iter,
        borrow = [&],
        expr(e) => {
            if result.is_none() { result = find_function_in_expr(e, proto_id); }
        },
        function(f) => {
            if result.is_none() { result = find_function_in_function_expr(f, proto_id); }
        }
    }
    result
}

fn find_function_in_lvalue<'a>(
    lvalue: &'a AstLValue,
    proto_id: usize,
) -> Option<&'a AstFunctionExpr> {
    let mut result: Option<&'a AstFunctionExpr> = None;
    traverse_lvalue_children! {
        lvalue,
        borrow = [&],
        expr(e) => {
            if result.is_none() { result = find_function_in_expr(e, proto_id); }
        }
    }
    result
}

fn find_function_in_call<'a>(
    call: &'a AstCallKind,
    proto_id: usize,
) -> Option<&'a AstFunctionExpr> {
    let mut result: Option<&'a AstFunctionExpr> = None;
    traverse_call_children! {
        call,
        iter = iter,
        borrow = [&],
        expr(e) => {
            if result.is_none() { result = find_function_in_expr(e, proto_id); }
        }
    }
    result
}

fn find_function_in_function_expr(
    func: &AstFunctionExpr,
    proto_id: usize,
) -> Option<&AstFunctionExpr> {
    if func.function.0 == proto_id {
        return Some(func);
    }
    find_function_in_block(&func.body, proto_id)
}
