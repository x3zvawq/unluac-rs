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
//! 选择不在 generate 层做 elision 的原因：generate 层产出的是最终 Lua 源码，
//! 对它做局部截断会输出非法语法。对于"只看某个函数最终长什么样"的需求，用
//! `--stop-after readability --proto N` 或 `--stop-after ast --proto N` 得到的
//! 函数形状已足够；generate 层改为整文件直出，文档里也这么声明。

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use crate::ast::traverse::{
    traverse_call_children, traverse_expr_children, traverse_lvalue_children,
    traverse_stmt_children,
};
use crate::debug::{
    DebugColorMode, DebugDetail, DebugFilters, FocusPlan, FocusRequest, ProtoNode,
    build_proto_nodes, colorize_debug_text, compute_focus_plan, format_breadcrumb,
};
use crate::hir::LocalId;

use super::common::{
    AstBindingRef, AstBlock, AstCallExpr, AstCallKind, AstExpr, AstFunctionExpr, AstFunctionName,
    AstLValue, AstMethodCallExpr, AstModule, AstNamePath, AstNameRef, AstStmt, AstSyntheticLocalId,
    AstTableField,
};
use super::pretty::{
    is_default_numeric_for_step, preferred_negated_relational_render, preferred_relational_render,
};

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
pub fn dump_ast(
    module: &AstModule,
    detail: DebugDetail,
    filters: &DebugFilters,
    color: DebugColorMode,
) -> String {
    dump_module(module, detail, "AST", "ast", filters, color)
}

/// 输出 Readability 阶段的调试文本。
pub fn dump_readability(
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
        let digit_end = after.find(|c: char| !c.is_ascii_digit()).unwrap_or(after.len());
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
    let focus = plan
        .focus
        .and_then(|local| proto_ids.get(local).copied());
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
    let mut result: Option<&'a AstFunctionExpr> = None;    traverse_stmt_children! {
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

fn write_block(output: &mut String, indent: &str, block: &AstBlock, names: &FunctionRenderNames) {
    if block.stmts.is_empty() {
        let _ = writeln!(output, "{indent}<empty>");
        return;
    }

    for stmt in &block.stmts {
        match stmt {
            AstStmt::LocalDecl(local_decl) => {
                let bindings = local_decl
                    .bindings
                    .iter()
                    .map(|binding| format_local_binding(binding, names))
                    .collect::<Vec<_>>()
                    .join(", ");
                if local_decl.values.is_empty() {
                    let _ = writeln!(output, "{indent}local {bindings}");
                } else {
                    let _ = writeln!(
                        output,
                        "{indent}local {bindings} = {}",
                        format_value_list(&local_decl.values, indent, names),
                    );
                }
            }
            AstStmt::GlobalDecl(global_decl) => {
                let attr = global_decl
                    .bindings
                    .first()
                    .map(|binding| binding.attr)
                    .unwrap_or(super::common::AstGlobalAttr::None);
                let keyword = match attr {
                    super::common::AstGlobalAttr::None => "global",
                    super::common::AstGlobalAttr::Const => "global<const>",
                };
                let bindings = global_decl
                    .bindings
                    .iter()
                    .map(|binding| match &binding.target {
                        super::common::AstGlobalBindingTarget::Name(name) => name.text.clone(),
                        super::common::AstGlobalBindingTarget::Wildcard => "*".to_owned(),
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                if global_decl.values.is_empty() {
                    let _ = writeln!(output, "{indent}{keyword} {bindings}");
                } else {
                    let _ = writeln!(
                        output,
                        "{indent}{keyword} {bindings} = {}",
                        format_value_list(&global_decl.values, indent, names),
                    );
                }
            }
            AstStmt::Assign(assign) => {
                let _ = writeln!(
                    output,
                    "{indent}{} = {}",
                    assign
                        .targets
                        .iter()
                        .map(|target| format_lvalue(target, indent, names))
                        .collect::<Vec<_>>()
                        .join(", "),
                    format_value_list(&assign.values, indent, names),
                );
            }
            AstStmt::CallStmt(call_stmt) => {
                let _ = writeln!(
                    output,
                    "{indent}{}",
                    format_call(&call_stmt.call, indent, names)
                );
            }
            AstStmt::Return(ret) => {
                if ret.values.is_empty() {
                    let _ = writeln!(output, "{indent}return");
                } else {
                    let _ = writeln!(
                        output,
                        "{indent}return {}",
                        format_value_list(&ret.values, indent, names),
                    );
                }
            }
            AstStmt::If(if_stmt) => {
                write_if_stmt(output, indent, if_stmt, names);
            }
            AstStmt::While(while_stmt) => {
                let _ = writeln!(
                    output,
                    "{indent}while {} do",
                    format_head_expr(&while_stmt.cond, indent, names),
                );
                write_block(output, &format!("{indent}  "), &while_stmt.body, names);
                let _ = writeln!(output, "{indent}end");
            }
            AstStmt::Repeat(repeat_stmt) => {
                let _ = writeln!(output, "{indent}repeat");
                write_block(output, &format!("{indent}  "), &repeat_stmt.body, names);
                let _ = writeln!(
                    output,
                    "{indent}until {}",
                    format_head_expr(&repeat_stmt.cond, indent, names),
                );
            }
            AstStmt::NumericFor(numeric_for) => {
                let step_suffix = if is_default_numeric_for_step(&numeric_for.step) {
                    String::new()
                } else {
                    format!(", {}", format_expr(&numeric_for.step, indent, names))
                };
                let _ = writeln!(
                    output,
                    "{indent}for {} = {}, {}{} do",
                    format_binding_ref(numeric_for.binding, names),
                    format_expr(&numeric_for.start, indent, names),
                    format_expr(&numeric_for.limit, indent, names),
                    step_suffix,
                );
                write_block(output, &format!("{indent}  "), &numeric_for.body, names);
                let _ = writeln!(output, "{indent}end");
            }
            AstStmt::GenericFor(generic_for) => {
                let _ = writeln!(
                    output,
                    "{indent}for {} in {} do",
                    generic_for
                        .bindings
                        .iter()
                        .copied()
                        .map(|binding| format_binding_ref(binding, names))
                        .collect::<Vec<_>>()
                        .join(", "),
                    format_value_list(&generic_for.iterator, indent, names),
                );
                write_block(output, &format!("{indent}  "), &generic_for.body, names);
                let _ = writeln!(output, "{indent}end");
            }
            AstStmt::Break => {
                let _ = writeln!(output, "{indent}break");
            }
            AstStmt::Continue => {
                let _ = writeln!(output, "{indent}continue");
            }
            AstStmt::Goto(goto_stmt) => {
                let _ = writeln!(output, "{indent}goto L{}", goto_stmt.target.index());
            }
            AstStmt::Label(label) => {
                let _ = writeln!(output, "{indent}::L{}::", label.id.index());
            }
            AstStmt::DoBlock(block) => {
                let _ = writeln!(output, "{indent}do");
                write_block(output, &format!("{indent}  "), block, names);
                let _ = writeln!(output, "{indent}end");
            }
            AstStmt::FunctionDecl(function_decl) => {
                let function_names = collect_function_render_names(&function_decl.func.body);
                let proto_id = function_decl.func.function.0;
                let header = format!(
                    "{indent}{}({})",
                    format_function_name(&function_decl.target, names),
                    format_decl_params(
                        &function_decl.func,
                        matches!(function_decl.target, AstFunctionName::Method(_, _)),
                        names,
                    ),
                );
                if !ast_focus_is_visible(proto_id) {
                    let _ = writeln!(
                        output,
                        "{header} --[[ body elided proto#{proto_id} ]] end",
                    );
                    continue;
                }
                let _ = writeln!(output, "{header}");
                write_block(
                    output,
                    &format!("{indent}  "),
                    &function_decl.func.body,
                    &function_names,
                );
                let _ = writeln!(output, "{indent}end");
            }
            AstStmt::LocalFunctionDecl(local_function_decl) => {
                let function_names = collect_function_render_names(&local_function_decl.func.body);
                let proto_id = local_function_decl.func.function.0;
                let header = format!(
                    "{indent}local function {}({})",
                    format_binding_ref(local_function_decl.name, names),
                    format_decl_params(&local_function_decl.func, false, names),
                );
                if !ast_focus_is_visible(proto_id) {
                    let _ = writeln!(
                        output,
                        "{header} --[[ body elided proto#{proto_id} ]] end",
                    );
                    continue;
                }
                let _ = writeln!(output, "{header}");
                write_block(
                    output,
                    &format!("{indent}  "),
                    &local_function_decl.func.body,
                    &function_names,
                );
                let _ = writeln!(output, "{indent}end");
            }
            AstStmt::Error(message) => {
                let _ = writeln!(output, "{indent}-- [unluac error] {message}");
            }
        }
    }
}

fn format_value_list(values: &[AstExpr], indent: &str, names: &FunctionRenderNames) -> String {
    if values.is_empty() {
        "-".to_owned()
    } else {
        values
            .iter()
            .map(|expr| format_expr(expr, indent, names))
            .collect::<Vec<_>>()
            .join(", ")
    }
}

fn format_expr(expr: &AstExpr, indent: &str, names: &FunctionRenderNames) -> String {
    match expr {
        AstExpr::Nil => "nil".to_owned(),
        AstExpr::Boolean(value) => value.to_string(),
        AstExpr::Integer(value) => value.to_string(),
        AstExpr::Number(value) => value.to_string(),
        AstExpr::String(value) => format!("{value:?}"),
        AstExpr::Int64(value) => format!("{value}LL"),
        AstExpr::UInt64(value) => format!("{value}ULL"),
        AstExpr::Complex { real, imag } => format_complex_literal(*real, *imag),
        AstExpr::Var(name) => format_name_ref(name, names),
        AstExpr::FieldAccess(access) => {
            format!(
                "{}.{}",
                format_expr(&access.base, indent, names),
                access.field
            )
        }
        AstExpr::IndexAccess(access) => {
            format!(
                "{}[{}]",
                format_expr(&access.base, indent, names),
                format_expr(&access.index, indent, names)
            )
        }
        AstExpr::Unary(unary) => {
            if let Some(preferred) = preferred_negated_relational_render(unary) {
                format!(
                    "({} {} {})",
                    format_expr(preferred.lhs, indent, names),
                    preferred.op_text,
                    format_expr(preferred.rhs, indent, names)
                )
            } else {
                format!(
                    "({} {})",
                    format_unary_op(unary.op),
                    format_expr(&unary.expr, indent, names)
                )
            }
        }
        AstExpr::Binary(binary) => {
            if let Some(preferred) = preferred_relational_render(binary) {
                format!(
                    "({} {} {})",
                    format_expr(preferred.lhs, indent, names),
                    preferred.op_text,
                    format_expr(preferred.rhs, indent, names)
                )
            } else {
                format!(
                    "({} {} {})",
                    format_expr(&binary.lhs, indent, names),
                    format_binary_op(binary.op),
                    format_expr(&binary.rhs, indent, names)
                )
            }
        }
        AstExpr::LogicalAnd(logical) => {
            format!(
                "({} and {})",
                format_expr(&logical.lhs, indent, names),
                format_expr(&logical.rhs, indent, names)
            )
        }
        AstExpr::LogicalOr(logical) => {
            format!(
                "({} or {})",
                format_expr(&logical.lhs, indent, names),
                format_expr(&logical.rhs, indent, names)
            )
        }
        AstExpr::Call(call) => format_call_expr(call, indent, names),
        AstExpr::MethodCall(call) => format_method_call_expr(call, indent, names),
        AstExpr::SingleValue(expr) => format!("({})", format_expr(expr, indent, names)),
        AstExpr::VarArg => "...".to_owned(),
        AstExpr::TableConstructor(table) => {
            let fields = table
                .fields
                .iter()
                .map(|field| match field {
                    AstTableField::Array(expr) => format_expr(expr, indent, names),
                    AstTableField::Record(record) => match &record.key {
                        super::common::AstTableKey::Name(name) => {
                            format!("{name} = {}", format_expr(&record.value, indent, names))
                        }
                        super::common::AstTableKey::Expr(expr) => {
                            format!(
                                "[{}] = {}",
                                format_expr(expr, indent, names),
                                format_expr(&record.value, indent, names)
                            )
                        }
                    },
                })
                .collect::<Vec<_>>()
                .join(", ");
            format!("{{{fields}}}")
        }
        AstExpr::FunctionExpr(function) => format_function_expr(function, indent),
        AstExpr::Error(message) => format!("nil --[[ [unluac error] {message} ]]"),
    }
}

fn format_complex_literal(real: f64, imag: f64) -> String {
    if real == 0.0 {
        return format!("{imag}i");
    }
    let sign = if imag.is_sign_negative() { "-" } else { "+" };
    format!("({real} {sign} {}i)", imag.abs())
}

fn format_head_expr(expr: &AstExpr, indent: &str, names: &FunctionRenderNames) -> String {
    strip_outer_parens(format_expr(expr, indent, names))
}

fn write_if_stmt(
    output: &mut String,
    indent: &str,
    if_stmt: &super::common::AstIf,
    names: &FunctionRenderNames,
) {
    let _ = writeln!(
        output,
        "{indent}if {} then",
        format_head_expr(&if_stmt.cond, indent, names),
    );
    write_block(output, &format!("{indent}  "), &if_stmt.then_block, names);
    write_else_chain(output, indent, if_stmt.else_block.as_ref(), names);
    let _ = writeln!(output, "{indent}end");
}

fn write_else_chain(
    output: &mut String,
    indent: &str,
    else_block: Option<&AstBlock>,
    names: &FunctionRenderNames,
) {
    let Some(else_block) = else_block else {
        return;
    };

    if let [AstStmt::If(else_if)] = else_block.stmts.as_slice() {
        let _ = writeln!(
            output,
            "{indent}elseif {} then",
            format_head_expr(&else_if.cond, indent, names),
        );
        write_block(output, &format!("{indent}  "), &else_if.then_block, names);
        write_else_chain(output, indent, else_if.else_block.as_ref(), names);
        return;
    }

    let _ = writeln!(output, "{indent}else");
    write_block(output, &format!("{indent}  "), else_block, names);
}

fn format_name_ref(name: &AstNameRef, names: &FunctionRenderNames) -> String {
    match name {
        AstNameRef::Param(param) => format!("p{}", param.index()),
        AstNameRef::Local(local) => format!("l{}", local.index()),
        AstNameRef::Temp(temp) => format!("t{}", temp.index()),
        AstNameRef::SyntheticLocal(local) => format!("l{}", display_synthetic_local(*local, names)),
        AstNameRef::Upvalue(upvalue) => format!("u{}", upvalue.index()),
        AstNameRef::Global(global) => global.text.clone(),
    }
}

fn format_name_path(path: &AstNamePath, names: &FunctionRenderNames) -> String {
    let mut rendered = format_name_ref(&path.root, names);
    for field in &path.fields {
        rendered.push('.');
        rendered.push_str(field);
    }
    rendered
}

fn format_function_name(target: &AstFunctionName, names: &FunctionRenderNames) -> String {
    match target {
        AstFunctionName::Plain(path) => {
            let rendered = format_name_path(path, names);
            if matches!(path.root, AstNameRef::Global(_)) {
                format!("global function {rendered}")
            } else {
                format!("function {rendered}")
            }
        }
        AstFunctionName::Method(path, method) => {
            let rendered = format!("{}:{method}", format_name_path(path, names));
            if matches!(path.root, AstNameRef::Global(_)) {
                format!("global function {rendered}")
            } else {
                format!("function {rendered}")
            }
        }
    }
}

fn format_binding_ref(binding: AstBindingRef, names: &FunctionRenderNames) -> String {
    match binding {
        AstBindingRef::Local(local) => format!("l{}", local.index()),
        AstBindingRef::Temp(temp) => format!("t{}", temp.index()),
        AstBindingRef::SyntheticLocal(local) => {
            format!("l{}", display_synthetic_local(local, names))
        }
    }
}

fn format_local_binding(
    binding: &super::common::AstLocalBinding,
    names: &FunctionRenderNames,
) -> String {
    let name = format_binding_ref(binding.id, names);
    match binding.attr {
        super::common::AstLocalAttr::None => name,
        super::common::AstLocalAttr::Const => format!("{name}<const>"),
        super::common::AstLocalAttr::Close => format!("{name}<close>"),
    }
}

fn format_lvalue(target: &AstLValue, indent: &str, names: &FunctionRenderNames) -> String {
    match target {
        AstLValue::Name(name) => format_name_ref(name, names),
        AstLValue::FieldAccess(access) => {
            format!(
                "{}.{}",
                format_expr(&access.base, indent, names),
                access.field
            )
        }
        AstLValue::IndexAccess(access) => {
            format!(
                "{}[{}]",
                format_expr(&access.base, indent, names),
                format_expr(&access.index, indent, names)
            )
        }
    }
}

fn format_call(call: &AstCallKind, indent: &str, names: &FunctionRenderNames) -> String {
    match call {
        AstCallKind::Call(call) => format_call_expr(call, indent, names),
        AstCallKind::MethodCall(call) => format_method_call_expr(call, indent, names),
    }
}

fn format_call_expr(call: &AstCallExpr, indent: &str, names: &FunctionRenderNames) -> String {
    format!(
        "{}({})",
        format_call_target(&call.callee, indent, names),
        format_arg_list(&call.args, indent, names)
    )
}

fn format_method_call_expr(
    call: &AstMethodCallExpr,
    indent: &str,
    names: &FunctionRenderNames,
) -> String {
    format!(
        "{}:{}({})",
        format_expr(&call.receiver, indent, names),
        call.method,
        format_arg_list(&call.args, indent, names)
    )
}

fn format_call_target(expr: &AstExpr, indent: &str, names: &FunctionRenderNames) -> String {
    let rendered = format_expr(expr, indent, names);
    match expr {
        AstExpr::FunctionExpr(_) => format!("({rendered})"),
        _ => rendered,
    }
}

fn format_arg_list(values: &[AstExpr], indent: &str, names: &FunctionRenderNames) -> String {
    values
        .iter()
        .map(|expr| format_expr(expr, indent, names))
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_function_expr(function: &AstFunctionExpr, indent: &str) -> String {
    let proto_id = function.function.0;
    let child_names = collect_function_render_names(&function.body);
    let params = format_decl_params(function, false, &child_names);
    if !ast_focus_is_visible(proto_id) {
        // 焦点之外的函数保留语法骨架，body 折叠成单行占位，避免大文件里把所有嵌套
        // 函数都展开出来淹没真正要看的焦点函数。
        return format!("function({params}) --[[ body elided proto#{proto_id} ]] end");
    }
    let child_indent = format!("{indent}  ");
    let mut body = String::new();
    write_block(&mut body, &child_indent, &function.body, &child_names);
    format!("function({params})\n{body}{indent}end")
}

fn format_decl_params(
    function: &AstFunctionExpr,
    implicit_self: bool,
    names: &FunctionRenderNames,
) -> String {
    let mut params = function
        .params
        .iter()
        .skip(usize::from(implicit_self))
        .map(|param| format!("p{}", param.index()))
        .collect::<Vec<_>>();
    if function.is_vararg {
        params.push(if let Some(binding) = function.named_vararg {
            format!("...{}", format_binding_ref(binding, names))
        } else {
            "...".to_owned()
        });
    }
    params.join(", ")
}

fn display_synthetic_local(local: AstSyntheticLocalId, names: &FunctionRenderNames) -> usize {
    names
        .synthetic_locals
        .get(&local)
        .copied()
        .unwrap_or_else(|| local.index())
}

fn collect_function_render_names(block: &AstBlock) -> FunctionRenderNames {
    let mut max_local = None::<usize>;
    let mut synthetic_locals = BTreeSet::new();
    collect_function_render_names_in_block(block, &mut max_local, &mut synthetic_locals);
    let start_index = max_local.map_or(0, |index| index + 1);
    let synthetic_locals = synthetic_locals
        .into_iter()
        .enumerate()
        .map(|(offset, local)| (local, start_index + offset))
        .collect();
    FunctionRenderNames { synthetic_locals }
}

fn collect_function_render_names_in_block(
    block: &AstBlock,
    max_local: &mut Option<usize>,
    synthetic_locals: &mut BTreeSet<AstSyntheticLocalId>,
) {
    for stmt in &block.stmts {
        collect_function_render_names_in_stmt(stmt, max_local, synthetic_locals);
    }
}

fn collect_function_render_names_in_stmt(
    stmt: &AstStmt,
    max_local: &mut Option<usize>,
    synthetic_locals: &mut BTreeSet<AstSyntheticLocalId>,
) {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            for binding in &local_decl.bindings {
                collect_binding_ref(binding.id, max_local, synthetic_locals);
            }
            for value in &local_decl.values {
                collect_function_render_names_in_expr(value, max_local, synthetic_locals);
            }
        }
        AstStmt::GlobalDecl(global_decl) => {
            for value in &global_decl.values {
                collect_function_render_names_in_expr(value, max_local, synthetic_locals);
            }
        }
        AstStmt::Assign(assign) => {
            for target in &assign.targets {
                collect_function_render_names_in_lvalue(target, max_local, synthetic_locals);
            }
            for value in &assign.values {
                collect_function_render_names_in_expr(value, max_local, synthetic_locals);
            }
        }
        AstStmt::CallStmt(call_stmt) => {
            collect_function_render_names_in_call(&call_stmt.call, max_local, synthetic_locals);
        }
        AstStmt::Return(ret) => {
            for value in &ret.values {
                collect_function_render_names_in_expr(value, max_local, synthetic_locals);
            }
        }
        AstStmt::If(if_stmt) => {
            collect_function_render_names_in_expr(&if_stmt.cond, max_local, synthetic_locals);
            collect_function_render_names_in_block(
                &if_stmt.then_block,
                max_local,
                synthetic_locals,
            );
            if let Some(else_block) = &if_stmt.else_block {
                collect_function_render_names_in_block(else_block, max_local, synthetic_locals);
            }
        }
        AstStmt::While(while_stmt) => {
            collect_function_render_names_in_expr(&while_stmt.cond, max_local, synthetic_locals);
            collect_function_render_names_in_block(&while_stmt.body, max_local, synthetic_locals);
        }
        AstStmt::Repeat(repeat_stmt) => {
            collect_function_render_names_in_block(&repeat_stmt.body, max_local, synthetic_locals);
            collect_function_render_names_in_expr(&repeat_stmt.cond, max_local, synthetic_locals);
        }
        AstStmt::NumericFor(numeric_for) => {
            collect_binding_ref(numeric_for.binding, max_local, synthetic_locals);
            collect_function_render_names_in_expr(&numeric_for.start, max_local, synthetic_locals);
            collect_function_render_names_in_expr(&numeric_for.limit, max_local, synthetic_locals);
            collect_function_render_names_in_expr(&numeric_for.step, max_local, synthetic_locals);
            collect_function_render_names_in_block(&numeric_for.body, max_local, synthetic_locals);
        }
        AstStmt::GenericFor(generic_for) => {
            for binding in &generic_for.bindings {
                collect_binding_ref(*binding, max_local, synthetic_locals);
            }
            for iterator in &generic_for.iterator {
                collect_function_render_names_in_expr(iterator, max_local, synthetic_locals);
            }
            collect_function_render_names_in_block(&generic_for.body, max_local, synthetic_locals);
        }
        AstStmt::DoBlock(block) => {
            collect_function_render_names_in_block(block, max_local, synthetic_locals);
        }
        AstStmt::FunctionDecl(function_decl) => {
            collect_function_render_names_in_function_name(
                &function_decl.target,
                max_local,
                synthetic_locals,
            );
        }
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            collect_binding_ref(local_function_decl.name, max_local, synthetic_locals);
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) | AstStmt::Error(_) => {}
    }
}

fn collect_function_render_names_in_function_name(
    target: &AstFunctionName,
    max_local: &mut Option<usize>,
    synthetic_locals: &mut BTreeSet<AstSyntheticLocalId>,
) {
    let path = match target {
        AstFunctionName::Plain(path) => path,
        AstFunctionName::Method(path, _) => path,
    };
    collect_name_ref(&path.root, max_local, synthetic_locals);
}

fn collect_function_render_names_in_call(
    call: &AstCallKind,
    max_local: &mut Option<usize>,
    synthetic_locals: &mut BTreeSet<AstSyntheticLocalId>,
) {
    match call {
        AstCallKind::Call(call) => {
            collect_function_render_names_in_expr(&call.callee, max_local, synthetic_locals);
            for arg in &call.args {
                collect_function_render_names_in_expr(arg, max_local, synthetic_locals);
            }
        }
        AstCallKind::MethodCall(call) => {
            collect_function_render_names_in_expr(&call.receiver, max_local, synthetic_locals);
            for arg in &call.args {
                collect_function_render_names_in_expr(arg, max_local, synthetic_locals);
            }
        }
    }
}

fn collect_function_render_names_in_lvalue(
    target: &AstLValue,
    max_local: &mut Option<usize>,
    synthetic_locals: &mut BTreeSet<AstSyntheticLocalId>,
) {
    match target {
        AstLValue::Name(name) => collect_name_ref(name, max_local, synthetic_locals),
        AstLValue::FieldAccess(access) => {
            collect_function_render_names_in_expr(&access.base, max_local, synthetic_locals);
        }
        AstLValue::IndexAccess(access) => {
            collect_function_render_names_in_expr(&access.base, max_local, synthetic_locals);
            collect_function_render_names_in_expr(&access.index, max_local, synthetic_locals);
        }
    }
}

fn collect_function_render_names_in_expr(
    expr: &AstExpr,
    max_local: &mut Option<usize>,
    synthetic_locals: &mut BTreeSet<AstSyntheticLocalId>,
) {
    match expr {
        AstExpr::Var(name) => collect_name_ref(name, max_local, synthetic_locals),
        AstExpr::FieldAccess(access) => {
            collect_function_render_names_in_expr(&access.base, max_local, synthetic_locals);
        }
        AstExpr::IndexAccess(access) => {
            collect_function_render_names_in_expr(&access.base, max_local, synthetic_locals);
            collect_function_render_names_in_expr(&access.index, max_local, synthetic_locals);
        }
        AstExpr::Unary(unary) => {
            collect_function_render_names_in_expr(&unary.expr, max_local, synthetic_locals);
        }
        AstExpr::Binary(binary) => {
            collect_function_render_names_in_expr(&binary.lhs, max_local, synthetic_locals);
            collect_function_render_names_in_expr(&binary.rhs, max_local, synthetic_locals);
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            collect_function_render_names_in_expr(&logical.lhs, max_local, synthetic_locals);
            collect_function_render_names_in_expr(&logical.rhs, max_local, synthetic_locals);
        }
        AstExpr::Call(call) => {
            collect_function_render_names_in_expr(&call.callee, max_local, synthetic_locals);
            for arg in &call.args {
                collect_function_render_names_in_expr(arg, max_local, synthetic_locals);
            }
        }
        AstExpr::MethodCall(call) => {
            collect_function_render_names_in_expr(&call.receiver, max_local, synthetic_locals);
            for arg in &call.args {
                collect_function_render_names_in_expr(arg, max_local, synthetic_locals);
            }
        }
        AstExpr::SingleValue(expr) => {
            collect_function_render_names_in_expr(expr, max_local, synthetic_locals);
        }
        AstExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    AstTableField::Array(value) => {
                        collect_function_render_names_in_expr(value, max_local, synthetic_locals);
                    }
                    AstTableField::Record(record) => {
                        if let super::common::AstTableKey::Expr(key) = &record.key {
                            collect_function_render_names_in_expr(key, max_local, synthetic_locals);
                        }
                        collect_function_render_names_in_expr(
                            &record.value,
                            max_local,
                            synthetic_locals,
                        );
                    }
                }
            }
        }
        AstExpr::FunctionExpr(_)
        | AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Complex { .. }
        | AstExpr::VarArg | AstExpr::Error(_) => {}
    }
}

fn collect_name_ref(
    name: &AstNameRef,
    max_local: &mut Option<usize>,
    synthetic_locals: &mut BTreeSet<AstSyntheticLocalId>,
) {
    match name {
        AstNameRef::Local(local) => update_max_local(max_local, *local),
        AstNameRef::SyntheticLocal(local) => {
            synthetic_locals.insert(*local);
        }
        AstNameRef::Param(_)
        | AstNameRef::Temp(_)
        | AstNameRef::Upvalue(_)
        | AstNameRef::Global(_) => {}
    }
}

fn collect_binding_ref(
    binding: AstBindingRef,
    max_local: &mut Option<usize>,
    synthetic_locals: &mut BTreeSet<AstSyntheticLocalId>,
) {
    match binding {
        AstBindingRef::Local(local) => update_max_local(max_local, local),
        AstBindingRef::SyntheticLocal(local) => {
            synthetic_locals.insert(local);
        }
        AstBindingRef::Temp(_) => {}
    }
}

fn update_max_local(max_local: &mut Option<usize>, local: LocalId) {
    let index = local.index();
    *max_local = Some(max_local.map_or(index, |current| current.max(index)));
}

fn format_unary_op(op: super::common::AstUnaryOpKind) -> &'static str {
    match op {
        super::common::AstUnaryOpKind::Not => "not",
        super::common::AstUnaryOpKind::Neg => "-",
        super::common::AstUnaryOpKind::BitNot => "~",
        super::common::AstUnaryOpKind::Length => "#",
    }
}

fn format_binary_op(op: super::common::AstBinaryOpKind) -> &'static str {
    match op {
        super::common::AstBinaryOpKind::Add => "+",
        super::common::AstBinaryOpKind::Sub => "-",
        super::common::AstBinaryOpKind::Mul => "*",
        super::common::AstBinaryOpKind::Div => "/",
        super::common::AstBinaryOpKind::FloorDiv => "//",
        super::common::AstBinaryOpKind::Mod => "%",
        super::common::AstBinaryOpKind::Pow => "^",
        super::common::AstBinaryOpKind::BitAnd => "&",
        super::common::AstBinaryOpKind::BitOr => "|",
        super::common::AstBinaryOpKind::BitXor => "~",
        super::common::AstBinaryOpKind::Shl => "<<",
        super::common::AstBinaryOpKind::Shr => ">>",
        super::common::AstBinaryOpKind::Concat => "..",
        super::common::AstBinaryOpKind::Eq => "==",
        super::common::AstBinaryOpKind::Lt => "<",
        super::common::AstBinaryOpKind::Le => "<=",
    }
}

fn strip_outer_parens(rendered: String) -> String {
    if !rendered.starts_with('(') || !rendered.ends_with(')') {
        return rendered;
    }

    let mut depth = 0usize;
    for (index, ch) in rendered.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth = depth.saturating_sub(1);
                if depth == 0 && index + ch.len_utf8() != rendered.len() {
                    return rendered;
                }
            }
            _ => {}
        }
    }

    rendered[1..(rendered.len() - 1)].to_owned()
}
