//! 这个文件承载 HIR 层的共享调试输出。
//!
//! HIR dump 的重点是把 proto 边界、debug binding hint、绑定数量和 stmt tree 稳定打印
//! 出来，并让残留的 `Temp / Goto / Label / Continue / Unstructured` 一眼可见。stage dump
//! 入口直接从主 pipeline state 读取 HIR module；如果最终 dump 里还出现
//! `decision(...)`，那说明 HIR 末端的决策图消除退化了。

use std::collections::BTreeMap;
use std::fmt::Write as _;

use crate::debug::{
    DebugColorMode, DebugDetail, DebugFilters, FocusPlan, ProtoSummaryRow, build_proto_nodes,
    colorize_debug_text, compute_focus_plan, define_stage_dump, format_breadcrumb,
    format_proto_summary_row,
};

use super::common::{
    HirBlock, HirDecisionExpr, HirDecisionTarget, HirExpr, HirLValue, HirModule, HirProto, HirStmt,
    HirTableField, HirUnaryOpKind, HirValuePack,
};

#[derive(Debug, Clone, Copy)]
pub(super) struct HirProtoEntry<'a> {
    pub id: usize,
    pub parent: Option<usize>,
    pub proto: &'a HirProto,
}

define_stage_dump! {
    /// HIR 阶段的调试导出。
    pub fn dump_hir(state, options) => Hir,
        dump_hir_module(
            state.require_hir()?,
            options.detail,
            &options.filters,
            options.color
        );
}

/// 输出 HIR 的人类可读摘要。
pub(crate) fn dump_hir_module(
    module: &HirModule,
    detail: DebugDetail,
    filters: &DebugFilters,
    color: DebugColorMode,
) -> String {
    let mut output = String::new();

    let _ = writeln!(output, "===== Dump HIR =====");
    let _ = writeln!(
        output,
        "hir detail={} entry=proto#{} protos={}",
        detail,
        module.entry.index(),
        module.protos.len()
    );
    if let Some(proto_id) = filters.proto {
        let _ = writeln!(output, "filters proto=proto#{proto_id}");
    }
    let _ = writeln!(output, "filters proto_depth={}", filters.proto_depth);

    let entries = collect_hir_entries(module);
    let plan = plan_focus(&entries, filters);
    if let Some(breadcrumb) = format_breadcrumb(&plan) {
        let _ = writeln!(output, "focus {breadcrumb}");
    }
    let _ = writeln!(output);

    if plan.focus.is_none() {
        let _ = writeln!(output, "  <no proto matched filters>");
        return colorize_debug_text(&output, color);
    }

    for entry in &entries {
        if plan.is_elided(entry.id) {
            let _ = writeln!(
                output,
                "{}",
                format_proto_summary_row(&build_summary_row(entry)),
            );
            continue;
        }
        if !plan.is_visible(entry.id) {
            continue;
        }

        let proto = entry.proto;

        let _ = writeln!(
            output,
            "proto#{} params={} locals={} upvalues={} temps={} children={}",
            proto.id.index(),
            proto.params.len(),
            proto.locals.len(),
            proto.upvalues.len(),
            proto.temps.len(),
            format_proto_refs(&proto.children),
        );

        if matches!(detail, DebugDetail::Summary) {
            continue;
        }

        let _ = writeln!(
            output,
            "  source={} lines={}..{} vararg={}",
            proto.source.as_deref().unwrap_or("-"),
            proto.line_range.defined_start,
            proto.line_range.defined_end,
            proto.signature.is_vararg
        );
        write_debug_bindings(&mut output, proto);
        let _ = writeln!(output, "  body");
        write_block(&mut output, "    ", &proto.body);
    }

    colorize_debug_text(&output, color)
}

fn write_debug_bindings(output: &mut String, proto: &HirProto) {
    let _ = writeln!(output, "  debug binding hints");
    write_debug_hint_slice(output, "p", &proto.param_debug_hints, None);
    write_debug_hint_slice(output, "l", &proto.local_debug_hints, None);
    write_debug_hint_slice(output, "u", &proto.upvalue_debug_hints, None);
    write_debug_hint_slice(
        output,
        "t",
        &proto.temp_debug_locals,
        Some(&proto.temp_debug_scopes),
    );
}

fn write_debug_hint_slice(
    output: &mut String,
    prefix: &str,
    hints: &[Option<String>],
    scopes: Option<&[Option<usize>]>,
) {
    for (index, hint) in hints.iter().enumerate() {
        let Some(hint) = hint else {
            continue;
        };
        let scope = scopes
            .and_then(|scopes| scopes.get(index))
            .and_then(|scope| *scope)
            .map_or_else(String::new, |scope| format!(" scope#{scope}"));
        let _ = writeln!(output, "    {prefix}{index}{scope} -> {hint:?}");
    }
}

fn write_block(output: &mut String, indent: &str, block: &HirBlock) {
    if block.stmts.is_empty() {
        let _ = writeln!(output, "{indent}<empty>");
        return;
    }

    for stmt in &block.stmts {
        match stmt {
            HirStmt::LocalDecl(local_decl) => {
                let _ = writeln!(
                    output,
                    "{indent}local {:?} = {}",
                    local_decl
                        .bindings
                        .iter()
                        .map(|binding| format!("l{}", binding.index()))
                        .collect::<Vec<_>>(),
                    format_value_pack(&local_decl.values),
                );
            }
            HirStmt::GlobalDecl(global_decl) => {
                let _ = writeln!(
                    output,
                    "{indent}global {} = {}",
                    global_decl.names.join(", "),
                    format_value_pack(&global_decl.values),
                );
            }
            HirStmt::Assign(assign) => {
                let _ = writeln!(
                    output,
                    "{indent}assign {} = {}",
                    assign
                        .targets
                        .iter()
                        .map(format_lvalue)
                        .collect::<Vec<_>>()
                        .join(", "),
                    format_value_pack(&assign.values),
                );
            }
            HirStmt::TableSetList(set_list) => {
                let _ = writeln!(
                    output,
                    "{indent}table-set-list {} start={} values={}",
                    format_expr(&set_list.base),
                    set_list.start_index,
                    format_value_pack(&set_list.values),
                );
            }
            HirStmt::ErrNil(err_nnil) => {
                let _ = writeln!(
                    output,
                    "{indent}err-nnil {} name={}",
                    format_expr(&err_nnil.value),
                    err_nnil.name.as_deref().unwrap_or("?"),
                );
            }
            HirStmt::ToBeClosed(to_be_closed) => {
                let _ = writeln!(
                    output,
                    "{indent}to-be-closed {}",
                    format_expr(&to_be_closed.value)
                );
            }
            HirStmt::Close(close) => {
                let _ = writeln!(output, "{indent}close from r{}", close.from_reg);
            }
            HirStmt::CallStmt(call_stmt) => {
                let _ = writeln!(output, "{indent}call {}", format_call_expr(&call_stmt.call));
            }
            HirStmt::Return(ret) => {
                let _ = writeln!(output, "{indent}return {}", format_value_pack(&ret.values),);
            }
            HirStmt::If(if_stmt) => {
                let _ = writeln!(output, "{indent}if {}", format_expr(&if_stmt.cond));
                let _ = writeln!(output, "{indent}  then");
                write_block(output, &format!("{indent}    "), &if_stmt.then_block);
                if let Some(else_block) = &if_stmt.else_block {
                    let _ = writeln!(output, "{indent}  else");
                    write_block(output, &format!("{indent}    "), else_block);
                }
            }
            HirStmt::While(while_stmt) => {
                let _ = writeln!(output, "{indent}while {}", format_expr(&while_stmt.cond));
                write_block(output, &format!("{indent}  "), &while_stmt.body);
            }
            HirStmt::Repeat(repeat_stmt) => {
                let _ = writeln!(output, "{indent}repeat");
                write_block(output, &format!("{indent}  "), &repeat_stmt.body);
                let _ = writeln!(output, "{indent}until {}", format_expr(&repeat_stmt.cond));
            }
            HirStmt::NumericFor(numeric_for) => {
                let _ = writeln!(
                    output,
                    "{indent}numeric-for l{} = {}, {}, {}",
                    numeric_for.binding.index(),
                    format_expr(&numeric_for.start),
                    format_expr(&numeric_for.limit),
                    format_expr(&numeric_for.step),
                );
                write_block(output, &format!("{indent}  "), &numeric_for.body);
            }
            HirStmt::GenericFor(generic_for) => {
                let _ = writeln!(
                    output,
                    "{indent}generic-for {} in {}",
                    generic_for
                        .bindings
                        .iter()
                        .map(|binding| format!("l{}", binding.index()))
                        .collect::<Vec<_>>()
                        .join(", "),
                    format_value_pack(&generic_for.iterator),
                );
                write_block(output, &format!("{indent}  "), &generic_for.body);
            }
            HirStmt::Break => {
                let _ = writeln!(output, "{indent}break");
            }
            HirStmt::Continue => {
                let _ = writeln!(output, "{indent}continue");
            }
            HirStmt::Goto(goto_stmt) => {
                let _ = writeln!(output, "{indent}goto L{}", goto_stmt.target.index());
            }
            HirStmt::Label(label) => {
                let barriers = label
                    .tbc_barriers
                    .iter()
                    .map(|instr| format!("@{}", instr.index()))
                    .collect::<Vec<_>>()
                    .join(", ");
                let _ = writeln!(
                    output,
                    "{indent}label L{} tbc=[{barriers}]",
                    label.id.index()
                );
            }
            HirStmt::Block(block) => {
                let _ = writeln!(output, "{indent}block");
                write_block(output, &format!("{indent}  "), block);
            }
        }
    }
}

fn format_value_pack(values: &HirValuePack) -> String {
    if values.is_empty() {
        "-".to_owned()
    } else {
        let mut rendered = values.fixed.iter().map(format_expr).collect::<Vec<_>>();
        if let Some(tail) = &values.tail {
            let shape = tail
                .exact_width()
                .map_or_else(|| "open".to_owned(), |width| format!("exact:{width}"));
            rendered.push(format!("{} <tail:{shape}>", format_expr(tail.as_expr())));
        }
        rendered.join(", ")
    }
}

fn format_expr(expr: &HirExpr) -> String {
    match expr {
        HirExpr::Nil => "nil".to_owned(),
        HirExpr::Boolean(value) => value.to_string(),
        HirExpr::Integer(value) => value.to_string(),
        HirExpr::Number(value) => value.to_string(),
        HirExpr::String(value) => value.debug_literal(),
        HirExpr::Int64(value) => format!("{value}LL"),
        HirExpr::UInt64(value) => format!("{value}ULL"),
        HirExpr::Vector(vector) => format!("vector({:?})", vector.components.map(f32::from_bits)),
        HirExpr::Complex { real, imag } => format_complex_literal(*real, *imag),
        HirExpr::ParamRef(param) => format!("p{}", param.index()),
        HirExpr::LocalRef(local) => format!("l{}", local.index()),
        HirExpr::UpvalueRef(upvalue) => format!("u{}", upvalue.index()),
        HirExpr::TempRef(temp) => format!("t{}", temp.index()),
        HirExpr::GlobalRef(global) => format!("global({})", global.name),
        HirExpr::TableAccess(access) => {
            format!(
                "{}[{}]",
                format_expr(&access.base),
                format_expr(&access.key)
            )
        }
        HirExpr::Unary(unary) => format!(
            "({} {})",
            format_unary_op(unary.op),
            format_expr(&unary.expr)
        ),
        HirExpr::Binary(binary) => format!(
            "({} {} {})",
            format_expr(&binary.lhs),
            format_binary_op(binary.op),
            format_expr(&binary.rhs),
        ),
        HirExpr::LogicalAnd(logical) => {
            format!(
                "({} and {})",
                format_expr(&logical.lhs),
                format_expr(&logical.rhs)
            )
        }
        HirExpr::LogicalOr(logical) => {
            format!(
                "({} or {})",
                format_expr(&logical.lhs),
                format_expr(&logical.rhs)
            )
        }
        HirExpr::Decision(decision) => format_decision_expr(decision),
        HirExpr::Call(call) => format_call_expr(call),
        HirExpr::VarArg => "...".to_owned(),
        HirExpr::TableConstructor(table) => {
            let array_count = table
                .fields
                .iter()
                .filter(|field| matches!(field, HirTableField::Array(_)))
                .count();
            let record_count = table.fields.len().saturating_sub(array_count);
            format!(
                "table(array={}, record={}, trailing={})",
                array_count,
                record_count,
                table
                    .trailing_multivalue
                    .as_ref()
                    .map(|tail| format_expr(tail.as_expr()))
                    .unwrap_or_else(|| "-".to_owned()),
            )
        }
        HirExpr::Closure(closure) => format!(
            "closure(proto#{} captures={})",
            closure.proto.index(),
            closure
                .captures
                .iter()
                .map(|capture| {
                    let mode = match capture.mode {
                        crate::hir::common::HirCaptureMode::ByValue => "value",
                        crate::hir::common::HirCaptureMode::ByReference => "ref",
                    };
                    format!("{mode}({})", format_expr(&capture.value))
                })
                .collect::<Vec<_>>()
                .join(", ")
        ),
        HirExpr::Unresolved(unresolved) => format!("unresolved({})", unresolved.summary),
    }
}

fn format_complex_literal(real: f64, imag: f64) -> String {
    if real == 0.0 {
        return format!("{imag}i");
    }
    let sign = if imag.is_sign_negative() { "-" } else { "+" };
    format!("({real} {sign} {}i)", imag.abs())
}

fn format_decision_expr(decision: &HirDecisionExpr) -> String {
    let nodes = decision
        .nodes
        .iter()
        .map(|node| {
            format!(
                "d{}: if {} then {} else {}",
                node.id.index(),
                format_expr(&node.test),
                format_decision_target(&node.truthy),
                format_decision_target(&node.falsy),
            )
        })
        .collect::<Vec<_>>()
        .join("; ");
    format!("decision(entry=d{} [{}])", decision.entry.index(), nodes)
}

fn format_decision_target(target: &HirDecisionTarget) -> String {
    match target {
        HirDecisionTarget::Node(node_ref) => format!("d{}", node_ref.index()),
        HirDecisionTarget::CurrentValue => "current".to_owned(),
        HirDecisionTarget::Expr(expr) => format_expr(expr),
    }
}

fn format_lvalue(target: &HirLValue) -> String {
    match target {
        HirLValue::Param(param) => format!("p{}", param.index()),
        HirLValue::Temp(temp) => format!("t{}", temp.index()),
        HirLValue::Local(local) => format!("l{}", local.index()),
        HirLValue::Upvalue(upvalue) => format!("u{}", upvalue.index()),
        HirLValue::Global(global) => format!("global({})", global.name),
        HirLValue::TableAccess(access) => {
            format!(
                "{}[{}]",
                format_expr(&access.base),
                format_expr(&access.key)
            )
        }
    }
}

fn format_call_expr(call: &super::common::HirCallExpr) -> String {
    let kind = if call.method {
        "method"
    } else if call.fastcall.is_some() {
        "fastcall"
    } else {
        "normal"
    };
    format!(
        "call({kind}) {}({})",
        format_expr(&call.callee),
        format_value_pack(&call.args),
    )
}

fn format_unary_op(op: HirUnaryOpKind) -> &'static str {
    match op {
        HirUnaryOpKind::Not => "not",
        HirUnaryOpKind::Neg => "-",
        HirUnaryOpKind::BitNot => "~",
        HirUnaryOpKind::Length => "#",
    }
}

fn format_binary_op(op: super::common::HirBinaryOpKind) -> &'static str {
    match op {
        super::common::HirBinaryOpKind::Add => "+",
        super::common::HirBinaryOpKind::Sub => "-",
        super::common::HirBinaryOpKind::Mul => "*",
        super::common::HirBinaryOpKind::Div => "/",
        super::common::HirBinaryOpKind::FloorDiv => "//",
        super::common::HirBinaryOpKind::Mod => "%",
        super::common::HirBinaryOpKind::Pow => "^",
        super::common::HirBinaryOpKind::BitAnd => "&",
        super::common::HirBinaryOpKind::BitOr => "|",
        super::common::HirBinaryOpKind::BitXor => "~",
        super::common::HirBinaryOpKind::Shl => "<<",
        super::common::HirBinaryOpKind::Shr => ">>",
        super::common::HirBinaryOpKind::Concat => "..",
        super::common::HirBinaryOpKind::Eq => "==",
        super::common::HirBinaryOpKind::Lt => "<",
        super::common::HirBinaryOpKind::Le => "<=",
    }
}

fn format_proto_refs(protos: &[super::common::HirProtoRef]) -> String {
    if protos.is_empty() {
        "-".to_owned()
    } else {
        protos
            .iter()
            .map(|proto| format!("proto#{}", proto.index()))
            .collect::<Vec<_>>()
            .join(", ")
    }
}

pub(super) fn collect_hir_entries<'a>(module: &'a HirModule) -> Vec<HirProtoEntry<'a>> {
    // HIR 的 proto 存在扁平数组里，`HirProtoRef(id)` 指 `protos[id]`。
    // 为了生成 focus plan 需要的 DFS 序，我们按 entry 从根开始 DFS 展开。
    let proto_by_id: BTreeMap<usize, &'a HirProto> =
        module.protos.iter().map(|p| (p.id.index(), p)).collect();

    let mut entries = Vec::new();
    let mut pending = vec![(module.entry, None)];
    while let Some((current, parent_slot)) = pending.pop() {
        let Some(proto) = proto_by_id.get(&current.index()).copied() else {
            continue;
        };
        let slot = entries.len();
        entries.push(HirProtoEntry {
            id: slot,
            parent: parent_slot,
            proto,
        });
        pending.extend(
            proto
                .children
                .iter()
                .rev()
                .map(|child| (*child, Some(slot))),
        );
    }
    // 兜底：如果 module.protos 里有孤岛 proto（没被 entry 可达到），附在末尾，
    // 保证线性下标的稳定性，elided 计数也才准。
    let seen: std::collections::BTreeSet<usize> =
        entries.iter().map(|e| e.proto.id.index()).collect();
    for proto in &module.protos {
        if !seen.contains(&proto.id.index()) {
            let id = entries.len();
            entries.push(HirProtoEntry {
                id,
                parent: None,
                proto,
            });
        }
    }
    entries
}

pub(super) fn plan_focus(entries: &[HirProtoEntry<'_>], filters: &DebugFilters) -> FocusPlan {
    let parents: Vec<Option<usize>> = entries.iter().map(|e| e.parent).collect();
    let nodes = build_proto_nodes(&parents);
    // DebugFilters.proto 走的是 "HirProtoRef.index()" 语义；我们需要把它映射回
    // 当前 entries 数组里的 slot。
    let focus_slot = filters.proto.and_then(|target| {
        entries
            .iter()
            .position(|entry| entry.proto.id.index() == target)
    });
    let mut request = filters.as_focus_request();
    request.proto = focus_slot;
    compute_focus_plan(&nodes, &request)
}

pub(super) fn build_summary_row(entry: &HirProtoEntry<'_>) -> ProtoSummaryRow {
    ProtoSummaryRow {
        id: entry.proto.id.index(),
        name: None,
        first: None,
        lines: Some((
            entry.proto.line_range.defined_start,
            entry.proto.line_range.defined_end,
        )),
        instrs: None,
        children: Some(entry.proto.children.len()),
    }
}

/// 输出单个 proto 的快照文本（不着色），用于 pass dump 的 before/after 对比。
pub(crate) fn dump_proto_snapshot(proto: &super::common::HirProto) -> String {
    let mut output = String::new();
    let _ = writeln!(
        output,
        "proto#{} params={} locals={} upvalues={} temps={}",
        proto.id.index(),
        proto.params.len(),
        proto.locals.len(),
        proto.upvalues.len(),
        proto.temps.len(),
    );
    let _ = writeln!(output, "  body");
    write_block(&mut output, "    ", &proto.body);
    output
}
