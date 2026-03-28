//! 这个文件承载 HIR 层的共享调试输出。
//!
//! HIR dump 的重点是把 proto 边界、绑定数量和 stmt tree 稳定打印出来，并让残留
//! 的 `Temp / Goto / Label / Continue / Unstructured` 一眼可见。如果最终 dump 里
//! 还出现 `decision(...)`，那说明 HIR 末端的决策图消除退化了。

use std::fmt::Write as _;

use crate::debug::{DebugColorMode, DebugDetail, DebugFilters, colorize_debug_text};

use super::common::{
    HirBlock, HirDecisionExpr, HirDecisionTarget, HirExpr, HirLValue, HirModule, HirStmt,
    HirTableField, HirUnaryOpKind,
};

/// 输出 HIR 的人类可读摘要。
pub fn dump_hir(
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
    let _ = writeln!(output);

    for proto in &module.protos {
        if filters
            .proto
            .is_some_and(|proto_id| proto_id != proto.id.index())
        {
            continue;
        }

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
        let _ = writeln!(output, "  body");
        write_block(&mut output, "    ", &proto.body);
    }

    colorize_debug_text(&output, color)
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
                    format_expr_list(&local_decl.values),
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
                    format_expr_list(&assign.values),
                );
            }
            HirStmt::TableSetList(set_list) => {
                let _ = writeln!(
                    output,
                    "{indent}table-set-list {} start={} values={} trailing={}",
                    format_expr(&set_list.base),
                    set_list.start_index,
                    format_expr_list(&set_list.values),
                    set_list
                        .trailing_multivalue
                        .as_ref()
                        .map(format_expr)
                        .unwrap_or_else(|| "-".to_owned()),
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
                let _ = writeln!(output, "{indent}return {}", format_expr_list(&ret.values));
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
                    format_expr_list(&generic_for.iterator),
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
                let _ = writeln!(output, "{indent}label L{}", label.id.index());
            }
            HirStmt::Block(block) => {
                let _ = writeln!(output, "{indent}block");
                write_block(output, &format!("{indent}  "), block);
            }
            HirStmt::Unstructured(unstructured) => {
                let summary = unstructured.summary.as_deref().unwrap_or("-");
                let _ = writeln!(output, "{indent}unstructured summary={summary}");
                write_block(output, &format!("{indent}  "), &unstructured.body);
            }
        }
    }
}

fn format_expr_list(values: &[HirExpr]) -> String {
    if values.is_empty() {
        "-".to_owned()
    } else {
        values
            .iter()
            .map(format_expr)
            .collect::<Vec<_>>()
            .join(", ")
    }
}

fn format_expr(expr: &HirExpr) -> String {
    match expr {
        HirExpr::Nil => "nil".to_owned(),
        HirExpr::Boolean(value) => value.to_string(),
        HirExpr::Integer(value) => value.to_string(),
        HirExpr::Number(value) => value.to_string(),
        HirExpr::String(value) => format!("{value:?}"),
        HirExpr::Int64(value) => format!("{value}LL"),
        HirExpr::UInt64(value) => format!("{value}ULL"),
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
                    .map(format_expr)
                    .unwrap_or_else(|| "-".to_owned()),
            )
        }
        HirExpr::Closure(closure) => format!(
            "closure(proto#{} captures={})",
            closure.proto.index(),
            closure
                .captures
                .iter()
                .map(|capture| format_expr(&capture.value))
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
    let kind = if call.method { "method" } else { "normal" };
    format!(
        "call({kind}) {}({}) multiret={}",
        format_expr(&call.callee),
        call.args
            .iter()
            .map(format_expr)
            .collect::<Vec<_>>()
            .join(", "),
        call.multiret
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
