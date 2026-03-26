//! AST 层的人类可读 dump。

use std::fmt::Write as _;

use crate::debug::{DebugDetail, DebugFilters};

use super::common::{
    AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionName, AstLValue, AstModule,
    AstNamePath, AstNameRef, AstStmt, AstTableField,
};

/// 输出 AST 的调试文本。
pub fn dump_ast(module: &AstModule, detail: DebugDetail, _filters: &DebugFilters) -> String {
    dump_module(module, detail, "AST", "ast")
}

/// 输出 Readability 阶段的调试文本。
pub fn dump_readability(
    module: &AstModule,
    detail: DebugDetail,
    _filters: &DebugFilters,
) -> String {
    dump_module(module, detail, "Readability", "readability")
}

fn dump_module(
    module: &AstModule,
    detail: DebugDetail,
    stage_title: &str,
    stage_label: &str,
) -> String {
    let mut output = String::new();
    let _ = writeln!(output, "===== Dump {stage_title} =====");
    let _ = writeln!(output, "{stage_label} detail={detail}");
    let _ = writeln!(output);
    write_block(&mut output, "", &module.body);
    output
}

fn write_block(output: &mut String, indent: &str, block: &AstBlock) {
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
                    .map(format_local_binding)
                    .collect::<Vec<_>>()
                    .join(", ");
                if local_decl.values.is_empty() {
                    let _ = writeln!(output, "{indent}local {bindings}");
                } else {
                    let _ = writeln!(
                        output,
                        "{indent}local {bindings} = {}",
                        format_value_list(&local_decl.values, indent),
                    );
                }
            }
            AstStmt::GlobalDecl(global_decl) => {
                let bindings = global_decl
                    .bindings
                    .iter()
                    .map(|binding| match binding.attr {
                        super::common::AstGlobalAttr::None => binding.name.text.clone(),
                        super::common::AstGlobalAttr::Const => {
                            format!("{}<const>", binding.name.text)
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                if global_decl.values.is_empty() {
                    let _ = writeln!(output, "{indent}global {bindings}");
                } else {
                    let _ = writeln!(
                        output,
                        "{indent}global {bindings} = {}",
                        format_value_list(&global_decl.values, indent),
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
                        .map(|target| format_lvalue(target, indent))
                        .collect::<Vec<_>>()
                        .join(", "),
                    format_value_list(&assign.values, indent),
                );
            }
            AstStmt::CallStmt(call_stmt) => {
                let _ = writeln!(output, "{indent}{}", format_call(&call_stmt.call, indent));
            }
            AstStmt::Return(ret) => {
                if ret.values.is_empty() {
                    let _ = writeln!(output, "{indent}return");
                } else {
                    let _ = writeln!(
                        output,
                        "{indent}return {}",
                        format_value_list(&ret.values, indent),
                    );
                }
            }
            AstStmt::If(if_stmt) => {
                let _ = writeln!(
                    output,
                    "{indent}if {} then",
                    format_head_expr(&if_stmt.cond, indent),
                );
                write_block(output, &format!("{indent}  "), &if_stmt.then_block);
                if let Some(else_block) = &if_stmt.else_block {
                    let _ = writeln!(output, "{indent}else");
                    write_block(output, &format!("{indent}  "), else_block);
                }
                let _ = writeln!(output, "{indent}end");
            }
            AstStmt::While(while_stmt) => {
                let _ = writeln!(
                    output,
                    "{indent}while {} do",
                    format_head_expr(&while_stmt.cond, indent),
                );
                write_block(output, &format!("{indent}  "), &while_stmt.body);
                let _ = writeln!(output, "{indent}end");
            }
            AstStmt::Repeat(repeat_stmt) => {
                let _ = writeln!(output, "{indent}repeat");
                write_block(output, &format!("{indent}  "), &repeat_stmt.body);
                let _ = writeln!(
                    output,
                    "{indent}until {}",
                    format_head_expr(&repeat_stmt.cond, indent),
                );
            }
            AstStmt::NumericFor(numeric_for) => {
                let _ = writeln!(
                    output,
                    "{indent}for {} = {}, {}, {} do",
                    format_binding_ref(numeric_for.binding),
                    format_expr(&numeric_for.start, indent),
                    format_expr(&numeric_for.limit, indent),
                    format_expr(&numeric_for.step, indent),
                );
                write_block(output, &format!("{indent}  "), &numeric_for.body);
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
                        .map(format_binding_ref)
                        .collect::<Vec<_>>()
                        .join(", "),
                    format_value_list(&generic_for.iterator, indent),
                );
                write_block(output, &format!("{indent}  "), &generic_for.body);
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
                write_block(output, &format!("{indent}  "), block);
                let _ = writeln!(output, "{indent}end");
            }
            AstStmt::FunctionDecl(function_decl) => {
                let _ = writeln!(
                    output,
                    "{indent}{}({})",
                    format_function_name(&function_decl.target),
                    function_decl
                        .func
                        .params
                        .iter()
                        .map(|param| format!("p{}", param.index()))
                        .collect::<Vec<_>>()
                        .join(", "),
                );
                write_block(output, &format!("{indent}  "), &function_decl.func.body);
                let _ = writeln!(output, "{indent}end");
            }
            AstStmt::LocalFunctionDecl(local_function_decl) => {
                let _ = writeln!(
                    output,
                    "{indent}local function {}({})",
                    format_binding_ref(local_function_decl.name),
                    local_function_decl
                        .func
                        .params
                        .iter()
                        .map(|param| format!("p{}", param.index()))
                        .collect::<Vec<_>>()
                        .join(", "),
                );
                write_block(output, &format!("{indent}  "), &local_function_decl.func.body);
                let _ = writeln!(output, "{indent}end");
            }
        }
    }
}

fn format_value_list(values: &[AstExpr], indent: &str) -> String {
    if values.is_empty() {
        "-".to_owned()
    } else {
        values
            .iter()
            .map(|expr| format_expr(expr, indent))
            .collect::<Vec<_>>()
            .join(", ")
    }
}

fn format_expr(expr: &AstExpr, indent: &str) -> String {
    match expr {
        AstExpr::Nil => "nil".to_owned(),
        AstExpr::Boolean(value) => value.to_string(),
        AstExpr::Integer(value) => value.to_string(),
        AstExpr::Number(value) => value.to_string(),
        AstExpr::String(value) => format!("{value:?}"),
        AstExpr::Var(name) => format_name_ref(name),
        AstExpr::FieldAccess(access) => {
            format!("{}.{}", format_expr(&access.base, indent), access.field)
        }
        AstExpr::IndexAccess(access) => {
            format!(
                "{}[{}]",
                format_expr(&access.base, indent),
                format_expr(&access.index, indent)
            )
        }
        AstExpr::Unary(unary) => format!(
            "({} {})",
            format_unary_op(unary.op),
            format_expr(&unary.expr, indent)
        ),
        AstExpr::Binary(binary) => format!(
            "({} {} {})",
            format_expr(&binary.lhs, indent),
            format_binary_op(binary.op),
            format_expr(&binary.rhs, indent)
        ),
        AstExpr::LogicalAnd(logical) => {
            format!(
                "({} and {})",
                format_expr(&logical.lhs, indent),
                format_expr(&logical.rhs, indent)
            )
        }
        AstExpr::LogicalOr(logical) => {
            format!(
                "({} or {})",
                format_expr(&logical.lhs, indent),
                format_expr(&logical.rhs, indent)
            )
        }
        AstExpr::Call(call) => format_call(&AstCallKind::Call(call.clone()), indent),
        AstExpr::MethodCall(call) => format_call(&AstCallKind::MethodCall(call.clone()), indent),
        AstExpr::VarArg => "...".to_owned(),
        AstExpr::TableConstructor(table) => {
            let fields = table
                .fields
                .iter()
                .map(|field| match field {
                    AstTableField::Array(expr) => format_expr(expr, indent),
                    AstTableField::Record(record) => match &record.key {
                        super::common::AstTableKey::Name(name) => {
                            format!("{name} = {}", format_expr(&record.value, indent))
                        }
                        super::common::AstTableKey::Expr(expr) => {
                            format!(
                                "[{}] = {}",
                                format_expr(expr, indent),
                                format_expr(&record.value, indent)
                            )
                        }
                    },
                })
                .collect::<Vec<_>>()
                .join(", ");
            format!("{{{fields}}}")
        }
        AstExpr::FunctionExpr(function) => format_function_expr(function, indent),
    }
}

fn format_head_expr(expr: &AstExpr, indent: &str) -> String {
    strip_outer_parens(format_expr(expr, indent))
}

fn format_name_ref(name: &super::common::AstNameRef) -> String {
    match name {
        super::common::AstNameRef::Param(param) => format!("p{}", param.index()),
        super::common::AstNameRef::Local(local) => format!("l{}", local.index()),
        super::common::AstNameRef::Temp(temp) => format!("t{}", temp.index()),
        super::common::AstNameRef::Upvalue(upvalue) => format!("u{}", upvalue.index()),
        super::common::AstNameRef::Global(global) => global.text.clone(),
    }
}

fn format_name_path(path: &AstNamePath) -> String {
    let mut rendered = format_name_ref(&path.root);
    for field in &path.fields {
        rendered.push('.');
        rendered.push_str(field);
    }
    rendered
}

fn format_function_name(target: &AstFunctionName) -> String {
    match target {
        AstFunctionName::Plain(path) => {
            let rendered = format_name_path(path);
            if matches!(path.root, AstNameRef::Global(_)) {
                format!("global function {rendered}")
            } else {
                format!("function {rendered}")
            }
        }
        AstFunctionName::Method(path, method) => {
            let rendered = format!("{}:{method}", format_name_path(path));
            if matches!(path.root, AstNameRef::Global(_)) {
                format!("global function {rendered}")
            } else {
                format!("function {rendered}")
            }
        }
    }
}

fn format_binding_ref(binding: AstBindingRef) -> String {
    match binding {
        AstBindingRef::Local(local) => format!("l{}", local.index()),
        AstBindingRef::Temp(temp) => format!("t{}", temp.index()),
    }
}

fn format_local_binding(binding: &super::common::AstLocalBinding) -> String {
    let name = format_binding_ref(binding.id);
    match binding.attr {
        super::common::AstLocalAttr::None => name,
        super::common::AstLocalAttr::Const => format!("{name}<const>"),
        super::common::AstLocalAttr::Close => format!("{name}<close>"),
    }
}

fn format_lvalue(target: &AstLValue, indent: &str) -> String {
    match target {
        AstLValue::Name(name) => format_name_ref(name),
        AstLValue::FieldAccess(access) => {
            format!("{}.{}", format_expr(&access.base, indent), access.field)
        }
        AstLValue::IndexAccess(access) => {
            format!(
                "{}[{}]",
                format_expr(&access.base, indent),
                format_expr(&access.index, indent)
            )
        }
    }
}

fn format_call(call: &AstCallKind, indent: &str) -> String {
    match call {
        AstCallKind::Call(call) => format!(
            "{}({})",
            format_call_target(&call.callee, indent),
            format_arg_list(&call.args, indent)
        ),
        AstCallKind::MethodCall(call) => format!(
            "{}:{}({})",
            format_expr(&call.receiver, indent),
            call.method,
            format_arg_list(&call.args, indent)
        ),
    }
}

fn format_call_target(expr: &AstExpr, indent: &str) -> String {
    let rendered = format_expr(expr, indent);
    match expr {
        AstExpr::FunctionExpr(_) => format!("({rendered})"),
        _ => rendered,
    }
}

fn format_arg_list(values: &[AstExpr], indent: &str) -> String {
    values
        .iter()
        .map(|expr| format_expr(expr, indent))
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_function_expr(function: &super::common::AstFunctionExpr, indent: &str) -> String {
    let params = function
        .params
        .iter()
        .map(|param| format!("p{}", param.index()))
        .collect::<Vec<_>>()
        .join(", ");
    let child_indent = format!("{indent}  ");
    let mut body = String::new();
    write_block(&mut body, &child_indent, &function.body);
    format!("function({params})\n{body}{indent}end")
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
