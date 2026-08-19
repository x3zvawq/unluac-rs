//! 格式化 AST 表达式、lvalue、call 与函数参数；依赖操作符和渲染名称，不负责遍历 proto 树；例如保持复杂字面量和 method call 的可读结构。

use super::*;

pub(super) fn format_value_list(
    values: &[AstExpr],
    indent: &str,
    names: &FunctionRenderNames,
) -> String {
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

pub(super) fn format_expr(expr: &AstExpr, indent: &str, names: &FunctionRenderNames) -> String {
    match expr {
        AstExpr::Nil => "nil".to_owned(),
        AstExpr::Boolean(value) => value.to_string(),
        AstExpr::Integer(value) => value.to_string(),
        AstExpr::Number(value) => value.to_string(),
        AstExpr::String(value) => value.debug_literal(),
        AstExpr::Int64(value) => format!("{value}LL"),
        AstExpr::UInt64(value) => format!("{value}ULL"),
        AstExpr::Vector(vector) => format!("vector({:?})", vector.components.map(f32::from_bits)),
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
                        super::super::common::AstTableKey::Name(name) => {
                            format!("{name} = {}", format_expr(&record.value, indent, names))
                        }
                        super::super::common::AstTableKey::Expr(expr) => {
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

pub(super) fn format_complex_literal(real: f64, imag: f64) -> String {
    if real == 0.0 {
        return format!("{imag}i");
    }
    let sign = if imag.is_sign_negative() { "-" } else { "+" };
    format!("({real} {sign} {}i)", imag.abs())
}

pub(super) fn format_head_expr(
    expr: &AstExpr,
    indent: &str,
    names: &FunctionRenderNames,
) -> String {
    strip_outer_parens(format_expr(expr, indent, names))
}

pub(super) fn write_if_stmt(
    output: &mut String,
    indent: &str,
    if_stmt: &super::super::common::AstIf,
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

pub(super) fn write_else_chain(
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

pub(super) fn format_name_ref(name: &AstNameRef, names: &FunctionRenderNames) -> String {
    match name {
        AstNameRef::Param(param) => format!("p{}", param.index()),
        AstNameRef::Local(local) => format!("l{}", local.index()),
        AstNameRef::Temp(temp) => format!("t{}", temp.index()),
        AstNameRef::SyntheticLocal(local) => format!("l{}", display_synthetic_local(*local, names)),
        AstNameRef::Upvalue(upvalue) => format!("u{}", upvalue.index()),
        AstNameRef::Global(global) => global.text.clone(),
    }
}

pub(super) fn format_name_path(path: &AstNamePath, names: &FunctionRenderNames) -> String {
    let mut rendered = format_name_ref(&path.root, names);
    for field in &path.fields {
        rendered.push('.');
        rendered.push_str(field);
    }
    rendered
}

pub(super) fn format_function_name(
    target: &AstFunctionName,
    names: &FunctionRenderNames,
) -> String {
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

pub(super) fn format_binding_ref(binding: AstBindingRef, names: &FunctionRenderNames) -> String {
    match binding {
        AstBindingRef::Local(local) => format!("l{}", local.index()),
        AstBindingRef::Temp(temp) => format!("t{}", temp.index()),
        AstBindingRef::SyntheticLocal(local) => {
            format!("l{}", display_synthetic_local(local, names))
        }
    }
}

pub(super) fn format_local_binding(
    binding: &super::super::common::AstLocalBinding,
    names: &FunctionRenderNames,
) -> String {
    let name = format_binding_ref(binding.id, names);
    match binding.attr {
        super::super::common::AstLocalAttr::None => name,
        super::super::common::AstLocalAttr::Const => format!("{name}<const>"),
        super::super::common::AstLocalAttr::Close => format!("{name}<close>"),
    }
}

pub(super) fn format_lvalue(
    target: &AstLValue,
    indent: &str,
    names: &FunctionRenderNames,
) -> String {
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

pub(super) fn format_call(call: &AstCallKind, indent: &str, names: &FunctionRenderNames) -> String {
    match call {
        AstCallKind::Call(call) => format_call_expr(call, indent, names),
        AstCallKind::MethodCall(call) => format_method_call_expr(call, indent, names),
    }
}

pub(super) fn format_call_expr(
    call: &AstCallExpr,
    indent: &str,
    names: &FunctionRenderNames,
) -> String {
    format!(
        "{}({})",
        format_call_target(&call.callee, indent, names),
        format_arg_list(&call.args, indent, names)
    )
}

pub(super) fn format_method_call_expr(
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

pub(super) fn format_call_target(
    expr: &AstExpr,
    indent: &str,
    names: &FunctionRenderNames,
) -> String {
    let rendered = format_expr(expr, indent, names);
    match expr {
        AstExpr::FunctionExpr(_) => format!("({rendered})"),
        _ => rendered,
    }
}

pub(super) fn format_arg_list(
    values: &[AstExpr],
    indent: &str,
    names: &FunctionRenderNames,
) -> String {
    values
        .iter()
        .map(|expr| format_expr(expr, indent, names))
        .collect::<Vec<_>>()
        .join(", ")
}

pub(super) fn format_function_expr(function: &AstFunctionExpr, indent: &str) -> String {
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

pub(super) fn format_decl_params(
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

pub(super) fn display_synthetic_local(
    local: AstSyntheticLocalId,
    names: &FunctionRenderNames,
) -> usize {
    names
        .synthetic_locals
        .get(&local)
        .copied()
        .unwrap_or_else(|| local.index())
}
