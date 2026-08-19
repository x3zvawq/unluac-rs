//! 将 AST block/statement 写成稳定 debug 文本；依赖表达式格式器和渲染名称，不负责 focus 选择；例如打印 if/loop/table assignment 的树形快照。

use super::*;

pub(super) fn write_block(
    output: &mut String,
    indent: &str,
    block: &AstBlock,
    names: &FunctionRenderNames,
) {
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
                    .unwrap_or(super::super::common::AstGlobalAttr::None);
                let keyword = match attr {
                    super::super::common::AstGlobalAttr::None => "global",
                    super::super::common::AstGlobalAttr::Const => "global<const>",
                };
                let bindings = global_decl
                    .bindings
                    .iter()
                    .map(|binding| match &binding.target {
                        super::super::common::AstGlobalBindingTarget::Name(name) => {
                            name.text.clone()
                        }
                        super::super::common::AstGlobalBindingTarget::Wildcard => "*".to_owned(),
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
                    let _ = writeln!(output, "{header} --[[ body elided proto#{proto_id} ]] end",);
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
                    let _ = writeln!(output, "{header} --[[ body elided proto#{proto_id} ]] end",);
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
