//! AST 阶段调试输出：展示 AST 语句概览、状态机统计与 NameMap。

use std::fmt::Write;

use crate::decompile::{
    DebugOptions, DecompileError, DecompileStage, DecompileState, StageDebugOutput,
};

pub fn dump_ast(
    state: &DecompileState,
    options: &DebugOptions,
) -> Result<StageDebugOutput, DecompileError> {
    let ast = state.require_ast()?;
    let mut out = String::new();
    let _ = writeln!(out, "===== Dump AST =====");
    let _ = writeln!(
        out,
        "protos={} entry=proto#{} root_stmts={}",
        ast.protos.len(),
        ast.entry_function.index(),
        ast.body.stmts.len()
    );
    for proto in &ast.protos {
        let _ = writeln!(
            out,
            "  proto#{}: params={} locals={} upvalues={} state_machines={}",
            proto.id.index(),
            proto.params.len(),
            proto.local_count,
            proto.upvalues.len(),
            proto.state_machine_count
        );
    }
    if let Some(names) = state.naming.as_ref() {
        let _ = writeln!(out);
        out.push_str(&super::naming::dump_name_map(
            names,
            options.detail,
            &options.filters,
            options.color,
        ));
    }
    Ok(StageDebugOutput {
        stage: DecompileStage::Ast,
        detail: options.detail,
        content: out,
    })
}
