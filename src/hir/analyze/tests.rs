//! 这个文件承载 HIR analyze 层的回归测试。
//!
//! 我们这里优先验证“结构化 lower 完成时，关键状态语义已经落进 HIR”，
//! 避免把 analyze 与 simplify 的职责重新搅在一起。

use std::path::PathBuf;
use std::process::Command;

use super::lower::{ChildAnalyses, lower_proto};
use crate::cfg::{analyze_dataflow, analyze_graph_facts, build_cfg_graph};
use crate::hir::common::{HirExpr, HirLValue, HirModule, HirStmt};
use crate::hir::dump_hir;
use crate::parser::{ParseOptions, parse_luau_chunk};
use crate::structure::analyze_structure;
use crate::transformer::lower_chunk;

#[test]
fn luau_generic_for_keeps_loop_state_assignment_before_simplify() {
    let bytes = compile_luau_fixture("tests/lua_cases/luau/04_typed_callback_mesh.lua");
    let raw = parse_luau_chunk(&bytes, ParseOptions::default()).expect("fixture should parse");
    let lowered = lower_chunk(&raw).expect("fixture should lower into LIR");
    let cfg_graph = build_cfg_graph(&lowered);
    let graph_facts = analyze_graph_facts(&cfg_graph);
    let dataflow = analyze_dataflow(&lowered, &cfg_graph, &graph_facts);
    let structure = analyze_structure(&lowered, &cfg_graph, &graph_facts, &dataflow);

    let mut protos = Vec::new();
    let entry = lower_proto(
        &lowered.main,
        &cfg_graph.cfg,
        &graph_facts,
        &dataflow,
        &structure,
        ChildAnalyses {
            cfg_graphs: &cfg_graph.children,
            graph_facts: &graph_facts.children,
            dataflow: &dataflow.children,
            structure: &structure.children,
        },
        &mut protos,
    );
    let module = HirModule { entry, protos };
    let proto = &module.protos[1];
    let generic_for = proto
        .body
        .stmts
        .iter()
        .find_map(|stmt| match stmt {
            HirStmt::GenericFor(generic_for) => Some(generic_for.as_ref()),
            _ => None,
        })
        .expect("fixture should lower into a generic-for");
    assert!(
        generic_for.body.stmts.iter().any(|stmt| {
            matches!(
                stmt,
                HirStmt::Assign(assign)
                    if matches!(
                        assign.targets.as_slice(),
                        [HirLValue::Temp(_) | HirLValue::Local(_)]
                    ) && matches!(assign.values.as_slice(), [HirExpr::Call(_)])
            )
        }),
        "structured HIR lost the generic-for loop state update before simplify:\n{}",
        dump_hir(
            &module,
            crate::debug::DebugDetail::Normal,
            &crate::debug::DebugFilters::default(),
            crate::debug::DebugColorMode::Never,
        ),
    );
}

fn compile_luau_fixture(source_relative: &str) -> Vec<u8> {
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let source = repo_root.join(source_relative);
    let compiler = repo_root.join("lua/build/luau/luau-compile");
    let output = Command::new(&compiler)
        .arg("--binary")
        .arg("-g0")
        .arg(&source)
        .output()
        .unwrap_or_else(|error| {
            panic!(
                "should spawn compiler {} for {}: {error}",
                compiler.display(),
                source.display()
            )
        });
    assert!(
        output.status.success(),
        "fixture compiler should succeed for {}:\nstdout:\n{}\nstderr:\n{}",
        source.display(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    output.stdout
}
