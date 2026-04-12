//! 这个文件承载 HIR analyze 层的回归测试。
//!
//! 我们这里优先验证“结构化 lower 完成时，关键状态语义已经落进 HIR”，
//! 避免把 analyze 与 simplify 的职责重新搅在一起。

use std::path::PathBuf;
use std::process::Command;

use super::lower::{ChildAnalyses, LowerArtifacts, lower_proto};
use crate::cfg::{analyze_dataflow, analyze_graph_facts, build_cfg_proto};
use crate::hir::common::{HirBinaryOpKind, HirExpr, HirLValue, HirModule, HirStmt};
use crate::hir::dump_hir;
use crate::parser::{ParseOptions, parse_lua55_chunk, parse_luau_chunk};
use crate::structure::analyze_structure;
use crate::transformer::lower_chunk;

#[test]
fn luau_generic_for_keeps_loop_state_assignment_before_simplify() {
    let module = lower_luau_fixture_to_hir("tests/lua_cases/luau/04_typed_callback_mesh.lua");
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

#[test]
fn luau_while_header_consts_stay_in_condition_expr() {
    let module = lower_luau_fixture_to_hir("tests/lua_cases/common/control_flow/02_loops.lua");
    let while_stmt = module.protos[module.entry.index()]
        .body
        .stmts
        .iter()
        .find_map(|stmt| match stmt {
            HirStmt::While(while_stmt) => Some(while_stmt.as_ref()),
            _ => None,
        })
        .expect("fixture should lower into a while loop");

    let HirExpr::Binary(cond) = &while_stmt.cond else {
        panic!(
            "expected while condition to stay a binary comparison:\n{}",
            dump_hir(
                &module,
                crate::debug::DebugDetail::Normal,
                &crate::debug::DebugFilters::default(),
                crate::debug::DebugColorMode::Never,
            )
        );
    };
    assert_eq!(cond.op, HirBinaryOpKind::Le);
    assert!(
        matches!(&cond.rhs, HirExpr::Integer(3)),
        "while header constant should be folded into condition instead of leaking as temp:\n{}",
        dump_hir(
            &module,
            crate::debug::DebugDetail::Normal,
            &crate::debug::DebugFilters::default(),
            crate::debug::DebugColorMode::Never,
        ),
    );
}

#[test]
fn luau_branch_carried_state_stays_resolved_across_nested_loops() {
    let module =
        lower_luau_fixture_to_hir("tests/lua_cases/common/tricky/04_nested_control_flow.lua");
    let proto = &module.protos[1];
    let hir_dump = dump_hir(
        &module,
        crate::debug::DebugDetail::Normal,
        &crate::debug::DebugFilters::default(),
        crate::debug::DebugColorMode::Never,
    );

    assert!(
        !proto.body.stmts.iter().any(stmt_contains_unresolved_expr),
        "nested branch-carried loop state should not fall back to unresolved phi:\n{hir_dump}",
    );
}

#[test]
fn lua55_fixed_multiresult_call_keeps_all_fixed_defs_before_simplify() {
    let bytes = unluac_test_support::compile_lua_case(
        "lua5.5",
        "tests/lua_cases/lua5.5/05_global_const_gate.lua",
    );
    let raw = parse_lua55_chunk(&bytes, ParseOptions::default()).expect("fixture should parse");
    let lowered = lower_chunk(&raw).expect("fixture should lower into LIR");
    let cfg_graph = build_cfg_proto(&lowered.main);
    let graph_facts = analyze_graph_facts(&cfg_graph);
    let dataflow = analyze_dataflow(&lowered.main, &cfg_graph.cfg, &graph_facts, &cfg_graph.children);

    assert_eq!(
        dataflow.instr_defs[7].len(),
        2,
        "lua5.5 const gate call should define both fixed result registers",
    );

    let structure = analyze_structure(&lowered.main, &cfg_graph.cfg, &graph_facts, &dataflow, &cfg_graph.children);
    let mut artifacts = LowerArtifacts::default();
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
        &mut artifacts,
    );
    let module = HirModule {
        entry,
        protos: artifacts.protos,
    };
    let proto = &module.protos[module.entry.index()];

    assert!(
        proto.body.stmts.iter().any(|stmt| {
            matches!(
                stmt,
                HirStmt::Assign(assign)
                    if matches!(assign.targets.as_slice(), [HirLValue::Temp(_), HirLValue::Temp(_)])
                        && matches!(assign.values.as_slice(), [HirExpr::Call(call)] if call.multiret)
            )
        }),
        "fixed multiresult call should stay a two-target assign before simplify:\n{}",
        dump_hir(
            &module,
            crate::debug::DebugDetail::Verbose,
            &crate::debug::DebugFilters::default(),
            crate::debug::DebugColorMode::Never,
        ),
    );
}

#[test]
fn lua55_self_assign_branch_keeps_preserved_entry_value_before_simplify() {
    let module =
        lower_lua55_fixture_to_hir("tests/lua_cases/common/tricky/34_self_assign_branch_shell.lua");
    let proto = &module.protos[module.entry.index()];
    let hir_dump = dump_hir(
        &module,
        crate::debug::DebugDetail::Verbose,
        &crate::debug::DebugFilters::default(),
        crate::debug::DebugColorMode::Never,
    );

    let init_temp = proto
        .body
        .stmts
        .iter()
        .find_map(|stmt| match stmt {
            HirStmt::Assign(assign)
                if matches!(assign.targets.as_slice(), [HirLValue::Temp(_)])
                    && matches!(assign.values.as_slice(), [HirExpr::String(value)] if value == "x") =>
            {
                let HirLValue::Temp(temp) = assign.targets[0] else {
                    unreachable!("guard above ensures a temp target");
                };
                Some(temp)
            }
            _ => None,
        })
        .unwrap_or_else(|| {
            panic!("fixture should keep the preserved entry value temp before simplify:\n{hir_dump}")
        });
    let carried_temp = proto
        .body
        .stmts
        .iter()
        .find_map(|stmt| match stmt {
            HirStmt::Assign(assign)
                if matches!(assign.targets.as_slice(), [HirLValue::Temp(_)])
                    && matches!(assign.values.as_slice(), [HirExpr::TempRef(source)] if *source == init_temp) =>
            {
                let HirLValue::Temp(temp) = assign.targets[0] else {
                    unreachable!("guard above ensures a temp target");
                };
                Some(temp)
            }
            _ => None,
        })
        .unwrap_or_else(|| {
            panic!(
                "fixture should keep an explicit preserved-value handoff temp before simplify:\n{hir_dump}"
            )
        });
    let (if_index, if_stmt) = proto
        .body
        .stmts
        .iter()
        .enumerate()
        .find_map(|(index, stmt)| match stmt {
            HirStmt::If(if_stmt) => Some((index, if_stmt.as_ref())),
            _ => None,
        })
        .expect("fixture should still lower into a conditional rewrite before simplify");

    assert!(
        if_writes_temp_with_string(if_stmt, carried_temp, "z"),
        "conditional rewrite should keep the changed branch on the carried temp:\n{hir_dump}",
    );
    let then_writes = block_writes_temp(&if_stmt.then_block, carried_temp);
    let else_writes = if_stmt
        .else_block
        .as_ref()
        .is_some_and(|block| block_writes_temp(block, carried_temp));
    assert!(
        then_writes ^ else_writes,
        "one branch should preserve the carried temp by not reassigning it:\n{hir_dump}",
    );
    assert!(
        proto
            .body
            .stmts
            .iter()
            .skip(if_index + 1)
            .any(|stmt| stmt_mentions_temp(stmt, carried_temp)),
        "the carried temp should still be consumed after the conditional rewrite:\n{hir_dump}",
    );
}

fn lower_luau_fixture_to_hir(source_relative: &str) -> HirModule {
    let bytes = compile_luau_fixture(source_relative);
    let raw = parse_luau_chunk(&bytes, ParseOptions::default()).expect("fixture should parse");
    let lowered = lower_chunk(&raw).expect("fixture should lower into LIR");
    let cfg_graph = build_cfg_proto(&lowered.main);
    let graph_facts = analyze_graph_facts(&cfg_graph);
    let dataflow = analyze_dataflow(&lowered.main, &cfg_graph.cfg, &graph_facts, &cfg_graph.children);
    let structure = analyze_structure(&lowered.main, &cfg_graph.cfg, &graph_facts, &dataflow, &cfg_graph.children);

    let mut artifacts = LowerArtifacts::default();
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
        &mut artifacts,
    );

    HirModule {
        entry,
        protos: artifacts.protos,
    }
}

fn lower_lua55_fixture_to_hir(source_relative: &str) -> HirModule {
    let bytes = unluac_test_support::compile_lua_case("lua5.5", source_relative);
    let raw = parse_lua55_chunk(&bytes, ParseOptions::default()).expect("fixture should parse");
    let lowered = lower_chunk(&raw).expect("fixture should lower into LIR");
    let cfg_graph = build_cfg_proto(&lowered.main);
    let graph_facts = analyze_graph_facts(&cfg_graph);
    let dataflow = analyze_dataflow(&lowered.main, &cfg_graph.cfg, &graph_facts, &cfg_graph.children);
    let structure = analyze_structure(&lowered.main, &cfg_graph.cfg, &graph_facts, &dataflow, &cfg_graph.children);

    let mut artifacts = LowerArtifacts::default();
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
        &mut artifacts,
    );

    HirModule {
        entry,
        protos: artifacts.protos,
    }
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

fn stmt_contains_unresolved_expr(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::LocalDecl(local_decl) => local_decl.values.iter().any(expr_contains_unresolved),
        HirStmt::Assign(assign) => assign.values.iter().any(expr_contains_unresolved),
        HirStmt::TableSetList(set_list) => {
            expr_contains_unresolved(&set_list.base)
                || set_list.values.iter().any(expr_contains_unresolved)
                || set_list
                    .trailing_multivalue
                    .as_ref()
                    .is_some_and(expr_contains_unresolved)
        }
        HirStmt::ErrNil(err_nil) => expr_contains_unresolved(&err_nil.value),
        HirStmt::ToBeClosed(to_be_closed) => expr_contains_unresolved(&to_be_closed.value),
        HirStmt::CallStmt(call_stmt) => {
            expr_contains_unresolved(&call_stmt.call.callee)
                || call_stmt.call.args.iter().any(expr_contains_unresolved)
        }
        HirStmt::Return(ret) => ret.values.iter().any(expr_contains_unresolved),
        HirStmt::If(if_stmt) => {
            expr_contains_unresolved(&if_stmt.cond)
                || if_stmt
                    .then_block
                    .stmts
                    .iter()
                    .any(stmt_contains_unresolved_expr)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(|block| block.stmts.iter().any(stmt_contains_unresolved_expr))
        }
        HirStmt::While(while_stmt) => {
            expr_contains_unresolved(&while_stmt.cond)
                || while_stmt
                    .body
                    .stmts
                    .iter()
                    .any(stmt_contains_unresolved_expr)
        }
        HirStmt::Repeat(repeat_stmt) => {
            repeat_stmt
                .body
                .stmts
                .iter()
                .any(stmt_contains_unresolved_expr)
                || expr_contains_unresolved(&repeat_stmt.cond)
        }
        HirStmt::NumericFor(numeric_for) => {
            expr_contains_unresolved(&numeric_for.start)
                || expr_contains_unresolved(&numeric_for.limit)
                || expr_contains_unresolved(&numeric_for.step)
                || numeric_for
                    .body
                    .stmts
                    .iter()
                    .any(stmt_contains_unresolved_expr)
        }
        HirStmt::GenericFor(generic_for) => {
            generic_for.iterator.iter().any(expr_contains_unresolved)
                || generic_for
                    .body
                    .stmts
                    .iter()
                    .any(stmt_contains_unresolved_expr)
        }
        HirStmt::Block(block) => block.stmts.iter().any(stmt_contains_unresolved_expr),
        HirStmt::Unstructured(unstructured) => unstructured
            .body
            .stmts
            .iter()
            .any(stmt_contains_unresolved_expr),
        HirStmt::Break
        | HirStmt::Close(_)
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => false,
    }
}

fn if_writes_temp_with_string(
    if_stmt: &crate::hir::HirIf,
    temp: crate::hir::TempId,
    value: &str,
) -> bool {
    block_writes_temp_with_string(&if_stmt.then_block, temp, value)
        || if_stmt
            .else_block
            .as_ref()
            .is_some_and(|block| block_writes_temp_with_string(block, temp, value))
}

fn block_writes_temp_with_string(
    block: &crate::hir::HirBlock,
    temp: crate::hir::TempId,
    value: &str,
) -> bool {
    block.stmts.iter().any(|stmt| {
        matches!(
            stmt,
            HirStmt::Assign(assign)
                if matches!(assign.targets.as_slice(), [HirLValue::Temp(id)] if *id == temp)
                    && matches!(assign.values.as_slice(), [HirExpr::String(string)] if string == value)
        )
    })
}

fn block_writes_temp(block: &crate::hir::HirBlock, temp: crate::hir::TempId) -> bool {
    block.stmts.iter().any(|stmt| {
        matches!(
            stmt,
            HirStmt::Assign(assign)
                if assign
                    .targets
                    .iter()
                    .any(|target| matches!(target, HirLValue::Temp(id) if *id == temp))
        )
    })
}

fn stmt_mentions_temp(stmt: &HirStmt, temp: crate::hir::TempId) -> bool {
    match stmt {
        HirStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter()
            .any(|expr| expr_mentions_temp(expr, temp)),
        HirStmt::Assign(assign) => {
            assign
                .targets
                .iter()
                .any(|target| matches!(target, HirLValue::Temp(id) if *id == temp))
                || assign
                    .values
                    .iter()
                    .any(|expr| expr_mentions_temp(expr, temp))
        }
        HirStmt::TableSetList(set_list) => {
            expr_mentions_temp(&set_list.base, temp)
                || set_list
                    .values
                    .iter()
                    .any(|expr| expr_mentions_temp(expr, temp))
                || set_list
                    .trailing_multivalue
                    .as_ref()
                    .is_some_and(|expr| expr_mentions_temp(expr, temp))
        }
        HirStmt::ErrNil(err_nil) => expr_mentions_temp(&err_nil.value, temp),
        HirStmt::ToBeClosed(to_be_closed) => expr_mentions_temp(&to_be_closed.value, temp),
        HirStmt::CallStmt(call_stmt) => {
            expr_mentions_temp(&call_stmt.call.callee, temp)
                || call_stmt
                    .call
                    .args
                    .iter()
                    .any(|expr| expr_mentions_temp(expr, temp))
        }
        HirStmt::Return(ret) => ret.values.iter().any(|expr| expr_mentions_temp(expr, temp)),
        HirStmt::If(if_stmt) => {
            expr_mentions_temp(&if_stmt.cond, temp)
                || if_stmt
                    .then_block
                    .stmts
                    .iter()
                    .any(|stmt| stmt_mentions_temp(stmt, temp))
                || if_stmt.else_block.as_ref().is_some_and(|block| {
                    block
                        .stmts
                        .iter()
                        .any(|stmt| stmt_mentions_temp(stmt, temp))
                })
        }
        HirStmt::While(while_stmt) => {
            expr_mentions_temp(&while_stmt.cond, temp)
                || while_stmt
                    .body
                    .stmts
                    .iter()
                    .any(|stmt| stmt_mentions_temp(stmt, temp))
        }
        HirStmt::Repeat(repeat_stmt) => {
            repeat_stmt
                .body
                .stmts
                .iter()
                .any(|stmt| stmt_mentions_temp(stmt, temp))
                || expr_mentions_temp(&repeat_stmt.cond, temp)
        }
        HirStmt::NumericFor(numeric_for) => {
            expr_mentions_temp(&numeric_for.start, temp)
                || expr_mentions_temp(&numeric_for.limit, temp)
                || expr_mentions_temp(&numeric_for.step, temp)
                || numeric_for
                    .body
                    .stmts
                    .iter()
                    .any(|stmt| stmt_mentions_temp(stmt, temp))
        }
        HirStmt::GenericFor(generic_for) => {
            generic_for
                .iterator
                .iter()
                .any(|expr| expr_mentions_temp(expr, temp))
                || generic_for
                    .body
                    .stmts
                    .iter()
                    .any(|stmt| stmt_mentions_temp(stmt, temp))
        }
        HirStmt::Block(block) => block
            .stmts
            .iter()
            .any(|stmt| stmt_mentions_temp(stmt, temp)),
        HirStmt::Unstructured(unstructured) => unstructured
            .body
            .stmts
            .iter()
            .any(|stmt| stmt_mentions_temp(stmt, temp)),
        HirStmt::Break
        | HirStmt::Close(_)
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => false,
    }
}

fn expr_contains_unresolved(expr: &HirExpr) -> bool {
    match expr {
        HirExpr::Unresolved(_) => true,
        HirExpr::TableAccess(access) => {
            expr_contains_unresolved(&access.base) || expr_contains_unresolved(&access.key)
        }
        HirExpr::Unary(unary) => expr_contains_unresolved(&unary.expr),
        HirExpr::Binary(binary) => {
            expr_contains_unresolved(&binary.lhs) || expr_contains_unresolved(&binary.rhs)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_contains_unresolved(&logical.lhs) || expr_contains_unresolved(&logical.rhs)
        }
        HirExpr::Decision(decision) => decision.nodes.iter().any(|node| {
            expr_contains_unresolved(&node.test)
                || decision_target_contains_unresolved(&node.truthy)
                || decision_target_contains_unresolved(&node.falsy)
        }),
        HirExpr::Call(call) => {
            expr_contains_unresolved(&call.callee) || call.args.iter().any(expr_contains_unresolved)
        }
        HirExpr::TableConstructor(table) => table.fields.iter().any(|field| match field {
            crate::hir::common::HirTableField::Array(value) => expr_contains_unresolved(value),
            crate::hir::common::HirTableField::Record(field) => {
                matches!(
                    &field.key,
                    crate::hir::common::HirTableKey::Expr(expr) if expr_contains_unresolved(expr)
                ) || expr_contains_unresolved(&field.value)
            }
        }) || table
            .trailing_multivalue
            .as_ref()
            .is_some_and(expr_contains_unresolved),
        HirExpr::Closure(closure) => closure
            .captures
            .iter()
            .any(|capture| expr_contains_unresolved(&capture.value)),
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg => false,
    }
}

fn expr_mentions_temp(expr: &HirExpr, temp: crate::hir::TempId) -> bool {
    match expr {
        HirExpr::TempRef(id) => *id == temp,
        HirExpr::TableAccess(access) => {
            expr_mentions_temp(&access.base, temp) || expr_mentions_temp(&access.key, temp)
        }
        HirExpr::Unary(unary) => expr_mentions_temp(&unary.expr, temp),
        HirExpr::Binary(binary) => {
            expr_mentions_temp(&binary.lhs, temp) || expr_mentions_temp(&binary.rhs, temp)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_mentions_temp(&logical.lhs, temp) || expr_mentions_temp(&logical.rhs, temp)
        }
        HirExpr::Decision(decision) => decision.nodes.iter().any(|node| {
            expr_mentions_temp(&node.test, temp)
                || decision_target_mentions_temp(&node.truthy, temp)
                || decision_target_mentions_temp(&node.falsy, temp)
        }),
        HirExpr::Call(call) => {
            expr_mentions_temp(&call.callee, temp)
                || call.args.iter().any(|expr| expr_mentions_temp(expr, temp))
        }
        HirExpr::TableConstructor(table) => table.fields.iter().any(|field| match field {
            crate::hir::common::HirTableField::Array(value) => expr_mentions_temp(value, temp),
            crate::hir::common::HirTableField::Record(field) => {
                matches!(
                    &field.key,
                    crate::hir::common::HirTableKey::Expr(expr) if expr_mentions_temp(expr, temp)
                ) || expr_mentions_temp(&field.value, temp)
            }
        }) || table
            .trailing_multivalue
            .as_ref()
            .is_some_and(|expr| expr_mentions_temp(expr, temp)),
        HirExpr::Closure(closure) => closure
            .captures
            .iter()
            .any(|capture| expr_mentions_temp(&capture.value, temp)),
        HirExpr::Unresolved(_)
        | HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg => false,
    }
}

fn decision_target_contains_unresolved(target: &crate::hir::common::HirDecisionTarget) -> bool {
    match target {
        crate::hir::common::HirDecisionTarget::Expr(expr) => expr_contains_unresolved(expr),
        crate::hir::common::HirDecisionTarget::Node(_)
        | crate::hir::common::HirDecisionTarget::CurrentValue => false,
    }
}

fn decision_target_mentions_temp(
    target: &crate::hir::common::HirDecisionTarget,
    temp: crate::hir::TempId,
) -> bool {
    match target {
        crate::hir::common::HirDecisionTarget::Expr(expr) => expr_mentions_temp(expr, temp),
        crate::hir::common::HirDecisionTarget::Node(_)
        | crate::hir::common::HirDecisionTarget::CurrentValue => false,
    }
}
