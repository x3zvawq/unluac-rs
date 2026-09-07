//! 这个子模块负责从 HIR 闭包结构里提取 capture provenance。
//!
//! 它依赖 HIR 已经恢复好的 closure/capture 形状，只回答“子函数的 upvalue 来自哪里”，
//! 不会在这里分配最终名字。
//! 例如：子闭包捕获某个 local 时，这里会记录它对应的捕获来源链。

use crate::hir::traverse::{
    traverse_hir_call_children, traverse_hir_decision_children, traverse_hir_expr_children,
    traverse_hir_lvalue_children, traverse_hir_stmt_children,
    traverse_hir_table_constructor_children,
};
use crate::hir::{HirBlock, HirClosureExpr, HirExpr, HirModule, HirProtoRef, HirStmt};

use super::super::NamingError;
use super::super::common::{CapturedBinding, ClosureCaptureEvidence};

pub(super) fn build_capture_evidence(
    hir: &HirModule,
) -> Result<Vec<Option<ClosureCaptureEvidence>>, NamingError> {
    let mut evidence = vec![None; hir.protos.len()];
    for proto in &hir.protos {
        collect_capture_evidence_in_block(proto.id, &proto.body, hir, &mut evidence)?;
    }
    Ok(evidence)
}

fn collect_capture_evidence_in_block(
    function: HirProtoRef,
    block: &HirBlock,
    hir: &HirModule,
    evidence: &mut [Option<ClosureCaptureEvidence>],
) -> Result<(), NamingError> {
    for stmt in &block.stmts {
        collect_capture_evidence_in_stmt(function, stmt, hir, evidence)?;
    }
    Ok(())
}

fn collect_capture_evidence_in_stmt(
    function: HirProtoRef,
    stmt: &HirStmt,
    hir: &HirModule,
    evidence: &mut [Option<ClosureCaptureEvidence>],
) -> Result<(), NamingError> {
    traverse_hir_stmt_children!(
        stmt,
        iter = iter,
        opt = as_ref,
        borrow = [&],
        expr(e) => { collect_capture_evidence_in_expr(function, e, hir, evidence)?; },
        lvalue(l) => {
            traverse_hir_lvalue_children!(
                l,
                borrow = [&],
                expr(e) => { collect_capture_evidence_in_expr(function, e, hir, evidence)?; }
            );
        },
        release(_local) => {},
        block(b) => { collect_capture_evidence_in_block(function, b, hir, evidence)?; },
        call(c) => {
            traverse_hir_call_children!(
                c,
                iter = iter,
                borrow = [&],
                expr(e) => { collect_capture_evidence_in_expr(function, e, hir, evidence)?; }
            );
        },
        condition(c) => { collect_capture_evidence_in_expr(function, c, hir, evidence)?; }
    );
    Ok(())
}

fn collect_capture_evidence_in_expr(
    function: HirProtoRef,
    expr: &HirExpr,
    hir: &HirModule,
    evidence: &mut [Option<ClosureCaptureEvidence>],
) -> Result<(), NamingError> {
    // Closure 需要额外记录 capture provenance，先处理再让宏走结构递归
    if let HirExpr::Closure(closure) = expr {
        record_closure_capture_evidence(function, closure, hir, evidence)?;
    }
    traverse_hir_expr_children!(
        expr,
        iter = iter,
        borrow = [&],
        expr(e) => { collect_capture_evidence_in_expr(function, e, hir, evidence)?; },
        call(c) => {
            traverse_hir_call_children!(
                c,
                iter = iter,
                borrow = [&],
                expr(e) => { collect_capture_evidence_in_expr(function, e, hir, evidence)?; }
            );
        },
        decision(d) => {
            traverse_hir_decision_children!(
                d,
                iter = iter,
                borrow = [&],
                expr(e) => { collect_capture_evidence_in_expr(function, e, hir, evidence)?; },
                condition(c) => { collect_capture_evidence_in_expr(function, c, hir, evidence)?; }
            );
        },
        table_constructor(t) => {
            traverse_hir_table_constructor_children!(
                t,
                iter = iter,
                opt = as_ref,
                borrow = [&],
                expr(e) => { collect_capture_evidence_in_expr(function, e, hir, evidence)?; }
            );
        },
        capture(_capture) => {}
    );
    Ok(())
}

fn record_closure_capture_evidence(
    parent: HirProtoRef,
    closure: &HirClosureExpr,
    hir: &HirModule,
    evidence: &mut [Option<ClosureCaptureEvidence>],
) -> Result<(), NamingError> {
    let child = hir
        .protos
        .get(closure.proto.index())
        .ok_or(NamingError::MissingFunction {
            function: closure.proto.index(),
        })?;
    if closure.captures.len() != child.upvalues.len() {
        return Err(NamingError::CaptureEvidenceMismatch {
            parent: parent.index(),
            child: closure.proto.index(),
            captures: closure.captures.len(),
            upvalues: child.upvalues.len(),
        });
    }

    let candidate = ClosureCaptureEvidence {
        parent,
        captures: closure
            .captures
            .iter()
            .map(|capture| CapturedBinding {
                parent,
                binding: capture.binding,
            })
            .collect(),
    };

    match &evidence[closure.proto.index()] {
        None => {
            evidence[closure.proto.index()] = Some(candidate);
            Ok(())
        }
        Some(existing) if *existing == candidate => Ok(()),
        Some(_) => Err(NamingError::ConflictingCaptureEvidence {
            child: closure.proto.index(),
        }),
    }
}
