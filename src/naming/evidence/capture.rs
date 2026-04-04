//! 这个子模块负责从 HIR 闭包结构里提取 capture provenance。
//!
//! 它依赖 HIR 已经恢复好的 closure/capture 形状，只回答“子函数的 upvalue 来自哪里”，
//! 不会在这里分配最终名字。
//! 例如：子闭包捕获某个 local 时，这里会记录它对应的捕获来源链。

use crate::hir::{
    HirBlock, HirClosureExpr, HirDecisionTarget, HirExpr, HirLValue, HirModule, HirProtoRef,
    HirStmt, HirTableField, HirTableKey,
};

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
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            for value in &local_decl.values {
                collect_capture_evidence_in_expr(function, value, hir, evidence)?;
            }
        }
        HirStmt::Assign(assign) => {
            for target in &assign.targets {
                if let HirLValue::TableAccess(access) = target {
                    collect_capture_evidence_in_expr(function, &access.base, hir, evidence)?;
                    collect_capture_evidence_in_expr(function, &access.key, hir, evidence)?;
                }
            }
            for value in &assign.values {
                collect_capture_evidence_in_expr(function, value, hir, evidence)?;
            }
        }
        HirStmt::TableSetList(set_list) => {
            collect_capture_evidence_in_expr(function, &set_list.base, hir, evidence)?;
            for value in &set_list.values {
                collect_capture_evidence_in_expr(function, value, hir, evidence)?;
            }
            if let Some(expr) = &set_list.trailing_multivalue {
                collect_capture_evidence_in_expr(function, expr, hir, evidence)?;
            }
        }
        HirStmt::ErrNil(err_nil) => {
            collect_capture_evidence_in_expr(function, &err_nil.value, hir, evidence)?;
        }
        HirStmt::ToBeClosed(to_be_closed) => {
            collect_capture_evidence_in_expr(function, &to_be_closed.value, hir, evidence)?;
        }
        HirStmt::CallStmt(call_stmt) => {
            collect_capture_evidence_in_expr(function, &call_stmt.call.callee, hir, evidence)?;
            for arg in &call_stmt.call.args {
                collect_capture_evidence_in_expr(function, arg, hir, evidence)?;
            }
        }
        HirStmt::Return(ret) => {
            for value in &ret.values {
                collect_capture_evidence_in_expr(function, value, hir, evidence)?;
            }
        }
        HirStmt::If(if_stmt) => {
            collect_capture_evidence_in_expr(function, &if_stmt.cond, hir, evidence)?;
            collect_capture_evidence_in_block(function, &if_stmt.then_block, hir, evidence)?;
            if let Some(else_block) = &if_stmt.else_block {
                collect_capture_evidence_in_block(function, else_block, hir, evidence)?;
            }
        }
        HirStmt::While(while_stmt) => {
            collect_capture_evidence_in_expr(function, &while_stmt.cond, hir, evidence)?;
            collect_capture_evidence_in_block(function, &while_stmt.body, hir, evidence)?;
        }
        HirStmt::Repeat(repeat_stmt) => {
            collect_capture_evidence_in_block(function, &repeat_stmt.body, hir, evidence)?;
            collect_capture_evidence_in_expr(function, &repeat_stmt.cond, hir, evidence)?;
        }
        HirStmt::NumericFor(numeric_for) => {
            collect_capture_evidence_in_expr(function, &numeric_for.start, hir, evidence)?;
            collect_capture_evidence_in_expr(function, &numeric_for.limit, hir, evidence)?;
            collect_capture_evidence_in_expr(function, &numeric_for.step, hir, evidence)?;
            collect_capture_evidence_in_block(function, &numeric_for.body, hir, evidence)?;
        }
        HirStmt::GenericFor(generic_for) => {
            for iterator in &generic_for.iterator {
                collect_capture_evidence_in_expr(function, iterator, hir, evidence)?;
            }
            collect_capture_evidence_in_block(function, &generic_for.body, hir, evidence)?;
        }
        HirStmt::Block(block) => collect_capture_evidence_in_block(function, block, hir, evidence)?,
        HirStmt::Unstructured(unstructured) => {
            collect_capture_evidence_in_block(function, &unstructured.body, hir, evidence)?;
        }
        HirStmt::Close(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => {}
    }
    Ok(())
}

fn collect_capture_evidence_in_expr(
    function: HirProtoRef,
    expr: &HirExpr,
    hir: &HirModule,
    evidence: &mut [Option<ClosureCaptureEvidence>],
) -> Result<(), NamingError> {
    match expr {
        HirExpr::TableAccess(access) => {
            collect_capture_evidence_in_expr(function, &access.base, hir, evidence)?;
            collect_capture_evidence_in_expr(function, &access.key, hir, evidence)?;
        }
        HirExpr::Unary(unary) => {
            collect_capture_evidence_in_expr(function, &unary.expr, hir, evidence)?;
        }
        HirExpr::Binary(binary) => {
            collect_capture_evidence_in_expr(function, &binary.lhs, hir, evidence)?;
            collect_capture_evidence_in_expr(function, &binary.rhs, hir, evidence)?;
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            collect_capture_evidence_in_expr(function, &logical.lhs, hir, evidence)?;
            collect_capture_evidence_in_expr(function, &logical.rhs, hir, evidence)?;
        }
        HirExpr::Decision(decision) => {
            for node in &decision.nodes {
                collect_capture_evidence_in_expr(function, &node.test, hir, evidence)?;
                collect_capture_evidence_in_decision_target(function, &node.truthy, hir, evidence)?;
                collect_capture_evidence_in_decision_target(function, &node.falsy, hir, evidence)?;
            }
        }
        HirExpr::Call(call) => {
            collect_capture_evidence_in_expr(function, &call.callee, hir, evidence)?;
            for arg in &call.args {
                collect_capture_evidence_in_expr(function, arg, hir, evidence)?;
            }
        }
        HirExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    HirTableField::Array(value) => {
                        collect_capture_evidence_in_expr(function, value, hir, evidence)?;
                    }
                    HirTableField::Record(field) => {
                        if let HirTableKey::Expr(key) = &field.key {
                            collect_capture_evidence_in_expr(function, key, hir, evidence)?;
                        }
                        collect_capture_evidence_in_expr(function, &field.value, hir, evidence)?;
                    }
                }
            }
            if let Some(expr) = &table.trailing_multivalue {
                collect_capture_evidence_in_expr(function, expr, hir, evidence)?;
            }
        }
        HirExpr::Closure(closure) => {
            record_closure_capture_evidence(function, closure, hir, evidence)?;
            for capture in &closure.captures {
                collect_capture_evidence_in_expr(function, &capture.value, hir, evidence)?;
            }
        }
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
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => {}
    }
    Ok(())
}

fn collect_capture_evidence_in_decision_target(
    function: HirProtoRef,
    target: &HirDecisionTarget,
    hir: &HirModule,
    evidence: &mut [Option<ClosureCaptureEvidence>],
) -> Result<(), NamingError> {
    if let HirDecisionTarget::Expr(expr) = target {
        collect_capture_evidence_in_expr(function, expr, hir, evidence)?;
    }
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
            .map(|capture| captured_binding_from_expr(parent, &capture.value))
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

fn captured_binding_from_expr(parent: HirProtoRef, expr: &HirExpr) -> Option<CapturedBinding> {
    match expr {
        HirExpr::ParamRef(param) => Some(CapturedBinding::Param {
            parent,
            param: *param,
        }),
        HirExpr::LocalRef(local) => Some(CapturedBinding::Local {
            parent,
            local: *local,
        }),
        HirExpr::TempRef(temp) => Some(CapturedBinding::Temp {
            parent,
            temp: *temp,
        }),
        HirExpr::UpvalueRef(upvalue) => Some(CapturedBinding::Upvalue {
            parent,
            upvalue: *upvalue,
        }),
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::TableAccess(_)
        | HirExpr::Unary(_)
        | HirExpr::Binary(_)
        | HirExpr::LogicalAnd(_)
        | HirExpr::LogicalOr(_)
        | HirExpr::Decision(_)
        | HirExpr::Call(_)
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => None,
    }
}
