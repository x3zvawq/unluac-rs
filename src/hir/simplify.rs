//! 这个文件承载 HIR 的后处理收敛入口。
//!
//! 和 [analyze.rs](/Users/x3zvawq/workspace/unluac-rs/src/hir/analyze.rs) 一样，外层文件只
//! 负责声明 simplify 子模块并暴露主入口；真正的 pass 实现都放在目录内部。这样
//! `src/hir` 下两条主线在结构上保持一致，后续维护时更不容易产生“哪边是入口、哪边
//! 是细节实现”的混淆。

mod boolean_shells;
mod closure_self_capture;
pub(super) mod decision;
mod locals;
mod logical_simplify;
mod table_constructors;
mod temp_inline;

use crate::hir::common::HirModule;
use crate::readability::ReadabilityOptions;
use crate::timing::TimingCollector;

const MAX_SIMPLIFY_ITERATIONS: usize = 128;

/// 对已经构造完成的 HIR 做 fixed-point 收敛。
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn simplify_hir(module: &mut HirModule, readability: ReadabilityOptions) {
    let timings = TimingCollector::disabled();
    simplify_hir_with_timing(module, readability, &timings);
}

pub(super) fn simplify_hir_with_timing(
    module: &mut HirModule,
    readability: ReadabilityOptions,
    timings: &TimingCollector,
) {
    let mut converged = false;

    for _ in 0..MAX_SIMPLIFY_ITERATIONS {
        let changed = timings.record("fixed-point-round", || {
            let mut changed = false;
            changed |= timings.record("decision", || {
                apply_proto_pass(module, decision::simplify_decision_exprs_in_proto)
            });
            changed |= timings.record("boolean-shells", || {
                apply_proto_pass(
                    module,
                    boolean_shells::remove_boolean_materialization_shells_in_proto,
                )
            });
            changed |= timings.record("logical-simplify", || {
                apply_proto_pass(module, logical_simplify::simplify_logical_exprs_in_proto)
            });
            changed |= timings.record("table-constructors", || {
                apply_proto_pass(
                    module,
                    table_constructors::stabilize_table_constructors_in_proto,
                )
            });
            changed |= timings.record("closure-self-capture", || {
                apply_proto_pass(
                    module,
                    closure_self_capture::resolve_recursive_closure_self_captures_in_proto,
                )
            });
            changed |= timings.record("temp-inline", || {
                apply_proto_pass(module, |proto| {
                    temp_inline::inline_temps_in_proto(proto, readability)
                })
            });
            changed |= timings.record("locals", || {
                apply_proto_pass(module, locals::promote_temps_to_locals_in_proto)
            });
            changed |= timings.record("table-constructors-post-locals", || {
                // 一部分建表片段只有在 temp-inline / locals 把机械绑定收平之后才会显形，
                // 例如 `local values = {}; values[1] = ...` 这类来源于寄存器搬运的形状。
                // 这里再跑一轮相同的结构化规则，把这些“晚显形”的稳定片段也收回构造器，
                // 避免把 `table-set-list` 残留继续推给 AST。
                apply_proto_pass(
                    module,
                    table_constructors::stabilize_table_constructors_in_proto,
                )
            });
            changed |= timings.record("eliminate-decisions", || {
                apply_proto_pass(module, decision::eliminate_remaining_decisions_in_proto)
            });
            changed
        });

        if !changed {
            converged = true;
            break;
        }
    }

    if !converged {
        emit_hir_warning(format!(
            "HIR simplify exceeded {MAX_SIMPLIFY_ITERATIONS} fixed-point rounds; \
             output may still contain unstable intermediate shapes."
        ));
    }

    let residuals = collect_hir_exit_residuals(module);
    if residuals.has_soft_residuals() {
        emit_hir_warning(format!(
            "HIR exit still contains residual nodes: decision={}, unresolved={}, \
             fallback_unstructured={}, other_unstructured={}.",
            residuals.decisions,
            residuals.unresolved,
            residuals.fallback_unstructured,
            residuals.other_unstructured
        ));
    }
}

fn apply_proto_pass(
    module: &mut HirModule,
    mut pass: impl FnMut(&mut crate::hir::common::HirProto) -> bool,
) -> bool {
    let mut changed = false;
    for proto in &mut module.protos {
        changed |= pass(proto);
    }
    changed
}

pub(crate) fn synthesize_readable_pure_logical_expr(
    expr: &crate::hir::common::HirExpr,
) -> Option<crate::hir::common::HirExpr> {
    decision::synthesize_readable_pure_logical_expr(expr)
}

#[derive(Default)]
struct HirExitResiduals {
    decisions: usize,
    unresolved: usize,
    fallback_unstructured: usize,
    other_unstructured: usize,
}

impl HirExitResiduals {
    fn has_soft_residuals(&self) -> bool {
        self.decisions != 0
            || self.unresolved != 0
            || self.fallback_unstructured != 0
            || self.other_unstructured != 0
    }
}

fn collect_hir_exit_residuals(module: &HirModule) -> HirExitResiduals {
    let mut residuals = HirExitResiduals::default();
    for proto in &module.protos {
        collect_block_residuals(&proto.body, &mut residuals);
    }
    residuals
}

fn collect_block_residuals(block: &crate::hir::common::HirBlock, residuals: &mut HirExitResiduals) {
    for stmt in &block.stmts {
        collect_stmt_residuals(stmt, residuals);
    }
}

fn collect_stmt_residuals(stmt: &crate::hir::common::HirStmt, residuals: &mut HirExitResiduals) {
    match stmt {
        crate::hir::common::HirStmt::LocalDecl(local_decl) => {
            for value in &local_decl.values {
                collect_expr_residuals(value, residuals);
            }
        }
        crate::hir::common::HirStmt::Assign(assign) => {
            for target in &assign.targets {
                collect_lvalue_residuals(target, residuals);
            }
            for value in &assign.values {
                collect_expr_residuals(value, residuals);
            }
        }
        crate::hir::common::HirStmt::TableSetList(set_list) => {
            collect_expr_residuals(&set_list.base, residuals);
            for value in &set_list.values {
                collect_expr_residuals(value, residuals);
            }
            if let Some(trailing) = &set_list.trailing_multivalue {
                collect_expr_residuals(trailing, residuals);
            }
        }
        crate::hir::common::HirStmt::ErrNil(err_nil) => {
            collect_expr_residuals(&err_nil.value, residuals);
        }
        crate::hir::common::HirStmt::ToBeClosed(to_be_closed) => {
            collect_expr_residuals(&to_be_closed.value, residuals);
        }
        crate::hir::common::HirStmt::Close(_) => {}
        crate::hir::common::HirStmt::CallStmt(call_stmt) => {
            collect_call_residuals(&call_stmt.call, residuals);
        }
        crate::hir::common::HirStmt::Return(ret) => {
            for value in &ret.values {
                collect_expr_residuals(value, residuals);
            }
        }
        crate::hir::common::HirStmt::If(if_stmt) => {
            collect_expr_residuals(&if_stmt.cond, residuals);
            collect_block_residuals(&if_stmt.then_block, residuals);
            if let Some(else_block) = &if_stmt.else_block {
                collect_block_residuals(else_block, residuals);
            }
        }
        crate::hir::common::HirStmt::While(while_stmt) => {
            collect_expr_residuals(&while_stmt.cond, residuals);
            collect_block_residuals(&while_stmt.body, residuals);
        }
        crate::hir::common::HirStmt::Repeat(repeat_stmt) => {
            collect_block_residuals(&repeat_stmt.body, residuals);
            collect_expr_residuals(&repeat_stmt.cond, residuals);
        }
        crate::hir::common::HirStmt::NumericFor(numeric_for) => {
            collect_expr_residuals(&numeric_for.start, residuals);
            collect_expr_residuals(&numeric_for.limit, residuals);
            collect_expr_residuals(&numeric_for.step, residuals);
            collect_block_residuals(&numeric_for.body, residuals);
        }
        crate::hir::common::HirStmt::GenericFor(generic_for) => {
            for expr in &generic_for.iterator {
                collect_expr_residuals(expr, residuals);
            }
            collect_block_residuals(&generic_for.body, residuals);
        }
        crate::hir::common::HirStmt::Block(block) => collect_block_residuals(block, residuals),
        crate::hir::common::HirStmt::Unstructured(unstructured) => {
            if unstructured
                .summary
                .as_deref()
                .is_some_and(|summary| summary.contains("fallback"))
            {
                residuals.fallback_unstructured += 1;
            } else {
                residuals.other_unstructured += 1;
            }
            collect_block_residuals(&unstructured.body, residuals);
        }
        crate::hir::common::HirStmt::Break
        | crate::hir::common::HirStmt::Continue
        | crate::hir::common::HirStmt::Goto(_)
        | crate::hir::common::HirStmt::Label(_) => {}
    }
}

fn collect_lvalue_residuals(
    lvalue: &crate::hir::common::HirLValue,
    residuals: &mut HirExitResiduals,
) {
    if let crate::hir::common::HirLValue::TableAccess(access) = lvalue {
        collect_expr_residuals(&access.base, residuals);
        collect_expr_residuals(&access.key, residuals);
    }
}

fn collect_call_residuals(
    call: &crate::hir::common::HirCallExpr,
    residuals: &mut HirExitResiduals,
) {
    collect_expr_residuals(&call.callee, residuals);
    for arg in &call.args {
        collect_expr_residuals(arg, residuals);
    }
}

fn collect_expr_residuals(expr: &crate::hir::common::HirExpr, residuals: &mut HirExitResiduals) {
    match expr {
        crate::hir::common::HirExpr::Decision(decision) => {
            residuals.decisions += 1;
            for node in &decision.nodes {
                collect_expr_residuals(&node.test, residuals);
                collect_decision_target_residuals(&node.truthy, residuals);
                collect_decision_target_residuals(&node.falsy, residuals);
            }
        }
        crate::hir::common::HirExpr::Unresolved(_) => {
            residuals.unresolved += 1;
        }
        crate::hir::common::HirExpr::TableAccess(access) => {
            collect_expr_residuals(&access.base, residuals);
            collect_expr_residuals(&access.key, residuals);
        }
        crate::hir::common::HirExpr::Unary(unary) => {
            collect_expr_residuals(&unary.expr, residuals);
        }
        crate::hir::common::HirExpr::Binary(binary) => {
            collect_expr_residuals(&binary.lhs, residuals);
            collect_expr_residuals(&binary.rhs, residuals);
        }
        crate::hir::common::HirExpr::LogicalAnd(logical)
        | crate::hir::common::HirExpr::LogicalOr(logical) => {
            collect_expr_residuals(&logical.lhs, residuals);
            collect_expr_residuals(&logical.rhs, residuals);
        }
        crate::hir::common::HirExpr::Call(call) => {
            collect_call_residuals(call, residuals);
        }
        crate::hir::common::HirExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    crate::hir::common::HirTableField::Array(expr) => {
                        collect_expr_residuals(expr, residuals);
                    }
                    crate::hir::common::HirTableField::Record(field) => {
                        if let crate::hir::common::HirTableKey::Expr(expr) = &field.key {
                            collect_expr_residuals(expr, residuals);
                        }
                        collect_expr_residuals(&field.value, residuals);
                    }
                }
            }
            if let Some(trailing) = &table.trailing_multivalue {
                collect_expr_residuals(trailing, residuals);
            }
        }
        crate::hir::common::HirExpr::Closure(closure) => {
            for capture in &closure.captures {
                collect_expr_residuals(&capture.value, residuals);
            }
        }
        crate::hir::common::HirExpr::Nil
        | crate::hir::common::HirExpr::Boolean(_)
        | crate::hir::common::HirExpr::Integer(_)
        | crate::hir::common::HirExpr::Number(_)
        | crate::hir::common::HirExpr::String(_)
        | crate::hir::common::HirExpr::ParamRef(_)
        | crate::hir::common::HirExpr::LocalRef(_)
        | crate::hir::common::HirExpr::UpvalueRef(_)
        | crate::hir::common::HirExpr::TempRef(_)
        | crate::hir::common::HirExpr::GlobalRef(_)
        | crate::hir::common::HirExpr::VarArg => {}
    }
}

fn collect_decision_target_residuals(
    target: &crate::hir::common::HirDecisionTarget,
    residuals: &mut HirExitResiduals,
) {
    match target {
        crate::hir::common::HirDecisionTarget::Node(_)
        | crate::hir::common::HirDecisionTarget::CurrentValue => {}
        crate::hir::common::HirDecisionTarget::Expr(expr) => {
            collect_expr_residuals(expr, residuals);
        }
    }
}

fn emit_hir_warning(message: String) {
    eprintln!("[unluac][hir-warning] {message}");
}
