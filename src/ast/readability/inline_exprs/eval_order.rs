//! 相邻单候选和多候选 run 搬运前的求值顺序证明。
//!
//! inline 会把声明 RHS 搬进 sink。这里把可观察 RHS 与 binding 值快照当成有序事件，
//! 递归展开它们之间的依赖，并要求这些事件仍是 sink 的同序前缀；任一 retained 有序
//! 声明或 sink 自身的状态事件都会形成屏障。table lvalue 的写入发生在 RHS 之后，只有
//! base/key 自身的事件构成前缀；method lookup 则位于 receiver 与显式参数之间。
//! 循环头还要求搬入 RHS 无事件且循环不变：递归展开已删除候选，外部 local/param
//! 必须未捕获并且循环体没有直接写入；未知读取和可能触发元方法的运算一律拒绝。
//! 合法顺序声明的候选依赖只会指向更早语句；递归环表示上游破坏了 binding 不变量。

use std::collections::{BTreeMap, BTreeSet};

use crate::ast::common::{
    AstBindingRef, AstCallKind, AstExpr, AstLValue, AstNameRef, AstStmt, AstTableField,
    AstTableKey, AstUnaryOpKind,
};

use super::super::binding_ref::binding_from_name_ref;
use super::super::expr_analysis::{
    expr_observes_eval_order, expr_requires_ordered_snapshot, is_eventless_primitive_literal,
};
use super::BindingWriteIndex;
use super::candidate::inline_candidate;

pub(super) fn preserves_adjacent_eval_order(
    sink: &AstStmt,
    binding: AstBindingRef,
    value: &AstExpr,
    mutable_snapshots: &BTreeSet<AstNameRef>,
) -> bool {
    let values = BTreeMap::from([(binding, value)]);
    let mut collector = EvalPrefixCollector {
        values: &values,
        ordered: BTreeSet::from([binding]),
        mutable_snapshots,
        visiting: BTreeSet::new(),
        emitted: BTreeSet::new(),
        prefix: Vec::new(),
        blocked: false,
    };
    collector.stmt(sink);
    !collector.blocked && collector.prefix == [binding]
}

pub(super) fn run_preserves_eval_order(
    stmts: &[AstStmt],
    run_start: usize,
    sink_index: usize,
    removed: &[bool],
    mutable_snapshots: &BTreeSet<AstNameRef>,
    write_index: &BindingWriteIndex,
) -> bool {
    let candidates = stmts[run_start..sink_index]
        .iter()
        .zip(removed)
        .filter_map(|(stmt, removed)| {
            let (candidate, value) = inline_candidate(stmt)?;
            (*removed).then_some((candidate.binding(), value))
        })
        .collect::<Vec<_>>();
    let values = candidates.iter().copied().collect::<BTreeMap<_, _>>();
    if matches!(stmts[sink_index], AstStmt::While(_) | AstStmt::Repeat(_))
        && candidates.iter().any(|(_, value)| {
            !loop_header_rhs_is_invariant(
                value,
                &values,
                sink_index,
                mutable_snapshots,
                write_index,
                &mut BTreeSet::new(),
            )
        })
    {
        // 候选拒绝[SemanticBarrier:EvalTime/EvalCount]：循环内可写快照或 lookup/call/元方法事件搬入循环头会改成体后重读或逐轮执行（regress_355、regress_373_loop_lookup_eval_count）；候选拒绝[ProofIncomplete]：只读 capture/upvalue、VarArg 单值位置及无事件运算仍缺少写入、值宽度或目标类型事实。
        return false;
    }
    let expected = candidates
        .iter()
        .filter_map(|(binding, value)| {
            expr_requires_ordered_snapshot(value, mutable_snapshots).then_some(*binding)
        })
        .collect::<Vec<_>>();
    if expected.is_empty() {
        return true;
    }

    let first_moved = expected[0];
    let mut reached_first = false;
    for (stmt, removed) in stmts[run_start..sink_index].iter().zip(removed) {
        let Some((candidate, value)) = inline_candidate(stmt) else {
            continue;
        };
        reached_first |= candidate.binding() == first_moved;
        if reached_first && !removed && expr_requires_ordered_snapshot(value, mutable_snapshots) {
            // 候选拒绝[SemanticBarrier:EvalOrder]：已移动事件之后仍保留有序 producer，会把原声明顺序交错成 sink 内的另一顺序。
            return false;
        }
    }

    let mut collector = EvalPrefixCollector {
        values: &values,
        ordered: expected.iter().copied().collect(),
        mutable_snapshots,
        visiting: BTreeSet::new(),
        emitted: BTreeSet::new(),
        prefix: Vec::new(),
        blocked: false,
    };
    collector.stmt(&stmts[sink_index]);
    !collector.blocked && collector.prefix == expected
}

fn loop_header_rhs_is_invariant(
    value: &AstExpr,
    removed_values: &BTreeMap<AstBindingRef, &AstExpr>,
    loop_stmt_index: usize,
    mutable_snapshots: &BTreeSet<AstNameRef>,
    write_index: &BindingWriteIndex,
    visiting: &mut BTreeSet<AstBindingRef>,
) -> bool {
    if is_eventless_primitive_literal(value) {
        return true;
    }

    match value {
        AstExpr::Var(name) => {
            if let Some(binding) = binding_from_name_ref(name)
                && let Some(candidate_value) = removed_values.get(&binding)
            {
                assert!(
                    visiting.insert(binding),
                    "inline candidate dependency must point to an earlier local declaration"
                );
                let invariant = loop_header_rhs_is_invariant(
                    candidate_value,
                    removed_values,
                    loop_stmt_index,
                    mutable_snapshots,
                    write_index,
                    visiting,
                );
                visiting.remove(&binding);
                return invariant;
            }

            matches!(
                name,
                AstNameRef::Param(_) | AstNameRef::Local(_) | AstNameRef::SyntheticLocal(_)
            ) && !mutable_snapshots.contains(name)
                && !write_index.stmt_directly_writes_name(loop_stmt_index, name)
        }
        AstExpr::Unary(unary) if unary.op == AstUnaryOpKind::Not => loop_header_rhs_is_invariant(
            &unary.expr,
            removed_values,
            loop_stmt_index,
            mutable_snapshots,
            write_index,
            visiting,
        ),
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            loop_header_rhs_is_invariant(
                &logical.lhs,
                removed_values,
                loop_stmt_index,
                mutable_snapshots,
                write_index,
                visiting,
            ) && loop_header_rhs_is_invariant(
                &logical.rhs,
                removed_values,
                loop_stmt_index,
                mutable_snapshots,
                write_index,
                visiting,
            )
        }
        AstExpr::SingleValue(inner) => loop_header_rhs_is_invariant(
            inner,
            removed_values,
            loop_stmt_index,
            mutable_snapshots,
            write_index,
            visiting,
        ),
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Vector(_)
        | AstExpr::Complex { .. }
        | AstExpr::FieldAccess(_)
        | AstExpr::IndexAccess(_)
        | AstExpr::Unary(_)
        | AstExpr::Binary(_)
        | AstExpr::Call(_)
        | AstExpr::MethodCall(_)
        | AstExpr::VarArg
        | AstExpr::TableConstructor(_)
        | AstExpr::FunctionExpr(_)
        | AstExpr::Error(_) => false,
    }
}

struct EvalPrefixCollector<'a> {
    values: &'a BTreeMap<AstBindingRef, &'a AstExpr>,
    ordered: BTreeSet<AstBindingRef>,
    mutable_snapshots: &'a BTreeSet<AstNameRef>,
    visiting: BTreeSet<AstBindingRef>,
    emitted: BTreeSet<AstBindingRef>,
    prefix: Vec<AstBindingRef>,
    blocked: bool,
}

impl EvalPrefixCollector<'_> {
    fn barrier(&mut self) {
        // 候选拒绝[SemanticBarrier:EvalOrder]：尚未发射的 producer 若位于该调用/lookup/控制事件之后，内联会改变可观察事件前缀。
        self.blocked |= self.prefix.len() < self.ordered.len();
    }

    fn snapshot_barrier(&mut self) {
        self.blocked |= self.values.iter().any(|(binding, value)| {
            self.ordered.contains(binding)
                && !self.emitted.contains(binding)
                && expr_observes_eval_order(value)
        });
    }

    fn stmt(&mut self, stmt: &AstStmt) {
        match stmt {
            AstStmt::LocalDecl(decl) => self.exprs(&decl.values, WalkMode::Sink),
            AstStmt::GlobalDecl(decl) => self.exprs(&decl.values, WalkMode::Sink),
            AstStmt::Assign(assign) => {
                for target in &assign.targets {
                    self.lvalue(target);
                }
                self.exprs(&assign.values, WalkMode::Sink);
            }
            AstStmt::CallStmt(call) => self.call(&call.call),
            AstStmt::Return(ret) => self.exprs(&ret.values, WalkMode::Sink),
            AstStmt::If(stmt) => self.expr(&stmt.cond, WalkMode::Sink),
            AstStmt::While(stmt) => self.expr(&stmt.cond, WalkMode::Sink),
            AstStmt::Repeat(stmt) => self.expr(&stmt.cond, WalkMode::Sink),
            AstStmt::NumericFor(stmt) => {
                self.expr(&stmt.start, WalkMode::Sink);
                self.expr(&stmt.limit, WalkMode::Sink);
                self.expr(&stmt.step, WalkMode::Sink);
            }
            AstStmt::GenericFor(stmt) => self.exprs(&stmt.iterator, WalkMode::Sink),
            AstStmt::DoBlock(_)
            | AstStmt::FunctionDecl(_)
            | AstStmt::LocalFunctionDecl(_)
            | AstStmt::Break
            | AstStmt::Continue
            | AstStmt::Goto(_)
            | AstStmt::Label(_)
            | AstStmt::Error(_) => self.barrier(),
        }
    }

    fn lvalue(&mut self, value: &AstLValue) {
        if self.blocked {
            return;
        }
        match value {
            AstLValue::Name(_) => {}
            AstLValue::FieldAccess(access) => {
                self.expr(&access.base, WalkMode::Sink);
            }
            AstLValue::IndexAccess(access) => {
                self.expr(&access.base, WalkMode::Sink);
                self.expr(&access.index, WalkMode::Sink);
            }
        }
    }

    fn call(&mut self, call: &AstCallKind) {
        match call {
            AstCallKind::Call(call) => {
                self.expr(&call.callee, WalkMode::Sink);
                self.exprs(&call.args, WalkMode::Sink);
            }
            AstCallKind::MethodCall(call) => {
                self.expr(&call.receiver, WalkMode::Sink);
                self.barrier();
                self.exprs(&call.args, WalkMode::Sink);
            }
        }
        self.barrier();
    }

    fn exprs(&mut self, values: &[AstExpr], mode: WalkMode) {
        for value in values {
            self.expr(value, mode);
        }
    }

    fn expr(&mut self, value: &AstExpr, mode: WalkMode) {
        if self.blocked {
            return;
        }
        if let AstExpr::Var(name) = value
            && let Some(binding) = binding_from_name_ref(name)
            && self.values.contains_key(&binding)
        {
            self.candidate(binding);
            return;
        }

        match value {
            AstExpr::FieldAccess(access) => self.expr(&access.base, mode),
            AstExpr::IndexAccess(access) => {
                self.expr(&access.base, mode);
                self.expr(&access.index, mode);
            }
            AstExpr::Unary(unary) => self.expr(&unary.expr, mode),
            AstExpr::Binary(binary) => {
                self.expr(&binary.lhs, mode);
                self.expr(&binary.rhs, mode);
            }
            AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
                self.expr(&logical.lhs, mode);
                if matches!(mode, WalkMode::Dependency)
                    && contains_moved_binding(&logical.rhs, self.values)
                {
                    // 候选拒绝[SemanticBarrier:ControlFlow]：把必达声明搬进 `and/or` 右臂会让 producer 受左值 truthiness 控制。
                    self.barrier();
                }
            }
            AstExpr::Call(call) => {
                self.expr(&call.callee, mode);
                self.exprs(&call.args, mode);
            }
            AstExpr::MethodCall(call) => {
                self.expr(&call.receiver, mode);
                if matches!(mode, WalkMode::Sink)
                    || call
                        .args
                        .iter()
                        .any(|arg| contains_moved_binding(arg, self.values))
                {
                    self.barrier();
                }
                self.exprs(&call.args, mode);
            }
            AstExpr::SingleValue(value) => self.expr(value, mode),
            AstExpr::TableConstructor(table) => {
                for field in &table.fields {
                    match field {
                        AstTableField::Array(value) => self.expr(value, mode),
                        AstTableField::Record(field) => {
                            if let AstTableKey::Expr(key) = &field.key {
                                self.expr(key, mode);
                            }
                            self.expr(&field.value, mode);
                        }
                    }
                }
            }
            AstExpr::FunctionExpr(_) if matches!(mode, WalkMode::Dependency) => {
                // 候选拒绝[SemanticBarrier:Capture]：closure dependency 会把声明时捕获改成 sink 时创建/捕获，生命周期与值快照均可能改变。
                self.barrier();
            }
            AstExpr::Nil
            | AstExpr::Boolean(_)
            | AstExpr::Integer(_)
            | AstExpr::Number(_)
            | AstExpr::String(_)
            | AstExpr::Int64(_)
            | AstExpr::UInt64(_)
            | AstExpr::Vector(_)
            | AstExpr::Complex { .. }
            | AstExpr::Var(_)
            | AstExpr::VarArg
            | AstExpr::FunctionExpr(_)
            | AstExpr::Error(_) => {}
        }
        if matches!(mode, WalkMode::Sink) {
            if expr_observes_eval_order(value) || matches!(value, AstExpr::VarArg) {
                self.barrier();
            } else if expr_requires_ordered_snapshot(value, self.mutable_snapshots) {
                self.snapshot_barrier();
            }
        }
    }

    fn candidate(&mut self, binding: AstBindingRef) {
        if !self.visiting.insert(binding) || !self.emitted.insert(binding) {
            // 候选拒绝[SemanticBarrier:EvalCount]：循环依赖或同一候选在 sink 出现多次会递归/复制 RHS，不能保持一次求值。
            self.barrier();
            return;
        }
        let value = self.values[&binding];
        self.expr(value, WalkMode::Dependency);
        self.visiting.remove(&binding);
        if !self.blocked && self.ordered.contains(&binding) {
            self.prefix.push(binding);
        }
    }
}

#[derive(Clone, Copy)]
enum WalkMode {
    Sink,
    Dependency,
}

fn contains_moved_binding(value: &AstExpr, values: &BTreeMap<AstBindingRef, &AstExpr>) -> bool {
    values
        .keys()
        .any(|binding| super::super::binding_tree::expr_references_binding(value, *binding))
}
