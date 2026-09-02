//! raw temp branch-value 树的单次 Decision 构建器。
//!
//! Structure/HIR lowering 可能把一条长短路值链展开成多层 `assign guard; if guard`。
//! 父 pass 已证明候选只为同一 binding 选值；这里一次遍历整棵树，增量携带 local/temp
//! 引用事实并建立 root-first Decision，最后只做一次 value finalize。它不会决定候选是否
//! 能跨出根语句，也不会处理 local 壳或 goto/label 壳。
//!
//! 例子：`t0=a; if t0 then out=t0 else t1=b; if t1 ... end end` 会先建成两个 Decision
//! 节点，再一次收敛为 `out = a or b or ...`，而不是每深入一层重扫和 clone 已构造子树。

use std::collections::BTreeSet;

use super::{BranchValueBinding, raw_temp_guard_shape, single_assign_value};
use crate::hir::common::{
    HirBlock, HirDecisionExpr, HirDecisionNode, HirDecisionNodeRef, HirDecisionTarget, HirExpr,
    HirIf, HirLocalDecl, HirStmt, TempId,
};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::simplify::visit::{HirVisitor, visit_expr};

#[derive(Default)]
struct BindingRefs(BTreeSet<BranchValueBinding>);

impl BindingRefs {
    fn in_expr(expr: &HirExpr) -> Self {
        let mut collector = BindingRefCollector::default();
        visit_expr(expr, &mut collector);
        collector.refs
    }

    fn merge(&mut self, other: Self) {
        let mut other = other.0;
        if self.0.len() < other.len() {
            std::mem::swap(&mut self.0, &mut other);
        }
        self.0.extend(other);
    }

    fn mentions(&self, binding: BranchValueBinding) -> bool {
        self.0.contains(&binding)
    }
}

#[derive(Default)]
struct BindingRefCollector {
    refs: BindingRefs,
}

impl HirVisitor for BindingRefCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        match expr {
            HirExpr::LocalRef(local) => {
                self.refs.0.insert(BranchValueBinding::Local(*local));
            }
            HirExpr::TempRef(temp) => {
                self.refs.0.insert(BranchValueBinding::Temp(*temp));
            }
            _ => {}
        }
    }
}

pub(super) struct CollapsedBranchValueTarget {
    target: HirDecisionTarget,
    refs: BindingRefs,
}

pub(super) struct BranchValueDecisionBuilder {
    nodes: Vec<HirDecisionNode>,
    raw_guards: BTreeSet<TempId>,
    safety: HirExprSafety,
}

impl BranchValueDecisionBuilder {
    pub(super) fn new(safety: HirExprSafety) -> Self {
        Self {
            nodes: Vec::new(),
            raw_guards: BTreeSet::new(),
            safety,
        }
    }

    pub(super) fn collapse_if(
        &mut self,
        if_stmt: &HirIf,
        binding: BranchValueBinding,
    ) -> Option<CollapsedBranchValueTarget> {
        let (node_ref, mut refs) = self.reserve_node(&if_stmt.cond);
        let truthy = self.collapse_block(&if_stmt.then_block, binding)?;
        // 候选拒绝[SemanticBarrier:ControlFlow]：无 else 时 false-path 保留 binding 旧值；改成有值 Decision 会凭空定义该路径。
        let falsy = self.collapse_block(if_stmt.else_block.as_ref()?, binding)?;
        self.complete_node(node_ref, truthy.target, falsy.target);
        refs.merge(truthy.refs);
        refs.merge(falsy.refs);
        Some(CollapsedBranchValueTarget {
            target: HirDecisionTarget::Node(node_ref),
            refs,
        })
    }

    fn collapse_block(
        &mut self,
        block: &HirBlock,
        binding: BranchValueBinding,
    ) -> Option<CollapsedBranchValueTarget> {
        // 这个 block grammar 只把 binding 写在终端叶上，因此树中收集到的
        // binding ref 都读候选入口 epoch，可以原样留在最终单次赋值的 RHS。
        // 唯一会提前写 binding 的原地 raw guard 在 collapse_raw_temp_guard
        // 单独证明其 continuation 不再读该 epoch。
        match block.stmts.as_slice() {
            [HirStmt::Assign(assign)] => {
                let expr = single_assign_value(assign, binding)?;
                Some(CollapsedBranchValueTarget {
                    target: HirDecisionTarget::Expr(expr.clone()),
                    refs: BindingRefs::in_expr(expr),
                })
            }
            [HirStmt::If(if_stmt)] => self.collapse_if(if_stmt, binding),
            [HirStmt::LocalDecl(decl), HirStmt::If(if_stmt)] => {
                self.collapse_local_guard(decl, if_stmt, binding)
            }
            [assign_stmt @ HirStmt::Assign(_), if_stmt @ HirStmt::If(_)] => {
                self.collapse_raw_temp_guard(assign_stmt, if_stmt, binding)
            }
            // 其它语句序列不属于 raw branch-value 的终端叶 grammar；保留控制树后，
            // effect/control prefix 仍在原路径执行，不在这个 builder 内建立候选。
            _ => None,
        }
    }

    fn collapse_local_guard(
        &mut self,
        decl: &HirLocalDecl,
        if_stmt: &HirIf,
        binding: BranchValueBinding,
    ) -> Option<CollapsedBranchValueTarget> {
        let [guard] = decl.bindings.as_slice() else {
            return None;
        };
        let [value] = decl.values.fixed.as_slice() else {
            return None;
        };
        if decl.values.tail.is_some()
            || !matches!(if_stmt.cond, HirExpr::LocalRef(local) if local == *guard)
        {
            return None;
        }
        let [HirStmt::Assign(then_assign)] = if_stmt.then_block.stmts.as_slice() else {
            return None;
        };
        if !matches!(single_assign_value(then_assign, binding)?, HirExpr::LocalRef(local) if local == guard)
        {
            return None;
        }

        let (node_ref, mut refs) = self.reserve_node(value);
        // 候选拒绝[SemanticBarrier:ControlFlow]：local guard 无 else 时 false-path 保留 binding 旧值，不能构造成总有结果的 Decision。
        let rest = self.collapse_block(if_stmt.else_block.as_ref()?, binding)?;
        let guard = BranchValueBinding::Local(*guard);
        // 候选拒绝[SemanticBarrier:Scope]：删除 local guard 壳后，对该 guard 的剩余读取会改指外层或失去其声明 identity。
        if refs.mentions(guard) || rest.refs.mentions(guard) {
            return None;
        }
        self.complete_node(node_ref, HirDecisionTarget::CurrentValue, rest.target);
        refs.merge(rest.refs);
        Some(CollapsedBranchValueTarget {
            target: HirDecisionTarget::Node(node_ref),
            refs,
        })
    }

    fn collapse_raw_temp_guard(
        &mut self,
        assign_stmt: &HirStmt,
        if_stmt: &HirStmt,
        binding: BranchValueBinding,
    ) -> Option<CollapsedBranchValueTarget> {
        let shape = raw_temp_guard_shape(assign_stmt, if_stmt)?;
        if shape.binding != binding {
            return None;
        }

        let (node_ref, mut refs) = self.reserve_node(shape.value);
        let rest = self.collapse_block(shape.rest_block, binding)?;
        let guard = BranchValueBinding::Temp(shape.guard);
        let updates_binding = guard == binding;
        // 候选拒绝[SemanticBarrier:ValueFlow]：独立 raw guard 的 producer 会被删除，
        // value/rest 若再读 guard 会改读旧 epoch 或未定义值。原地 guard 则会被合并
        // 成同一个 binding 的最终赋值：value 还在写前读入站 epoch，但 rest 原本在
        // guard 写后读新 epoch，不能移进还未完成赋值的 RHS。
        if rest.refs.mentions(guard) || (!updates_binding && refs.mentions(guard)) {
            return None;
        }
        let rest_target = rest.target;
        let (truthy, falsy) = if shape.guard_is_truthy_value {
            (HirDecisionTarget::CurrentValue, rest_target)
        } else {
            (rest_target, HirDecisionTarget::CurrentValue)
        };
        self.complete_node(node_ref, truthy, falsy);
        if !updates_binding {
            self.raw_guards.insert(shape.guard);
        }
        refs.merge(rest.refs);
        Some(CollapsedBranchValueTarget {
            target: HirDecisionTarget::Node(node_ref),
            refs,
        })
    }

    fn reserve_node(&mut self, test: &HirExpr) -> (HirDecisionNodeRef, BindingRefs) {
        let node_ref = HirDecisionNodeRef(self.nodes.len());
        self.nodes.push(HirDecisionNode {
            id: node_ref,
            test: test.clone(),
            truthy: HirDecisionTarget::CurrentValue,
            falsy: HirDecisionTarget::CurrentValue,
        });
        (node_ref, BindingRefs::in_expr(test))
    }

    fn complete_node(
        &mut self,
        node_ref: HirDecisionNodeRef,
        truthy: HirDecisionTarget,
        falsy: HirDecisionTarget,
    ) {
        let node = &mut self.nodes[node_ref.index()];
        node.truthy = normalize_current_value_target(&node.test, truthy, self.safety);
        node.falsy = normalize_current_value_target(&node.test, falsy, self.safety);
    }

    pub(super) fn finish(
        self,
        root: CollapsedBranchValueTarget,
    ) -> Option<(HirExpr, BTreeSet<TempId>)> {
        // 候选拒绝[SemanticBarrier:ValueFlow]：结果若仍读将删除的 raw guard（如 `g=v; if g then out=g+1`），会改读旧 g epoch 或未定义值。
        if self
            .raw_guards
            .iter()
            .any(|guard| root.refs.mentions(BranchValueBinding::Temp(*guard)))
        {
            return None;
        }
        let value = match root.target {
            HirDecisionTarget::Node(entry) => crate::hir::decision::finalize_value_decision_expr(
                HirDecisionExpr {
                    entry,
                    nodes: self.nodes,
                },
                self.safety,
            ),
            HirDecisionTarget::Expr(expr) => expr,
            HirDecisionTarget::CurrentValue => {
                unreachable!("branch-value root cannot borrow a parent test value")
            }
        };
        // 候选拒绝[TargetConstraint]：Lua `and/or` 不能承载一般三元值 DAG；这里若把
        // residual Decision 安装回 raw temp assignment，eliminate-decisions 物化后会与
        // 本 pass 来回振荡，因此保留原控制树由它直接表达互斥求值。
        (!matches!(value, HirExpr::Decision(_))).then_some((value, self.raw_guards))
    }
}

fn normalize_current_value_target(
    test: &HirExpr,
    target: HirDecisionTarget,
    safety: HirExprSafety,
) -> HirDecisionTarget {
    match target {
        // 候选拒绝[SemanticBarrier:EvalCount]：`if f() then out=f()` 原本调用两次，非 repeatable test 归一成 CurrentValue 会错误复用第一次结果；见 regress_241。
        HirDecisionTarget::Expr(expr) if expr == *test && safety.is_repeatable(test) => {
            HirDecisionTarget::CurrentValue
        }
        target => target,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decompile::DecompileDialect;
    use crate::hir::common::{HirAssign, HirLValue, HirValuePack};

    fn block(stmts: Vec<HirStmt>) -> HirBlock {
        HirBlock { stmts }
    }

    fn assign_temp(temp: TempId, value: HirExpr) -> HirStmt {
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(temp)],
            values: HirValuePack::fixed(vec![value]),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        }))
    }

    fn if_expr(cond: HirExpr, then_block: HirBlock, else_block: HirBlock) -> HirIf {
        HirIf {
            cond,
            then_block,
            else_block: Some(else_block),
        }
    }

    fn builder() -> BranchValueDecisionBuilder {
        BranchValueDecisionBuilder::new(HirExprSafety::for_dialect(DecompileDialect::Lua54))
    }

    #[test]
    fn output_leaf_reads_preserve_the_incoming_binding_epoch() {
        let output = TempId(0);
        let root = if_expr(
            HirExpr::TempRef(TempId(1)),
            block(vec![assign_temp(output, HirExpr::TempRef(output))]),
            block(vec![assign_temp(output, HirExpr::Integer(7))]),
        );
        let mut builder = builder();
        let collapsed = builder
            .collapse_if(&root, BranchValueBinding::Temp(output))
            .expect("terminal output reads still observe the candidate entry epoch");

        let (value, guards) = builder
            .finish(collapsed)
            .expect("entry-epoch reads can remain on the replacement assignment RHS");

        assert!(BranchValueBinding::Temp(output).mentions_expr(&value));
        assert!(guards.is_empty());
    }

    #[test]
    fn in_place_raw_guard_keeps_only_pre_write_output_reads() {
        let output = TempId(0);
        let in_place_guard = block(vec![
            assign_temp(output, HirExpr::TempRef(output)),
            HirStmt::If(Box::new(if_expr(
                HirExpr::TempRef(output),
                block(vec![assign_temp(output, HirExpr::TempRef(output))]),
                block(vec![assign_temp(output, HirExpr::Integer(7))]),
            ))),
        ]);
        let root = if_expr(
            HirExpr::TempRef(TempId(1)),
            in_place_guard,
            block(vec![assign_temp(output, HirExpr::Integer(9))]),
        );
        let mut builder = builder();
        let collapsed = builder
            .collapse_if(&root, BranchValueBinding::Temp(output))
            .expect("the producer RHS reads output before the in-place write");

        let (_, guards) = builder
            .finish(collapsed)
            .expect("an in-place guard can collapse without deleting its output binding");

        assert!(!guards.contains(&output));
    }

    #[test]
    fn in_place_raw_guard_rejects_post_write_output_reads() {
        let output = TempId(0);
        let in_place_guard = block(vec![
            assign_temp(output, HirExpr::Boolean(false)),
            HirStmt::If(Box::new(if_expr(
                HirExpr::TempRef(output),
                block(vec![assign_temp(output, HirExpr::TempRef(output))]),
                block(vec![assign_temp(output, HirExpr::TempRef(output))]),
            ))),
        ]);
        let root = if_expr(
            HirExpr::TempRef(TempId(1)),
            in_place_guard,
            block(vec![assign_temp(output, HirExpr::Integer(9))]),
        );
        let mut builder = builder();

        assert!(
            builder
                .collapse_if(&root, BranchValueBinding::Temp(output))
                .is_none(),
            "the continuation reads the epoch written by the guard producer"
        );
    }
}
