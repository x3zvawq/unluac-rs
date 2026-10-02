//! 恢复单一落入路径末端的 repeat 条件准备帧。
//! 保留提前 break 与词法作用域，复用普通帧证明及整批前缀事务。

use super::*;
use crate::hir::simplify::lexical_cfg::stmt_has_current_owner_continue;

fn preparation_tail(mut block: &HirBlock) -> Option<&[HirStmt]> {
    let mut crossed_branch = false;
    loop {
        if block
            .stmts
            .iter()
            .any(|stmt| matches!(stmt, HirStmt::Close(_) | HirStmt::ToBeClosed(_)))
        {
            // 候选拒绝[SemanticBarrier:Lifetime]：条件不能越过离开分支作用域时的清理。
            return None;
        }
        match block.stmts.last()? {
            HirStmt::If(branch)
                if matches!(branch.then_block.stmts.as_slice(), [HirStmt::Break]) =>
            {
                block = branch.else_block.as_ref()?;
                crossed_branch = true;
            }
            HirStmt::Block(nested) => block = nested,
            _ => break,
        }
    }
    if !crossed_branch {
        return None;
    }
    let start = block
        .stmts
        .iter()
        .rposition(|stmt| scalar_binding(stmt).is_none())
        .map_or(0, |index| index + 1);
    let tail = &block.stmts[start..];
    (!tail.is_empty()).then_some(tail)
}

pub(super) fn collect(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    count: usize,
) -> Vec<Plan> {
    let mut forbidden = false;
    let ends = prefix::coordinates::owner_ends(&context.proto.body, count);
    let mut scopes = vec![None; context.proto.local_count];
    prefix::coordinates::visit_scoped(
        &context.proto.body,
        &mut 0,
        &mut |index, owner, kind, stmt| {
            if kind != PointKind::Statement {
                return;
            }
            match stmt {
                HirStmt::Goto(_) | HirStmt::Label(_) => forbidden = true,
                HirStmt::LocalDecl(decl) => {
                    for local in &decl.bindings {
                        scopes[local.index()] = Some((index, ends[owner]));
                    }
                }
                HirStmt::NumericFor(loop_) => {
                    scopes[loop_.binding.index()] = ends.get(index + 1).map(|&end| (index, end))
                }
                HirStmt::GenericFor(loop_) => {
                    for local in &loop_.bindings {
                        scopes[local.index()] = ends.get(index + 1).map(|&end| (index, end));
                    }
                }
                _ => {}
            }
        },
    );
    if forbidden {
        // 候选拒绝[ProofIncomplete:ControlFlow]：非局部跳转可能绕过尾准备或进入其中。
        return Vec::new();
    }
    let mut plans = Vec::new();
    prefix::coordinates::visit(&context.proto.body, &mut 0, &mut |sink, kind, stmt| {
        let (PointKind::RepeatCondition, HirStmt::Repeat(repeat)) = (kind, stmt) else {
            return;
        };
        let Some(tail) = preparation_tail(&repeat.body) else {
            return;
        };
        if repeat
            .body
            .stmts
            .iter()
            .any(stmt_has_current_owner_continue)
        {
            // 候选拒绝[SemanticBarrier:ControlFlow]：continue 可以读取上一轮参数，不能当成本轮准备。
            return;
        }
        let run = tail.iter().collect::<Vec<_>>();
        let Some(mut plan) = condition_plan(context, &run, facts, dialect, &repeat.cond) else {
            return;
        };
        let mut escaped = false;
        crate::hir::visit::visit_expr(
            &plan.values.fixed[0],
            &mut BindingReadCollector(|binding| {
                if let HirBinding::Local(local) = binding {
                    escaped |= scopes[local.index()]
                        .is_none_or(|(start, end)| !(start <= sink && sink < end));
                }
            }),
        );
        if escaped {
            // 候选拒绝[SemanticBarrier:Scope]：尾调用不能把分支内部 local 的读取带出声明域。
            return;
        }
        // 每层另一臂直接退出本 repeat，且 else 是 DFS 最后一臂；准备区与条件坐标相邻。
        // 只退休完整帧认领的后缀，不移动分支、声明或其它效果。外层仍统一验证回边与根前缀。
        plan.start += sink - run.len();
        plan.sink = sink;
        plan.removed = (plan.start..sink).collect();
        plans.push(plan);
    });
    plans
}
