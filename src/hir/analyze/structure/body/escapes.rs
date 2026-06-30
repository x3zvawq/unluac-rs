//! 这个文件承载 structured body lowering 中的 active-loop escape 降低。
//!
//! region walker 遇到当前 active loop 的 continue target、post-loop、break pad 或跨层
//! escape edge 时，需要把这些 CFG 边翻成 `continue` / `break` / `goto`，并在必要时
//! 快照 loop state。本文件只消费已经构建好的 `ActiveLoopContext`、entry override 与
//! dataflow live-in 信息；它不重新判断 loop/branch 候选，也不替 StructureFacts 补事实。
//!
//! 输入形状：loop body 内一条边跳到外层 block。
//! 输出形状：必要的 state assignment 加目标 label `goto`。

use super::*;

impl StructuredBodyLowerer<'_, '_> {
    pub(super) fn active_loop_escape_stmts(&mut self, block: BlockRef) -> Option<Vec<HirStmt>> {
        let loop_context = self.active_loops.last()?.clone();
        if loop_context.continue_target == Some(block) && self.loop_continue_target_is_empty(block)
        {
            return self
                .can_emit_continue_stmt()
                .then(|| vec![HirStmt::Continue]);
        }
        if block == loop_context.post_loop || Some(block) == loop_context.downstream_post_loop {
            return Some(vec![HirStmt::Break]);
        }
        if let Some(break_block) = loop_context.break_exits.get(&block) {
            self.visited.extend(break_block.blocks.iter().copied());
            return Some(break_block.block.stmts.clone());
        }
        None
    }

    pub(super) fn lower_escape_edge(
        &mut self,
        from: BlockRef,
        to: BlockRef,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Option<HirBlock> {
        if to == self.lowering.cfg.exit_block || !self.lowering.cfg.reachable_blocks.contains(&to) {
            return None;
        }
        self.required_labels.insert(to);
        let mut stmts = self.escape_state_snapshot_stmts(from, to, target_overrides);
        stmts.extend(goto_block(self.label_map[&to]).stmts);
        Some(HirBlock { stmts })
    }

    fn escape_state_snapshot_stmts(
        &self,
        from: BlockRef,
        to: BlockRef,
        target_overrides: &BTreeMap<TempId, HirLValue>,
    ) -> Vec<HirStmt> {
        let live_in = self.lowering.dataflow.live_in_regs(to);
        let expr_overrides = temp_expr_overrides(target_overrides);
        let mut seen_regs = BTreeSet::new();
        let mut targets = Vec::new();
        let mut values = Vec::new();

        for loop_context in &self.active_loops {
            if loop_context.loop_blocks.contains(&to) {
                continue;
            }

            for state in &loop_context.state_slots {
                if !live_in.contains(&state.reg) || !seen_regs.insert(state.reg) {
                    continue;
                }
                let Some(target) = self.escape_state_target(to, state.reg) else {
                    continue;
                };
                let mut value = expr_for_reg_at_block_exit(self.lowering, from, state.reg);
                rewrite_expr_temps(&mut value, &expr_overrides);
                if lvalue_as_expr(&target)
                    .as_ref()
                    .is_some_and(|target_expr| *target_expr == value)
                {
                    continue;
                }
                targets.push(target);
                values.push(value);
            }
        }

        if targets.is_empty() {
            Vec::new()
        } else {
            vec![assign_stmt(targets, values)]
        }
    }

    fn escape_state_target(&self, to: BlockRef, reg: Reg) -> Option<HirLValue> {
        if let Some(target) = self
            .overrides
            .block_entry_expr(to, reg)
            .and_then(expr_as_lvalue)
        {
            return Some(target);
        }

        self.active_loops
            .iter()
            .filter(|loop_context| !loop_context.loop_blocks.contains(&to))
            .flat_map(|loop_context| loop_context.state_slots.iter())
            .find(|state| state.reg == reg)
            .map(|state| state.target.clone())
    }
}
