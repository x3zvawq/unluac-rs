//! 这个文件承载 block prefix temp 的表达式恢复辅助。
//!
//! loop header、short-circuit consumed header 等路径都会先把 block terminator 前的
//! prefix 指令作为 single-eval 事实消费。这里统一提供“哪些 prefix temp 可以内联成
//! 表达式、哪些 temp 只是被定义但不可安全内联”的查询，不归属于 loop state 或
//! short-circuit 某一个具体策略。
//!
//! 输入形状：block prefix 中若干 fixed def。
//! 输出形状：可内联 temp 的表达式 override，以及所有 prefix temp / 定义顺序集合。

use super::*;

impl StructuredBodyLowerer<'_, '_> {
    /// 返回 (expr_overrides, all_prefix_temps)，其中：
    /// - `expr_overrides`：前缀指令能成功内联的 temp → 表达式映射
    /// - `all_prefix_temps`：前缀指令定义的所有 temp 集合
    ///
    /// 调用方可通过 `all_prefix_temps - expr_overrides.keys()` 得到"无法内联的前缀 temp"。
    pub(crate) fn block_prefix_temp_expr_overrides(
        &self,
        block: BlockRef,
    ) -> (BTreeMap<TempId, HirExpr>, BTreeSet<TempId>) {
        let Some(prefix_indices) = self.block_prefix_instr_indices(block, false) else {
            return (BTreeMap::new(), BTreeSet::new());
        };

        let mut expr_overrides = BTreeMap::new();
        let mut all_prefix_temps = BTreeSet::new();
        for instr_index in prefix_indices {
            let instr_ref = InstrRef(instr_index);
            if self.overrides.instr_is_suppressed(instr_ref) {
                continue;
            }
            for def in &self.lowering.dataflow.instr_defs[instr_index] {
                let temp = self.lowering.bindings.fixed_temps[def.index()];
                all_prefix_temps.insert(temp);
                let Some(mut expr) = expr_for_fixed_def(self.lowering, *def) else {
                    continue;
                };
                rewrite_expr_temps(&mut expr, &expr_overrides);
                expr_overrides.insert(temp, expr);
            }
        }

        (expr_overrides, all_prefix_temps)
    }

    pub(crate) fn block_prefix_temp_def_order(&self, block: BlockRef) -> BTreeMap<TempId, usize> {
        let Some(prefix_indices) = self.block_prefix_instr_indices(block, false) else {
            return BTreeMap::new();
        };

        let mut def_order = BTreeMap::new();
        for instr_index in prefix_indices {
            for def in &self.lowering.dataflow.instr_defs[instr_index] {
                let temp = self.lowering.bindings.fixed_temps[def.index()];
                def_order.insert(temp, instr_index);
            }
        }
        def_order
    }
}
