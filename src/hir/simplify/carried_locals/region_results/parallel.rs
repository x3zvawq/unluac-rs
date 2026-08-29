//! 合并相邻的初始化 local 声明；依赖 binding mention 查询，不负责推导 rewrite。

use super::*;

pub(super) fn merge_initialized_local_declarations(
    block: &mut HirBlock,
    start: usize,
    count: usize,
) -> bool {
    if count < 2 {
        return false;
    }
    // 候选拒绝[ConvergenceGuard]：越界表示 caller 提供的 declaration group 与当前 block 漂移，不是语义候选缺少证明。
    if start + count > block.stmts.len() {
        return false;
    }
    let mut bindings = Vec::with_capacity(count);
    let mut values = Vec::with_capacity(count);
    for stmt in &block.stmts[start..start + count] {
        let Some((binding, value)) = initialized_local(stmt) else {
            return false;
        };
        let earlier = bindings
            .iter()
            .copied()
            .map(CarryBinding::Local)
            .collect::<Vec<_>>();
        if bindings_are_mentioned_in_exprs(std::iter::once(value), &earlier) {
            // 候选拒绝[SemanticBarrier:Scope]：顺序 `local a=v; local b=a` 合成并行声明后，b 的 RHS 会解析到外层 a。
            return false;
        }
        bindings.push(binding);
        values.push(value.clone());
    }
    block.stmts[start] = HirStmt::LocalDecl(Box::new(HirLocalDecl {
        bindings,
        values: HirValuePack::fixed(values),
    }));
    block.stmts.drain(start + 1..start + count);
    true
}
