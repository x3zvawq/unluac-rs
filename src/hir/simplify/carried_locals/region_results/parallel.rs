//! 合并相邻的初始化 local 声明；依赖 binding mention 查询，不负责推导 rewrite。

use super::*;

pub(super) fn merge_initialized_local_declarations(
    block: &mut HirBlock,
    start: usize,
    count: usize,
) -> bool {
    if count < 2 || start + count > block.stmts.len() {
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
