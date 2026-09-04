//! 合并相邻的初始化 local 声明；消费共享 local 形状与读取事实，不推导 binding 身份。
//! 先验证 RHS 不读取前面的新绑定，再移动原有值节点提交；例如 `local a=v; local b=a`
//! 必须保留顺序声明，而彼此独立的 RHS 可以保持求值顺序合成并行声明。

use super::super::reads::BindingReadCollector;
use super::*;

pub(super) fn merge_initialized_local_declarations(
    block: &mut HirBlock,
    start: usize,
    count: usize,
) -> bool {
    if count < 2 {
        return false;
    }
    assert!(
        start + count <= block.stmts.len(),
        "planned declaration merge must remain within the current block"
    );
    let mut bindings = Vec::with_capacity(count);
    let mut earlier = BTreeSet::new();
    for stmt in &block.stmts[start..start + count] {
        let (binding, value) = initialized_single_local_decl(stmt)
            .expect("planned declaration merge must retain initialized local statements");
        if !earlier.is_empty() {
            let mut reads = BindingReadCollector::default();
            reads.collect_expr(value);
            if reads.reads.iter().any(|binding| earlier.contains(binding)) {
                // 候选拒绝[SemanticBarrier:Scope]：顺序 `local a=v; local b=a` 合成并行声明后，b 的 RHS 会解析到外层 a。
                return false;
            }
        }
        earlier.insert(CarryBinding::Local(binding));
        bindings.push(binding);
    }
    let mut values = Vec::with_capacity(count);
    for stmt in &mut block.stmts[start..start + count] {
        let HirStmt::LocalDecl(decl) = stmt else {
            unreachable!("validated declaration merge must retain local statements");
        };
        values.append(&mut decl.values.fixed);
    }
    block.stmts[start] = HirStmt::LocalDecl(Box::new(HirLocalDecl {
        bindings,
        values: HirValuePack::fixed(values),
        initializer_merge_transaction: None,
    }));
    block.stmts.drain(start + 1..start + count);
    true
}
