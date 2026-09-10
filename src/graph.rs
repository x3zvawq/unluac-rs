//! Structure、HIR 与 AST 共用的非递归图算法和词法引用索引。
//!
//! 调用方提供当前快照的稠密身份、可见域及邻接关系；这里不解释控制语句或跨层复用
//! 旧拓扑。Structure 保存支配分析所需的 DFS 顺序，HIR 在改写后重新分析其实际控制边。
//! 例如 `entry -> a -> b -> a` 产生源 SCC `{entry}` 与循环 SCC `{a,b}`，不可达前驱
//! 不会混入分量。分量按源到汇顺序签发，身份只在调用方提供的图快照内有效。
//! label_refs 独立处理词法引用范围，不借执行图的可达性删除语法入边。

mod dominance;
mod label_refs;
mod positions;

pub(crate) use dominance::{DominatorTree, dominator_tree};
pub(crate) use label_refs::{LabelReferenceIndex, LabelReferences};
pub(crate) use positions::PositionIndex;

pub(crate) struct DfsTraversal<N> {
    pub(crate) preorder: Vec<N>,
    pub(crate) parent: Vec<Option<N>>,
    pub(crate) postorder: Vec<N>,
}

/// 每个可达可见节点仅在首次访问时请求相邻项，调用方可同时发布该节点的快照事实。
/// 相邻项可拥有其存储；重复边保留原顺序，但不导致重复构造节点。
pub(crate) fn depth_first<N: Copy, I: IntoIterator<Item = N>>(
    node_count: usize,
    root: N,
    index: impl Fn(N) -> usize,
    visible: impl Fn(N) -> bool,
    mut successors: impl FnMut(N) -> I,
) -> DfsTraversal<N> {
    let mut traversal = DfsTraversal {
        preorder: Vec::with_capacity(node_count),
        parent: vec![None; node_count],
        postorder: Vec::with_capacity(node_count),
    };
    if !visible(root) {
        return traversal;
    }
    let mut visited = vec![false; node_count];
    visited[index(root)] = true;
    traversal.preorder.push(root);
    let mut stack = vec![(root, successors(root).into_iter())];
    while let Some((node, edges)) = stack.last_mut() {
        let from = *node;
        if let Some(next) = edges.next() {
            if visible(next) && !visited[index(next)] {
                visited[index(next)] = true;
                traversal.parent[index(next)] = Some(from);
                traversal.preorder.push(next);
                stack.push((next, successors(next).into_iter()));
            }
        } else {
            traversal.postorder.push(from);
            stack.pop();
        }
    }
    traversal
}

/// 消费同一图的 DFS 后序与反向边；后序同时限定入口可达域。
/// 分量按源到汇签发，跨分量边的 source 编号严格小于 target，可直接用于正反向传播。
pub(crate) fn strongly_connected_components<N: Copy, I: IntoIterator<Item = N>>(
    node_count: usize,
    postorder: &[N],
    index: impl Fn(N) -> usize,
    predecessors: impl Fn(N) -> I,
) -> Vec<Vec<N>> {
    let mut unassigned = vec![false; node_count];
    for &node in postorder {
        unassigned[index(node)] = true;
    }
    let mut components = Vec::new();
    let mut pending = Vec::new();
    for &root in postorder.iter().rev() {
        if !std::mem::replace(&mut unassigned[index(root)], false) {
            continue;
        }
        let mut component = Vec::new();
        pending.push(root);
        while let Some(node) = pending.pop() {
            component.push(node);
            for pred in predecessors(node) {
                if std::mem::replace(&mut unassigned[index(pred)], false) {
                    pending.push(pred);
                }
            }
        }
        components.push(component);
    }
    components
}
