//! Structure 与 HIR 共用的非递归图遍历算法。
//!
//! 调用方提供当前快照的稠密身份、可见域及邻接关系；这里不解释控制语句或跨层复用
//! 旧拓扑。Structure 保存支配分析所需的 DFS 顺序，HIR 在改写后重新分析其实际控制边。
//! 例如 `entry -> a -> b -> a` 产生源 SCC `{entry}` 与循环 SCC `{a,b}`，不可达前驱
//! 不会混入分量。分量按源到汇顺序签发，身份只在调用方提供的图快照内有效。

pub(crate) struct DfsTraversal<N> {
    pub(crate) preorder: Vec<N>,
    pub(crate) parent: Vec<Option<N>>,
    pub(crate) postorder: Vec<N>,
}

pub(crate) fn depth_first<N: Copy, I: IntoIterator<Item = N>>(
    node_count: usize,
    root: N,
    index: impl Fn(N) -> usize,
    visible: impl Fn(N) -> bool,
    successors: impl Fn(N) -> I,
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
