//! Analysis 内部通用图算法：迭代 DFS、强连通分量（Kosaraju）与 Lengauer-Tarjan 支配树。
//!
//! 消费调用方提供的图快照，不解释领域控制语义，所有核心遍历均采用显式栈避免爆栈。

pub(crate) struct DfsTraversal<N> {
    pub(crate) preorder: Vec<N>,
    pub(crate) parent: Vec<Option<N>>,
    pub(crate) postorder: Vec<N>,
}

/// 每个可达可见节点仅在首次访问时请求相邻项；重复边保留原顺序，但不重复构造节点。
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

pub(crate) struct DominatorTree<N> {
    pub(crate) parent: Vec<Option<N>>,
    pub(crate) children: Vec<Vec<N>>,
    pub(crate) order: Vec<N>,
    pub(crate) preorder_index: Vec<Option<usize>>,
    pub(crate) subtree_end: Vec<Option<usize>>,
}

impl<N> DominatorTree<N> {
    pub(crate) fn dominates(&self, dom: N, node: N, index: impl Fn(N) -> usize) -> bool {
        let dom = index(dom);
        let (Some(start), Some(end), Some(node_start)) = (
            self.preorder_index[dom],
            self.subtree_end[dom],
            self.preorder_index[index(node)],
        ) else {
            return false;
        };
        start <= node_start && node_start < end
    }
}

pub(crate) fn dominator_tree<N: Copy + Eq + std::fmt::Display, I: IntoIterator<Item = N>>(
    traversal: &DfsTraversal<N>,
    index: impl Fn(N) -> usize,
    node_at: impl Fn(usize) -> N,
    predecessors: impl Fn(N) -> I,
) -> Result<DominatorTree<N>, String> {
    let node_count = traversal.parent.len();
    let mut tree = DominatorTree {
        parent: vec![None; node_count],
        children: vec![Vec::new(); node_count],
        order: Vec::with_capacity(traversal.preorder.len()),
        preorder_index: vec![None; node_count],
        subtree_end: vec![None; node_count],
    };
    let Some(root) = traversal.preorder.first().copied() else {
        return Ok(tree);
    };
    if traversal.preorder.len() == 1 {
        tree.order.push(root);
        tree.preorder_index[index(root)] = Some(0);
        tree.subtree_end[index(root)] = Some(1);
        return Ok(tree);
    }
    let mut semi = vec![usize::MAX; node_count];
    let mut label = (0..node_count).map(&node_at).collect::<Vec<_>>();
    for (number, node) in traversal.preorder.iter().copied().enumerate() {
        semi[index(node)] = number;
    }
    let mut ancestor = vec![None; node_count];
    let idom = &mut tree.parent;
    idom[index(root)] = Some(root);
    let mut buckets = vec![Vec::new(); node_count];
    let mut eval_path = Vec::with_capacity(node_count);
    for node in traversal.preorder.iter().copied().skip(1).rev() {
        for predecessor in predecessors(node) {
            if semi[index(predecessor)] == usize::MAX {
                continue;
            }
            let representative = eval(
                predecessor,
                &mut ancestor,
                &mut label,
                &semi,
                &mut eval_path,
                &index,
            )?;
            semi[index(node)] = semi[index(node)].min(semi[index(representative)]);
        }
        let semi_dominator = traversal.preorder[semi[index(node)]];
        buckets[index(semi_dominator)].push(node);
        let parent = traversal.parent[index(node)]
            .ok_or_else(|| format!("non-root DFS node {node} has no traversal parent"))?;
        ancestor[index(node)] = Some(parent);
        while let Some(bucket_node) = buckets[index(parent)].pop() {
            let representative = eval(
                bucket_node,
                &mut ancestor,
                &mut label,
                &semi,
                &mut eval_path,
                &index,
            )?;
            idom[index(bucket_node)] =
                Some(if semi[index(representative)] < semi[index(bucket_node)] {
                    representative
                } else {
                    parent
                });
        }
    }
    for node in traversal.preorder.iter().copied().skip(1) {
        let semi_dominator = traversal.preorder[semi[index(node)]];
        if idom[index(node)] != Some(semi_dominator) {
            let provisional = idom[index(node)].ok_or_else(|| {
                format!("reachable non-root node {node} has no provisional dominator")
            })?;
            idom[index(node)] = Some(idom[index(provisional)].ok_or_else(|| {
                format!("provisional dominator {provisional} for {node} is unresolved")
            })?);
        }
    }
    // root 自指只服务于构建期修正；发布的支配树根节点没有父节点。
    idom[index(root)] = None;
    for (node_index, maybe_idom) in idom.iter().copied().enumerate() {
        if let Some(parent) = maybe_idom {
            tree.children[index(parent)].push(node_at(node_index));
        }
    }
    let mut pending = vec![root];
    while let Some(node) = pending.pop() {
        tree.preorder_index[index(node)] = Some(tree.order.len());
        tree.order.push(node);
        tree.subtree_end[index(node)] = Some(tree.order.len());
        pending.extend(tree.children[index(node)].iter().rev().copied());
    }
    for node in tree.order.iter().copied().rev() {
        if let Some(parent) = tree.parent[index(node)] {
            tree.subtree_end[index(parent)] =
                tree.subtree_end[index(parent)].max(tree.subtree_end[index(node)]);
        }
    }
    Ok(tree)
}

fn eval<N: Copy + std::fmt::Display>(
    node: N,
    ancestor: &mut [Option<N>],
    label: &mut [N],
    semi: &[usize],
    path: &mut Vec<N>,
    index: &impl Fn(N) -> usize,
) -> Result<N, String> {
    // 显式路径先压缩父节点再比较 label，避免把 CFG 深度转成调用栈深度。
    path.clear();
    let mut current = node;
    while let Some(parent) = ancestor[index(current)] {
        if ancestor[index(parent)].is_none() {
            break;
        }
        path.push(current);
        current = parent;
    }
    for current in path.iter().copied().rev() {
        let parent = ancestor[index(current)]
            .ok_or_else(|| format!("compressed dominator path for {current} lost its parent"))?;
        let parent_label = label[index(parent)];
        if semi[index(parent_label)] < semi[index(label[index(current)])] {
            label[index(current)] = parent_label;
        }
        ancestor[index(current)] = ancestor[index(parent)];
    }
    Ok(label[index(node)])
}
