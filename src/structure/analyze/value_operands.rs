//! 将取值 DAG 内部单次消费的 phi 划为谓词操作数，并冻结控制节点的直接归属。
//! 内外表达式共享物理 CFG；后层不再沿 SSA 重新选择短路候选。

use super::*;
use crate::structure::plan::{ValueDecisionNodeId, ValueDecisionOperandPlan};

pub(super) fn select_operands(
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    graph: &GraphFacts,
    candidate: &ShortCircuitCandidate,
    by_phi: &BTreeMap<super::super::PhiId, &ShortCircuitCandidate>,
) -> Option<Vec<ValueDecisionOperandPlan>> {
    let nodes = candidate
        .nodes
        .iter()
        .map(|node| (node.header, node.id.index()))
        .collect::<BTreeMap<_, _>>();
    let mut operands = Vec::new();
    let mut events = Vec::new();
    for block in &candidate.blocks {
        for phi in dataflow.phi_candidates_in_block(*block) {
            if Some(phi.id) == candidate.result_phi_id || dataflow.phi_use_count(phi.id) == 0 {
                continue;
            }
            // 入边来自域外的 phi 是 RegionInput，仍由入口 prefix 提供。
            if phi.incoming.iter().any(|incoming| {
                incoming
                    .pred
                    .is_none_or(|pred| !candidate.blocks.contains(&pred))
            }) {
                continue;
            }
            let inner = *by_phi.get(&phi.id)?;
            let [use_site] = dataflow.phi_uses.get(phi.id.index())?.as_slice() else {
                return None;
            };
            let consumer_block = cfg.instr_to_block[use_site.instr.index()];
            let consumer = *nodes.get(&consumer_block)?;
            let continuation = *nodes.get(&phi.block)?;
            if inner.blocks.len() >= candidate.blocks.len()
                || !dataflow.phi_consumer_ids(phi.id).is_empty()
                || cfg.blocks[consumer_block.index()].instrs.last() != Some(use_site.instr)
                || !graph.post_dominates(consumer_block, phi.block)
                || dataflow.instr_effects[use_site.instr.index()].repeats_fixed_use(use_site.reg)
            {
                // 候选拒绝[ProofIncomplete:EvaluationCount]：只签发一个谓词直接读取一次的
                // 操作数；多个消费者或 phi 链仍需要显式绑定。
                return None;
            }
            let entry = *nodes.get(&inner.header)?;
            let index = operands.len();
            let leaves = phi
                .incoming
                .iter()
                .map(|incoming| Some((incoming.edge?, incoming.value)))
                .collect::<Option<BTreeMap<_, _>>>()?;
            operands.push(ValueDecisionOperandPlan {
                phi: phi.id,
                entry: ValueDecisionNodeId(entry),
                continuation: ValueDecisionNodeId(continuation),
                consumer: ValueDecisionNodeId(consumer),
                nodes: Vec::new(),
                leaves,
                current_values: BTreeSet::new(),
            });
            let depth = graph.dominator_tree.depth[inner.header.index()]?;
            // 严格支配子树减去 merge 子树恰是该闭合操作数的控制域。用区间事件划分
            // 直接 owner，每个外层节点只归属一次，不逐层复制或反复扫描嵌套 DAG。
            let start = graph.dominator_tree.preorder_index[inner.header.index()]?;
            let end = graph.dominator_tree.subtree_end[inner.header.index()]?;
            let merge_start = graph.dominator_tree.preorder_index[phi.block.index()]?;
            let merge_end = graph.dominator_tree.subtree_end[phi.block.index()]?;
            if !(start < merge_start && merge_end <= end) {
                return None;
            }
            for range in [start..merge_start, merge_end..end] {
                if !range.is_empty() {
                    events.push((range.start, true, depth, Reverse(inner.blocks.len()), index));
                    events.push((range.end, false, depth, Reverse(inner.blocks.len()), index));
                }
            }
        }
    }
    if operands.is_empty() {
        return Some(operands);
    }
    events.sort_unstable();
    let mut positions = candidate
        .nodes
        .iter()
        .map(|node| {
            Some((
                graph.dominator_tree.preorder_index[node.header.index()]?,
                node.id.index(),
            ))
        })
        .collect::<Option<Vec<_>>>()?;
    positions.sort_unstable();
    let mut active = BTreeSet::new();
    let mut cursor = 0;
    for (position, node) in positions {
        while let Some(&(at, entering, depth, size, operand)) = events.get(cursor) {
            if at > position {
                break;
            }
            if entering {
                active.insert((depth, size, operand));
            } else {
                active.remove(&(depth, size, operand));
            }
            cursor += 1;
        }
        if let Some(&(_, _, owner)) = active.last() {
            let source = by_phi.get(&operands[owner].phi)?;
            if !source.blocks.contains(&candidate.nodes[node].header) {
                return None;
            }
            operands[owner].nodes.push(ValueDecisionNodeId(node));
        }
    }
    let root = operands.len();
    let mut owners = vec![root; candidate.nodes.len()];
    for (index, operand) in operands.iter().enumerate() {
        if operand.nodes.is_empty() || operand.nodes.contains(&operand.consumer) {
            return None;
        }
        for node in &operand.nodes {
            owners[node.index()] = index;
        }
    }
    let mut children = vec![Vec::new(); root + 1];
    for (index, operand) in operands.iter().enumerate() {
        children[owners[operand.consumer.index()]].push(index);
    }
    let mut visited = vec![false; root + 1];
    let mut pending = vec![(root, false)];
    while let Some((parent, exiting)) = pending.pop() {
        if !exiting {
            if std::mem::replace(&mut visited[parent], true) {
                return None;
            }
            pending.push((parent, true));
            pending.extend(children[parent].iter().map(|child| (*child, false)));
            continue;
        }
        if parent == root {
            continue;
        }
        // 比较自身的控制头可能晚于其操作数准备；例如先算 a、b，再以 a==b
        // 选择 7/8。组合表达式从最早的子操作数开始，不能把此前两份准备留在父域。
        let mut entry = operands[parent].entry;
        for &child in &children[parent] {
            let child_entry = operands[child].entry;
            let child_block = candidate.nodes[child_entry.index()].header;
            let entry_block = candidate.nodes[entry.index()].header;
            if graph.dominates(child_block, entry_block) {
                entry = child_entry;
            } else if !graph.dominates(entry_block, child_block) {
                return None;
            }
        }
        operands[parent].entry = entry;
    }
    if visited.iter().any(|visited| !visited) {
        return None;
    }
    operands.sort_unstable_by_key(|operand| operand.phi);
    Some(operands)
}
