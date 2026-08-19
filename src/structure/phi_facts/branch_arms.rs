//! 将 branch phi incoming 汇入 then/else arm 的值集合；依赖支配与数据流，不负责 branch 候选选择；例如区分 entry value 与 arm 内更新值。

use super::*;

pub(super) fn extend_branch_value_arm(
    header: BlockRef,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    entry_value: SsaValue,
    arm: &mut BranchValueMergeArm,
    incoming: &crate::structure::PhiIncoming,
) {
    let Some(pred) = incoming.pred else {
        return;
    };
    arm.preds.insert(pred);
    arm.values.insert(incoming.value);
    let carries_entry = dataflow.value_contains(incoming.value, entry_value);
    // 非循环 header 的当前入口值不可能包含一个由 header 严格支配的定义；若能从
    // header 之后重新流回入口，就已经构成 backedge。顺序 branch 的 preserved arm
    // 因而无需反复展开随前序分支增长的整条 Phi 链。
    let needs_dominated_update_check = carries_entry
        && (incoming.value != entry_value || graph_facts.loop_headers.contains(&header));
    let is_dominated_update = needs_dominated_update_check
        && dataflow.leaf_defs(incoming.value).iter().any(|def| {
            let block = dataflow.def_block(*def);
            block != header && graph_facts.dominator_tree.dominates(header, block)
        });
    if carries_entry {
        arm.entry_values.insert(incoming.value);
    }
    if !carries_entry || is_dominated_update {
        arm.update_values.insert(incoming.value);
    }
}
