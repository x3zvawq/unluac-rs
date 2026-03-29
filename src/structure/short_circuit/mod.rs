//! 这个文件实现短路候选提取。
//!
//! 当前实现分两部分：
//! 1. 条件出口型短路继续沿用保守的线性识别，优先保证 `if a and b then ...` 这类
//!    条件链稳定可用；
//! 2. 值合流型短路改成受控 DAG 提取，允许普通 Lua 源码里常见的共享 continuation，
//!    例如 `(a and b) or (c and d)`。
//!
//! 这样做的原因是：值型短路的 CFG 更容易出现“多个失败路径汇到同一后续表达式”的
//! 共享形状，如果继续强行压成线性链，HIR 只能看到残缺证据，后面就会被迫回退。
//! 这里还额外坚持一个边界约束：既然我们产出的是 DAG，就必须在结构层保证“无环”。
//! 像 loop header 里那种会回指前一个判断节点的图形，应该留给 loop/branch 恢复处理，
//! 不能伪装成短路 DAG 再把有环图塞给后层。
//!
//! 它依赖 branch 骨架、Dataflow phi 和 CFG 图查询已经到位，只负责产出短路候选及其
//! 必须保留的约束；它不会越权决定最终是 `if`、逻辑表达式还是赋值语句，那一步仍在 HIR。
//!
//! 例子：
//! - `if a and b then ... end` 会走 branch-exit 候选提取
//! - `local x = a and b or c` 会走 value-merge 候选提取
//! - 带回边的 loop 条件链不会在这里伪装成短路 DAG，而会留给 loop/branch 恢复

mod branch_exit;
mod shared;
mod value_merge;

use std::collections::BTreeMap;

use crate::cfg::{BlockRef, Cfg, DataflowFacts, GraphFacts};
use crate::transformer::{LoweredProto, Reg};

use super::common::{BranchCandidate, ShortCircuitCandidate};

pub(super) fn analyze_short_circuits(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    branch_candidates: &[BranchCandidate],
) -> Vec<ShortCircuitCandidate> {
    let branch_by_header = branch_candidates
        .iter()
        .map(|candidate| (candidate.header, candidate))
        .collect::<BTreeMap<BlockRef, _>>();

    let mut candidates = branch_exit::analyze_linear_branch_exit_candidates(
        proto,
        cfg,
        &branch_by_header,
        branch_candidates,
    );
    candidates.extend(branch_exit::analyze_guard_branch_exit_dag_candidates(
        proto,
        cfg,
        graph_facts,
        &branch_by_header,
        branch_candidates,
    ));
    candidates.extend(value_merge::analyze_value_merge_candidates(
        proto,
        cfg,
        graph_facts,
        dataflow,
        &branch_by_header,
        branch_candidates,
    ));
    candidates.sort_by_key(|candidate| {
        (
            candidate.header,
            candidate.blocks.len(),
            candidate.nodes.len(),
            candidate.result_reg.map(Reg::index),
        )
    });
    candidates
}
