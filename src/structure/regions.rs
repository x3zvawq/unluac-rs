//! 从不可规约 SCC 提取区域成员与出入边事实。
//!
//! 向最终结构计划发布 RegionFact，可规约的 loop/branch 仍由各自 owner 表达。

use crate::structure::{BlockRef, Cfg};

use super::common::{IrreducibleRegion, RegionFact};
use super::helpers::collect_region_exits;

pub(super) fn analyze_regions(
    cfg: &Cfg,
    irreducible_regions: &[IrreducibleRegion],
) -> Vec<RegionFact> {
    if irreducible_regions.is_empty() {
        return Vec::new();
    }
    // 每个连接块只索引一次前驱；多个出口指向同一 join 时不反复扫描其入边。
    let private_jump_predecessors = cfg
        .blocks
        .iter()
        .enumerate()
        .map(|(index, _)| {
            let block = BlockRef(index);
            super::branches::transparent_jump_target(cfg, block)?;
            cfg.unique_reachable_predecessor_matching(block, |_| true)
        })
        .collect::<Vec<_>>();
    let mut regions = irreducible_regions
        .iter()
        .map(|irreducible| {
            let mut blocks = irreducible.blocks.clone();
            let mut pending = blocks.iter().copied().collect::<Vec<_>>();
            while let Some(from) = pending.pop() {
                for edge in &cfg.succs[from.index()] {
                    let target = cfg.edges[edge.index()].to;
                    // 独占 JMP 是原出口的连接点，没有新的入口或求值。将其归入同一
                    // island 后，内部 branch 不会因编译器拆出的出口 pad 跨越容器边界。
                    // 共享 join 与带清理/计算的块仍由原外部 owner 持有。
                    if private_jump_predecessors[target.index()] == Some(from)
                        && blocks.insert(target)
                    {
                        pending.push(target);
                    }
                }
            }
            RegionFact {
                entry: irreducible.entry,
                exits: collect_region_exits(cfg, &blocks),
                blocks,
            }
        })
        .collect::<Vec<_>>();

    regions.sort_by_key(|region| region.entry);
    regions
}
