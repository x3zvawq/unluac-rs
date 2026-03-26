//! 这个文件承载 `short_circuit` 模块的局部不变量测试。
//!
//! 我们把测试和实现分开存放，避免主实现文件被大段 `#[cfg(test)]` 代码淹没。

use super::*;
use crate::structure::{
    ShortCircuitCandidate, ShortCircuitExit, ShortCircuitNode, ShortCircuitTarget,
};

#[test]
fn conditional_reassign_picks_shallowest_changed_only_region() {
    let short = ShortCircuitCandidate {
        header: BlockRef(12),
        blocks: BTreeSet::from([
            BlockRef(12),
            BlockRef(13),
            BlockRef(14),
            BlockRef(15),
            BlockRef(16),
            BlockRef(17),
            BlockRef(18),
            BlockRef(19),
            BlockRef(20),
            BlockRef(21),
            BlockRef(22),
        ]),
        entry: ShortCircuitNodeRef(0),
        nodes: vec![
            ShortCircuitNode {
                id: ShortCircuitNodeRef(0),
                header: BlockRef(12),
                truthy: ShortCircuitTarget::Node(ShortCircuitNodeRef(1)),
                falsy: ShortCircuitTarget::Node(ShortCircuitNodeRef(6)),
            },
            ShortCircuitNode {
                id: ShortCircuitNodeRef(1),
                header: BlockRef(13),
                truthy: ShortCircuitTarget::Node(ShortCircuitNodeRef(2)),
                falsy: ShortCircuitTarget::Node(ShortCircuitNodeRef(6)),
            },
            ShortCircuitNode {
                id: ShortCircuitNodeRef(2),
                header: BlockRef(16),
                truthy: ShortCircuitTarget::Node(ShortCircuitNodeRef(3)),
                falsy: ShortCircuitTarget::Node(ShortCircuitNodeRef(4)),
            },
            ShortCircuitNode {
                id: ShortCircuitNodeRef(3),
                header: BlockRef(17),
                truthy: ShortCircuitTarget::Value(BlockRef(18)),
                falsy: ShortCircuitTarget::Node(ShortCircuitNodeRef(4)),
            },
            ShortCircuitNode {
                id: ShortCircuitNodeRef(4),
                header: BlockRef(19),
                truthy: ShortCircuitTarget::Node(ShortCircuitNodeRef(5)),
                falsy: ShortCircuitTarget::Value(BlockRef(22)),
            },
            ShortCircuitNode {
                id: ShortCircuitNodeRef(5),
                header: BlockRef(20),
                truthy: ShortCircuitTarget::Value(BlockRef(21)),
                falsy: ShortCircuitTarget::Value(BlockRef(22)),
            },
            ShortCircuitNode {
                id: ShortCircuitNodeRef(6),
                header: BlockRef(14),
                truthy: ShortCircuitTarget::Value(BlockRef(14)),
                falsy: ShortCircuitTarget::Node(ShortCircuitNodeRef(7)),
            },
            ShortCircuitNode {
                id: ShortCircuitNodeRef(7),
                header: BlockRef(15),
                truthy: ShortCircuitTarget::Node(ShortCircuitNodeRef(2)),
                falsy: ShortCircuitTarget::Value(BlockRef(15)),
            },
        ],
        exit: ShortCircuitExit::ValueMerge(BlockRef(23)),
        result_reg: None,
        reducible: true,
    };
    let leaf_kinds = BTreeMap::from([
        (BlockRef(14), ValueLeafKind::Preserved),
        (BlockRef(15), ValueLeafKind::Preserved),
        (BlockRef(18), ValueLeafKind::Changed),
        (BlockRef(21), ValueLeafKind::Changed),
        (BlockRef(22), ValueLeafKind::Changed),
    ]);

    let region = find_changed_region_entry(&short, &leaf_kinds);

    assert_eq!(
        region,
        Some(ChangedRegionEntry::Node(ShortCircuitNodeRef(2)))
    );
}
