//! 为展开帧的当前 HIR 快照索引源码坐标与 binding 读写。
//! 查询只在调用方确定的无条件覆盖边界内计数，不把不同值版本的读取混在一起。

use super::*;
use crate::hir::simplify::lexical_cfg::HirStmtTree;
use crate::hir::visit::{visit_expr, visit_stmt_header};

pub(super) struct ValueUses<'a> {
    pub points: Vec<(usize, &'a HirStmt)>,
    pub tree: HirStmtTree,
    pub count: usize,
    reads: BTreeMap<HirBinding, Vec<usize>>,
    writes: BTreeMap<HirBinding, usize>,
}

impl<'a> ValueUses<'a> {
    pub fn new(proto: &'a HirProto) -> Self {
        let mut reads = BTreeMap::<HirBinding, Vec<usize>>::new();
        let mut writes = BTreeMap::<HirBinding, usize>::new();
        let mut points = Vec::new();
        let mut count = 0;
        prefix::coordinates::visit(&proto.body, &mut count, &mut |index, kind, stmt| {
            if kind == PointKind::Boundary {
                return;
            }
            if kind == PointKind::Statement {
                points.push((index, stmt));
            }
            let mut collector = (
                BindingReadCollector(|binding| {
                    reads.entry(binding).or_default().push(index);
                }),
                BindingWriteCollector(|binding| {
                    *writes.entry(binding).or_default() += 1;
                }),
            );
            // repeat 条件读取发生在 body 之后，坐标不能提前到循环入口。
            if let HirStmt::Repeat(repeat) = stmt {
                if kind == PointKind::RepeatCondition {
                    visit_expr(&repeat.cond, &mut collector);
                }
            } else {
                visit_stmt_header(stmt, &mut collector);
            }
        });
        // 共享树与源码帧遍历的直属子块先序一致；树不包含 repeat 的额外条件点。
        let tree = HirStmtTree::build(&proto.body.stmts, &mut |_, _| {});
        Self {
            points,
            tree,
            count,
            reads,
            writes,
        }
    }

    pub fn reads(&self, local: LocalId, begin: usize, end: usize) -> usize {
        self.binding_reads(HirBinding::Local(local), begin, end)
    }

    pub fn binding_reads(&self, binding: HirBinding, begin: usize, end: usize) -> usize {
        self.reads.get(&binding).map_or(0, |sites| {
            sites.partition_point(|&site| site < end) - sites.partition_point(|&site| site < begin)
        })
    }

    pub fn writes(&self, local: LocalId) -> usize {
        self.binding_writes(HirBinding::Local(local))
    }

    pub fn binding_writes(&self, binding: HirBinding) -> usize {
        self.writes.get(&binding).copied().unwrap_or(0)
    }
}
