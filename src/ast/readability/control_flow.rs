//! 分析当前 AST 的词法跳转、落空与支配关系。
//!
//! 消费当前函数的语句结构，供 Readability 查询；不读取前层 CFG 或进入 child function。

use std::collections::BTreeMap;

use crate::graph;

use super::super::common::{AstBlock, AstLabelId, AstStmt};
use crate::ast::visit::any_stmt_structure;

pub(super) fn block_contains_label_or_goto(block: &AstBlock) -> bool {
    block.stmts.iter().any(stmt_contains_label_or_goto)
}

pub(super) fn stmt_contains_label_or_goto(stmt: &AstStmt) -> bool {
    any_stmt_structure(stmt, &mut |stmt| {
        matches!(stmt, AstStmt::Label(_) | AstStmt::Goto(_))
    })
}

pub(super) struct BlockGotoIndex(graph::LabelReferenceIndex<AstLabelId>);

impl BlockGotoIndex {
    pub(super) fn new(stmts: &[AstStmt]) -> Self {
        let refs = stmts
            .iter()
            .map(|stmt| collect_jumps(stmt).refs)
            .collect::<Vec<_>>();
        Self(graph::LabelReferenceIndex::new(&refs))
    }

    pub(super) fn has_external_entry(&self, start: usize, end: usize) -> bool {
        self.0.has_incoming_outside(start..end, start..end)
    }
}

/// Repeat body 顶层语句 CFG；nested goto/continue 映射到所属顶层 statement。
///
/// 这份图只回答 dominance/must-execute，不尝试恢复 structured statement 内部的逐节点
/// 路径。调用方若把一个 structured statement 当作 handoff owner，仍需单独证明它的每条
/// fallthrough/continue 路径已经完成 handoff。
pub(super) struct RepeatBodyControlFlow {
    dominance: graph::DominatorTree<usize>,
    exit: usize,
}

impl RepeatBodyControlFlow {
    pub(super) fn new(stmts: &[AstStmt]) -> Option<Self> {
        let exit = stmts.len();
        let jumps = stmts.iter().map(collect_jumps).collect::<Vec<_>>();
        let mut label_owners = BTreeMap::new();
        for (stmt_index, jump) in jumps.iter().enumerate() {
            for &label in &jump.refs.labels {
                if label_owners.insert(label, stmt_index).is_some() {
                    return None;
                }
            }
        }

        let mut successors = vec![Vec::new(); stmts.len() + 1];
        for (stmt_index, jump) in jumps.into_iter().enumerate() {
            for target in jump.refs.goto_targets {
                successors[stmt_index].push(*label_owners.get(&target)?);
            }
            if jump.has_continue {
                successors[stmt_index].push(exit);
            }
            if jump.may_fall_through {
                successors[stmt_index].push(stmt_index + 1);
            }
            successors[stmt_index].sort_unstable();
            successors[stmt_index].dedup();
        }
        let mut predecessors = vec![Vec::new(); successors.len()];
        for (node, targets) in successors.iter().enumerate() {
            for &target in targets {
                predecessors[target].push(node);
            }
        }
        let traversal = graph::depth_first(
            successors.len(),
            0,
            |node| node,
            |_| exit != 0,
            |node| successors[node].iter().copied(),
        );
        let dominance = graph::dominator_tree(
            &traversal,
            |node| node,
            |node| node,
            |node| predecessors[node].iter().copied(),
        )
        .expect("repeat CFG traversal must define a valid dominance tree");
        Some(Self { dominance, exit })
    }

    pub(super) const fn exit(&self) -> usize {
        self.exit
    }

    pub(super) fn dominates(&self, dominator: usize, node: usize) -> bool {
        dominator < self.exit
            && node <= self.exit
            && self.dominance.dominates(dominator, node, |node| node)
    }
}

#[derive(Default)]
struct GotoLabelCollector {
    refs: graph::LabelReferences<AstLabelId>,
    has_continue: bool,
    may_fall_through: bool,
}

struct StatementFlow {
    has_jump: bool,
    may_fall_through: bool,
}

impl GotoLabelCollector {
    fn collect_stmt(&mut self, stmt: &AstStmt) -> StatementFlow {
        match stmt {
            AstStmt::Goto(goto) => {
                self.refs.goto_targets.insert(goto.target);
            }
            AstStmt::Label(label) => {
                self.refs.labels.insert(label.id);
            }
            AstStmt::Continue => self.has_continue = true,
            _ => {}
        }
        let mut flow = StatementFlow {
            has_jump: matches!(stmt, AstStmt::Label(_) | AstStmt::Goto(_)),
            may_fall_through: match stmt {
                AstStmt::Return(_) | AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) => false,
                AstStmt::If(if_stmt) => if_stmt.else_block.is_none(),
                _ => true,
            },
        };
        crate::ast::traverse::traverse_stmt_children!(
            stmt,
            iter = iter,
            opt = as_ref,
            borrow = [&],
            expr(_expr) => {},
            lvalue(_lvalue) => {},
            block(block) => {
                let child = self.collect_block(block);
                flow.has_jump |= child.has_jump;
                match stmt {
                    AstStmt::If(_) => flow.may_fall_through |= child.may_fall_through,
                    AstStmt::DoBlock(_) => flow.may_fall_through = child.may_fall_through,
                    _ => {}
                }
            },
            function(_function) => {},
            condition(_condition) => {},
            call(_call) => {}
        );
        flow
    }

    fn collect_block(&mut self, block: &AstBlock) -> StatementFlow {
        let mut flow = StatementFlow {
            has_jump: false,
            may_fall_through: true,
        };
        for stmt in &block.stmts {
            let child = self.collect_stmt(stmt);
            flow.has_jump |= child.has_jump;
            flow.may_fall_through &= child.may_fall_through;
        }
        // 未构造 owner 内部 CFG：嵌套 goto 可能越过 terminator 后重新落入 label，
        // 因而保留整个 block 的落空边。即使已遇到 terminator，也必须收集后续跳转。
        flow.may_fall_through |= flow.has_jump;
        flow
    }
}

fn collect_jumps(stmt: &AstStmt) -> GotoLabelCollector {
    let mut collector = GotoLabelCollector::default();
    collector.may_fall_through = collector.collect_stmt(stmt).may_fall_through;
    collector
}
