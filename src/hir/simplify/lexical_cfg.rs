//! 这个文件提供 HIR simplify 共用的词法 block 控制流摘要。
//!
//! label 只在其直接 block 建边；嵌套 block 内能够自行解析的 goto 被内部消费，指向父层
//! label 的 goto 则逐层上浮。`break` / `continue` 由最近的 loop owner 消费，恒真/恒假
//! loop 的正常出口使用目标方言 truthiness 事实判定。这样消费者可以在不复制 walker 的
//! 前提下查询顶层 successor、外部出口，以及某条声明是否支配其后的词法作用域入口。
//! 本模块不推断 temp reaching-def 或 root lifetime；这些仍由具体 pass 结合 promotion facts
//! 判断。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{HirBlock, HirLabelId, HirStmt};
use crate::hir::expr_safety::HirExprSafety;

use super::expr_facts::expr_truthiness;
use super::label_refs::count_label_references;
use super::visit::{HirVisitor, visit_stmts};

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(super) enum LexicalCfgFailure {
    AmbiguousLabel,
    ExternalEntry,
}

pub(super) struct LexicalCfg {
    successors: Vec<BTreeSet<usize>>,
    reachable: Vec<bool>,
    has_external_exit: bool,
    has_label_flow: bool,
}

impl LexicalCfg {
    pub(super) fn analyze(
        stmts: &[HirStmt],
        owner_label_refs: &BTreeMap<HirLabelId, usize>,
        safety: HirExprSafety,
    ) -> Result<Self, LexicalCfgFailure> {
        let mut owned_labels = OwnedLabelCollector::default();
        visit_stmts(stmts, &mut owned_labels);
        if owned_labels.has_duplicate {
            return Err(LexicalCfgFailure::AmbiguousLabel);
        }
        let internal_refs = count_label_references(stmts);
        for &label in &owned_labels.labels {
            if owner_label_refs.get(&label).copied().unwrap_or_default()
                != internal_refs.get(&label).copied().unwrap_or_default()
            {
                return Err(LexicalCfgFailure::ExternalEntry);
            }
        }

        let direct_labels = stmts
            .iter()
            .enumerate()
            .filter_map(|(index, stmt)| match stmt {
                HirStmt::Label(label) => Some((label.id, index)),
                _ => None,
            })
            .collect::<BTreeMap<_, _>>();
        let mut successors = vec![BTreeSet::<usize>::new(); stmts.len()];
        let mut has_external_exit = false;
        for (index, stmt) in stmts.iter().enumerate() {
            let summary = summarize_stmt_flow(stmt, safety);
            if index + 1 < stmts.len() && summary.falls_through {
                successors[index].insert(index + 1);
            }
            for target in summary.outgoing_gotos {
                if let Some(&target_index) = direct_labels.get(&target) {
                    successors[index].insert(target_index);
                } else {
                    has_external_exit = true;
                }
            }
        }
        let reachable = reachable_indices(&successors, None);

        Ok(Self {
            successors,
            reachable,
            has_external_exit,
            has_label_flow: !owned_labels.labels.is_empty()
                || !internal_refs.is_empty()
                || has_external_exit,
        })
    }

    pub(super) fn successors(&self) -> &[BTreeSet<usize>] {
        &self.successors
    }

    pub(super) fn has_external_exit(&self) -> bool {
        self.has_external_exit
    }

    pub(super) fn has_label_flow(&self) -> bool {
        self.has_label_flow
    }

    /// 新 local 的词法作用域从 declaration 延伸到 block 末尾；因此任何入口路径若能
    /// 绕过 declaration 到达后缀 label，改写都会生成未初始化读取或非法跳入 local scope。
    pub(super) fn statement_dominates_suffix(&self, declaration: usize) -> bool {
        if declaration >= self.successors.len() || !self.reachable[declaration] {
            return false;
        }
        let reachable_without_declaration = reachable_indices(&self.successors, Some(declaration));
        !reachable_without_declaration[declaration + 1..]
            .iter()
            .any(|reachable| *reachable)
    }
}

fn reachable_indices(successors: &[BTreeSet<usize>], excluded: Option<usize>) -> Vec<bool> {
    let mut reachable = vec![false; successors.len()];
    if successors.is_empty() || excluded == Some(0) {
        return reachable;
    }
    reachable[0] = true;
    let mut pending = vec![0usize];
    while let Some(index) = pending.pop() {
        for &successor in &successors[index] {
            if excluded != Some(successor) && !reachable[successor] {
                reachable[successor] = true;
                pending.push(successor);
            }
        }
    }
    reachable
}

#[derive(Default)]
struct OwnedLabelCollector {
    labels: BTreeSet<HirLabelId>,
    has_duplicate: bool,
}

impl HirVisitor for OwnedLabelCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        if let HirStmt::Label(label) = stmt {
            self.has_duplicate |= !self.labels.insert(label.id);
        }
    }
}

#[derive(Default)]
struct ControlFlowSummary {
    falls_through: bool,
    breaks_loop: bool,
    continues_loop: bool,
    outgoing_gotos: BTreeSet<HirLabelId>,
}

impl ControlFlowSummary {
    fn fallthrough() -> Self {
        Self {
            falls_through: true,
            breaks_loop: false,
            continues_loop: false,
            outgoing_gotos: BTreeSet::new(),
        }
    }

    fn merge(&mut self, other: Self) {
        self.falls_through |= other.falls_through;
        self.breaks_loop |= other.breaks_loop;
        self.continues_loop |= other.continues_loop;
        self.outgoing_gotos.extend(other.outgoing_gotos);
    }
}

fn summarize_stmt_flow(stmt: &HirStmt, safety: HirExprSafety) -> ControlFlowSummary {
    match stmt {
        HirStmt::Goto(goto_stmt) => ControlFlowSummary {
            falls_through: false,
            breaks_loop: false,
            continues_loop: false,
            outgoing_gotos: BTreeSet::from([goto_stmt.target]),
        },
        HirStmt::Break => ControlFlowSummary {
            breaks_loop: true,
            ..ControlFlowSummary::default()
        },
        HirStmt::Continue => ControlFlowSummary {
            continues_loop: true,
            ..ControlFlowSummary::default()
        },
        HirStmt::Return(_) => ControlFlowSummary::default(),
        HirStmt::If(if_stmt) => match expr_truthiness(&if_stmt.cond, safety) {
            Some(true) => summarize_block_flow(&if_stmt.then_block, safety),
            Some(false) => if_stmt
                .else_block
                .as_ref()
                .map_or_else(ControlFlowSummary::fallthrough, |block| {
                    summarize_block_flow(block, safety)
                }),
            None => {
                let mut summary = summarize_block_flow(&if_stmt.then_block, safety);
                if let Some(else_block) = &if_stmt.else_block {
                    summary.merge(summarize_block_flow(else_block, safety));
                } else {
                    summary.falls_through = true;
                }
                summary
            }
        },
        HirStmt::Block(block) => summarize_block_flow(block, safety),
        HirStmt::While(while_stmt) => {
            let truthiness = expr_truthiness(&while_stmt.cond, safety);
            if truthiness == Some(false) {
                return ControlFlowSummary::fallthrough();
            }
            let body = summarize_block_flow(&while_stmt.body, safety);
            ControlFlowSummary {
                falls_through: truthiness != Some(true) || body.breaks_loop,
                breaks_loop: false,
                continues_loop: false,
                outgoing_gotos: body.outgoing_gotos,
            }
        }
        HirStmt::Repeat(repeat_stmt) => {
            let body = summarize_block_flow(&repeat_stmt.body, safety);
            let reaches_condition = body.falls_through || body.continues_loop;
            ControlFlowSummary {
                falls_through: body.breaks_loop
                    || (expr_truthiness(&repeat_stmt.cond, safety) != Some(false)
                        && reaches_condition),
                breaks_loop: false,
                continues_loop: false,
                outgoing_gotos: body.outgoing_gotos,
            }
        }
        HirStmt::NumericFor(numeric_for) => {
            let body = summarize_block_flow(&numeric_for.body, safety);
            ControlFlowSummary {
                falls_through: true,
                breaks_loop: false,
                continues_loop: false,
                outgoing_gotos: body.outgoing_gotos,
            }
        }
        HirStmt::GenericFor(generic_for) => {
            let body = summarize_block_flow(&generic_for.body, safety);
            ControlFlowSummary {
                falls_through: true,
                breaks_loop: false,
                continues_loop: false,
                outgoing_gotos: body.outgoing_gotos,
            }
        }
        HirStmt::Label(_)
        | HirStmt::LocalDecl(_)
        | HirStmt::GlobalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_) => ControlFlowSummary::fallthrough(),
    }
}

fn summarize_block_flow(block: &HirBlock, safety: HirExprSafety) -> ControlFlowSummary {
    let direct_labels = block
        .stmts
        .iter()
        .enumerate()
        .filter_map(|(index, stmt)| match stmt {
            HirStmt::Label(label) => Some((label.id, index)),
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();
    let stmt_summaries = block
        .stmts
        .iter()
        .map(|stmt| summarize_stmt_flow(stmt, safety))
        .collect::<Vec<_>>();
    let mut reachable = vec![false; block.stmts.len() + 1];
    reachable[0] = true;
    let mut pending = vec![0usize];
    let mut outgoing_gotos = BTreeSet::new();
    let mut breaks_loop = false;
    let mut continues_loop = false;

    while let Some(index) = pending.pop() {
        if index == block.stmts.len() {
            continue;
        }
        let summary = &stmt_summaries[index];
        breaks_loop |= summary.breaks_loop;
        continues_loop |= summary.continues_loop;
        if summary.falls_through && !reachable[index + 1] {
            reachable[index + 1] = true;
            pending.push(index + 1);
        }
        for &target in &summary.outgoing_gotos {
            if let Some(&target_index) = direct_labels.get(&target) {
                if !reachable[target_index] {
                    reachable[target_index] = true;
                    pending.push(target_index);
                }
            } else {
                outgoing_gotos.insert(target);
            }
        }
    }

    ControlFlowSummary {
        falls_through: reachable[block.stmts.len()],
        breaks_loop,
        continues_loop,
        outgoing_gotos,
    }
}
