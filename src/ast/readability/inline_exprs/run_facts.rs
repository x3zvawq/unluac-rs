//! 当前语句快照的 inline 候选属性、RHS 与连续段事实。
//!
//! 候选识别归 candidate；这里一次保留识别结果，供失败后从下一句重试的各类 run
//! 消费者复用。原始语句在 plan 提交前不变，索引不适用于改写后的 sink 或新语句列表。
//! 例如 `local a=x; local b=f(a); return b` 的两个起点共享终点 2，而起点 0 的
//! 后续 call-result 是位置 1。声明身份、debug 来源与 initializer root 属性保留自
//! candidate 的识别结果；RHS 借用原快照，不克隆表达式，也不用于逐步改写中的 stable-copy。

use crate::graph::PositionIndex;
use std::cell::OnceCell;

use super::super::binding_flow::expr_has_binding_read;
use super::candidate::{InlineCandidate, inline_candidate, stmt_is_adjacent_call_result_sink};
use crate::ast::common::{AstBindingRef, AstExpr, AstStmt};

struct CandidatePosition<'a> {
    candidate: Option<(InlineCandidate, &'a AstExpr)>,
    end: usize,
}

pub(super) struct CandidateRunFacts<'a> {
    stmts: &'a [AstStmt],
    positions: Vec<CandidatePosition<'a>>,
    call_results: OnceCell<Vec<Option<usize>>>,
    declarations: OnceCell<PositionIndex<AstBindingRef>>,
}

impl<'a> CandidateRunFacts<'a> {
    pub(super) fn new(stmts: &'a [AstStmt]) -> Self {
        let mut end = stmts.len();
        let mut positions = Vec::with_capacity(end);
        for (index, stmt) in stmts.iter().enumerate().rev() {
            let candidate = inline_candidate(stmt);
            if candidate.is_none() {
                end = index;
            }
            positions.push(CandidatePosition { candidate, end });
        }
        positions.reverse();
        Self {
            stmts,
            positions,
            call_results: OnceCell::new(),
            declarations: OnceCell::new(),
        }
    }

    pub(super) fn end(&self, start: usize) -> usize {
        self.positions[start].end
    }

    pub(super) fn candidate_at(&self, index: usize) -> Option<(InlineCandidate, &'a AstExpr)> {
        self.positions[index].candidate
    }

    pub(super) fn binding_at(&self, index: usize) -> Option<AstBindingRef> {
        self.candidate_at(index)
            .map(|(candidate, _)| candidate.binding())
    }

    pub(super) fn call_result_after(&self, start: usize) -> Option<usize> {
        self.candidate_at(start)?;
        self.call_results.get_or_init(|| {
            let mut results = vec![None; self.stmts.len()];
            let mut next = None;
            for (index, position) in self.positions.iter().enumerate().rev() {
                if position.candidate.is_none() {
                    next = None;
                } else {
                    results[index] = next;
                    if stmt_is_adjacent_call_result_sink(&self.stmts[index]) {
                        next = Some(index);
                    }
                }
            }
            results
        })[start]
    }

    pub(super) fn reads_other_candidate(
        &self,
        expr: &AstExpr,
        start: usize,
        except: AstBindingRef,
    ) -> bool {
        let declarations = self.declarations.get_or_init(|| {
            let mut declarations = PositionIndex::default();
            for (index, position) in self.positions.iter().enumerate() {
                if let Some((candidate, _)) = position.candidate {
                    declarations.record(candidate.binding(), index);
                }
            }
            declarations
        });
        let end = self.end(start);
        expr_has_binding_read(expr, |binding| {
            binding != except && declarations.last_in(&binding, start..end).is_some()
        })
    }
}
