//! 当前语句快照的 inline 候选范围和身份事实。
//!
//! 候选识别归 candidate；这里一次保留识别结果，供失败后从下一句重试的各类 run
//! 消费者复用。原始语句在 plan 提交前不变，索引不适用于改写后的 sink 或新语句列表。
//! 例如 `local a=x; local b=f(a); return b` 的两个起点共享终点 2，而起点 0 的
//! 后续 call-result 是位置 1。声明身份只来自候选本身，不能用其 RHS 读取集合替代。

use std::cell::OnceCell;
use std::collections::BTreeMap;

use super::super::binding_flow::expr_has_binding_read;
use super::candidate::{inline_candidate, stmt_is_adjacent_call_result_sink};
use crate::ast::common::{AstBindingRef, AstExpr, AstStmt};

struct CandidatePosition {
    binding: Option<AstBindingRef>,
    end: usize,
}

pub(super) struct CandidateRunFacts<'a> {
    stmts: &'a [AstStmt],
    positions: Vec<CandidatePosition>,
    call_results: OnceCell<Vec<Option<usize>>>,
    declarations: OnceCell<BTreeMap<AstBindingRef, Vec<usize>>>,
}

impl<'a> CandidateRunFacts<'a> {
    pub(super) fn new(stmts: &'a [AstStmt]) -> Self {
        let mut end = stmts.len();
        let mut positions = Vec::with_capacity(end);
        for (index, stmt) in stmts.iter().enumerate().rev() {
            let binding = inline_candidate(stmt).map(|(candidate, _)| candidate.binding());
            if binding.is_none() {
                end = index;
            }
            positions.push(CandidatePosition { binding, end });
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

    pub(super) fn call_result_after(&self, start: usize) -> Option<usize> {
        self.positions[start].binding?;
        self.call_results.get_or_init(|| {
            let mut results = vec![None; self.stmts.len()];
            let mut next = None;
            for (index, position) in self.positions.iter().enumerate().rev() {
                if position.binding.is_none() {
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
            let mut declarations = BTreeMap::<_, Vec<_>>::new();
            for (index, position) in self.positions.iter().enumerate() {
                if let Some(binding) = position.binding {
                    declarations.entry(binding).or_default().push(index);
                }
            }
            declarations
        });
        let end = self.end(start);
        expr_has_binding_read(expr, |binding| {
            binding != except
                && declarations.get(&binding).is_some_and(|indices| {
                    indices
                        .get(indices.partition_point(|&index| index < start))
                        .is_some_and(|&index| index < end)
                })
        })
    }
}
