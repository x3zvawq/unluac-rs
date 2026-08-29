//! 将已接受的源码 debug local 尾区间物化为 HIR 词法块。
//!
//! DebugHinted 只保留名字身份并不足以保留 `debug.getlocal` 可观察的生命周期。Structure
//! 已经把每个可信 debug entry 绑定到唯一 SSA，并保留原始 PC 区间；locals promotion
//! 必须把 scope identity 继续带到 LocalId。这里仅消费一种边界完全可证明的形状：debug
//! 区间的终点直接落在当前 HIR block 的空终结 Return 上。此时声明到 Return 前之间没有
//! 未表示的 low-IR 指令，Return 也不携带可能由物理 copy 间接依赖该 scope 的结果，因而
//! 可以安全恢复尾部 `do ... end`；其它 PC/HIR value 布局不靠声明位置猜测。

use std::collections::BTreeSet;

use crate::hir::common::{HirBlock, HirDebugScope, HirProto, HirStmt};

use super::label_refs::count_label_references;
use super::mention::stmts_mention_local;
use super::walk::{HirRewritePass, rewrite_proto};

pub(super) fn materialize_tail_debug_scopes_in_proto(proto: &mut HirProto) -> bool {
    let mut pass = TailDebugScopePass {
        local_debug_scopes: proto.local_debug_scopes.clone(),
        debug_scopes: proto.debug_scopes.clone(),
    };
    rewrite_proto(proto, &mut pass)
}

struct TailDebugScopePass {
    local_debug_scopes: Vec<Option<usize>>,
    debug_scopes: Vec<Option<HirDebugScope>>,
}

impl HirRewritePass for TailDebugScopePass {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        materialize_tail_scopes(block, &self.local_debug_scopes, &self.debug_scopes)
    }
}

fn materialize_tail_scopes(
    block: &mut HirBlock,
    local_debug_scopes: &[Option<usize>],
    debug_scopes: &[Option<HirDebugScope>],
) -> bool {
    let Some(return_index) = block
        .stmts
        .len()
        .checked_sub(1)
        .filter(|index| {
            matches!(&block.stmts[*index], HirStmt::Return(return_stmt) if return_stmt.values.is_empty())
        })
    else {
        return false;
    };
    let body_end = return_index
        .checked_sub(1)
        .filter(
            |index| matches!(&block.stmts[*index], HirStmt::Close(close) if close.from_reg == 0),
        )
        .unwrap_or(return_index);

    let mut starts = block
        .stmts
        .iter()
        .enumerate()
        .take(body_end)
        .filter_map(|(index, stmt)| {
            let HirStmt::LocalDecl(local_decl) = stmt else {
                return None;
            };
            let mut ranges = local_decl.bindings.iter().map(|local| {
                local_debug_scopes
                    .get(local.index())
                    .copied()
                    .flatten()
                    .and_then(|scope| debug_scopes.get(scope).copied().flatten())
            });
            let range = ranges.next().flatten()?;
            (range.ends_before_return
                && ranges.all(|candidate| candidate == Some(range))
                && local_decl
                    .bindings
                    .iter()
                    .all(|local| !stmts_mention_local(&block.stmts[body_end..], *local))
                && !scope_has_external_entry(&block.stmts, index, body_end))
            .then_some(index)
        })
        .collect::<Vec<_>>();
    starts.sort_unstable();
    starts.dedup();
    let Some(first_start) = starts.first().copied() else {
        return false;
    };

    let mut rewritten = block.stmts[..first_start].to_vec();
    rewritten.push(HirStmt::Block(Box::new(HirBlock {
        stmts: nest_tail(&block.stmts, first_start, body_end, &starts[1..]),
    })));
    rewritten.extend_from_slice(&block.stmts[body_end..]);
    block.stmts = rewritten;
    true
}

fn nest_tail(stmts: &[HirStmt], start: usize, end: usize, nested_starts: &[usize]) -> Vec<HirStmt> {
    let Some((&next_start, rest)) = nested_starts.split_first() else {
        return stmts[start..end].to_vec();
    };
    let mut nested = stmts[start..next_start].to_vec();
    nested.push(HirStmt::Block(Box::new(HirBlock {
        stmts: nest_tail(stmts, next_start, end, rest),
    })));
    nested
}

fn scope_has_external_entry(stmts: &[HirStmt], start: usize, end: usize) -> bool {
    let external_targets = count_label_references(&stmts[..start])
        .into_keys()
        .collect::<BTreeSet<_>>();
    stmts[start..end]
        .iter()
        .any(|stmt| matches!(stmt, HirStmt::Label(label) if external_targets.contains(&label.id)))
}
