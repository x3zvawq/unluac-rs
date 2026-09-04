//! 将已接受的源码 debug local 尾区间物化为 HIR 词法块。
//!
//! DebugHinted 只保留名字身份并不足以保留 `debug.getlocal` 可观察的生命周期。Structure
//! 已经把每个可信 debug entry 绑定到唯一 SSA，并保留原始 PC 区间；locals promotion
//! 必须把 scope identity 继续带到 LocalId。这里仅消费一种边界完全可证明的形状：debug
//! 区间的终点直接落在当前 HIR block 的空终结 Return 上。此时声明到 Return 前之间没有
//! 未表示的 low-IR 指令，Return 也不携带可能由物理 copy 间接依赖该 scope 的结果，因而
//! 可以安全恢复尾部 `do ... end`；其它 PC/HIR value 布局不靠声明位置猜测。
//! 接受的起点按当前语句位置递增；提交消费同一快照的段长，移动节点而不复制 HIR 子树。

use crate::hir::common::{HirBlock, HirDebugScope, HirProto, HirStmt};

use super::label_refs::label_references_by_stmt;
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

    // 已证明尾部仅为空 Return 或 Close(0) + 空 Return，不含任何 binding 引用。
    let label_refs = std::cell::OnceCell::new();
    let starts = block
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
                && !label_refs
                    .get_or_init(|| {
                        let mut refs = label_references_by_stmt(&block.stmts);
                        // 此候选只检查直属 label；嵌套 label 仍由原来的子块拥有。
                        for (stmt, refs) in block.stmts.iter().zip(&mut refs) {
                            if !matches!(stmt, HirStmt::Label(_)) {
                                refs.labels.clear();
                            }
                        }
                        crate::graph::LabelReferenceIndex::new(&refs)
                    })
                    .has_incoming_outside(index..body_end, index..block.stmts.len()))
            .then_some(index)
        })
        .collect::<Vec<_>>();
    let Some(first_start) = starts.first().copied() else {
        return false;
    };

    let mut stmts = std::mem::take(&mut block.stmts).into_iter();
    let mut rewritten: Vec<_> = stmts.by_ref().take(first_start).collect();
    rewritten.push(HirStmt::Block(Box::new(HirBlock {
        stmts: nest_tail(&mut stmts, first_start, body_end, &starts[1..]),
    })));
    rewritten.extend(stmts);
    block.stmts = rewritten;
    true
}

fn nest_tail(
    stmts: &mut std::vec::IntoIter<HirStmt>,
    start: usize,
    end: usize,
    nested_starts: &[usize],
) -> Vec<HirStmt> {
    let Some((&next_start, rest)) = nested_starts.split_first() else {
        return stmts.by_ref().take(end - start).collect();
    };
    let mut nested: Vec<_> = stmts.by_ref().take(next_start - start).collect();
    nested.push(HirStmt::Block(Box::new(HirBlock {
        stmts: nest_tail(stmts, next_start, end, rest),
    })));
    nested
}
