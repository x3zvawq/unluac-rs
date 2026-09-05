//! 将已接受的源码 debug local 尾区间物化为 HIR 词法块。
//!
//! DebugHinted 只保留名字身份并不足以保留 `debug.getlocal` 可观察的生命周期。Structure
//! 已经把每个可信 debug entry 绑定到唯一 SSA，并保留原始 PC 区间；locals promotion
//! 必须把 scope identity 继续带到 LocalId。这里仅消费一种边界完全可证明的形状：debug
//! 区间的终点直接落在当前 HIR block 的空终结 Return 上。此时声明到 Return 前之间没有
//! 未表示的 low-IR 指令，Return 也不携带可能由物理 copy 间接依赖该 scope 的结果，因而
//! 可以安全恢复尾部 `do ... end`；其它 PC/HIR value 布局不靠声明位置猜测。
//! 接受的起点按当前语句位置递增；提交消费同一快照的段长，移动节点而不复制 HIR 子树。
//! 独立 cleanup 与 Return 内含 cleanup 不共享尾部规则：前者只有全部资源绑定都由新块
//! 拥有时才随该词法边界消费；后者保持同来源的 Close/Return 相邻，不按零槽猜协议。

use crate::hir::common::{HirBlock, HirDebugScope, HirExpr, HirLValue, HirProto, HirStmt};
use crate::hir::visit::visit_stmt_structure;
use crate::transformer::{CloseKind, InstrRef};
use std::collections::BTreeSet;

use super::label_refs::label_references_by_stmt;
use super::walk::{HirRewritePass, rewrite_block};

pub(super) fn materialize_tail_debug_scopes_in_proto(proto: &mut HirProto) -> bool {
    let mut pass = TailDebugScopePass {
        local_debug_scopes: &proto.local_debug_scopes,
        debug_scopes: &proto.debug_scopes,
    };
    rewrite_block(&mut proto.body, &mut pass)
}

struct TailDebugScopePass<'a> {
    local_debug_scopes: &'a [Option<usize>],
    debug_scopes: &'a [Option<HirDebugScope>],
}

impl HirRewritePass for TailDebugScopePass<'_> {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        materialize_tail_scopes(block, self.local_debug_scopes, self.debug_scopes)
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
    let mut body_end = return_index;
    let mut explicit_cleanup = None;
    if let Some(index) = return_index.checked_sub(1)
        && let HirStmt::Close(close) = &block.stmts[index]
    {
        match close.kind {
            CloseKind::Explicit => explicit_cleanup = Some(index),
            CloseKind::Return(source) | CloseKind::TailCall(source) => {
                let HirStmt::Return(ret) = &block.stmts[return_index] else {
                    unreachable!("the terminal empty Return was checked above");
                };
                if ret.source_instr != Some(source) {
                    // 候选拒绝[ProofIncomplete]：原始返回事务的两部分已不匹配，不能切开尾部猜词法边界。
                    return false;
                }
                body_end = index;
            }
        }
    }

    // 空 Return 没有结果快照；原始 frame cleanup 的配对仍保留在新块外。
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
    if let Some(index) = explicit_cleanup {
        let HirStmt::Close(close) = &block.stmts[index] else {
            unreachable!("the explicit cleanup belongs to the unchanged snapshot");
        };
        let owned_origins = declared_resource_origins(&block.stmts[first_start..index]);
        if close.origins.is_empty()
            || !close
                .origins
                .iter()
                .all(|origin| owned_origins.contains(origin))
        {
            // 候选拒绝[ProofIncomplete]：cleanup 还关闭新块之外或身份未发布的资源，不能用局部词法退出代替。
            return false;
        }
        // 新建的所有尾块在同一位置结束；其资源按原声明逆序关闭，共同拥有这条 cleanup。
        body_end = index;
    }

    let mut stmts = std::mem::take(&mut block.stmts).into_iter();
    let mut rewritten: Vec<_> = stmts.by_ref().take(first_start).collect();
    rewritten.push(HirStmt::Block(Box::new(HirBlock {
        stmts: nest_tail(&mut stmts, first_start, body_end, &starts[1..]),
    })));
    if explicit_cleanup.is_some() {
        stmts
            .next()
            .expect("the validated explicit cleanup follows the moved body");
    }
    rewritten.extend(stmts);
    block.stmts = rewritten;
    true
}

/// TBC 的注册与实际绑定声明都必须落在新块内；只有 origin 出现不代表该块拥有其 binding。
fn declared_resource_origins(stmts: &[HirStmt]) -> BTreeSet<InstrRef> {
    let mut locals = BTreeSet::new();
    let mut temps = BTreeSet::new();
    for stmt in stmts {
        visit_stmt_structure(stmt, &mut |stmt| match stmt {
            HirStmt::LocalDecl(decl) => locals.extend(decl.bindings.iter().copied()),
            HirStmt::Assign(assign) => temps.extend(assign.targets.iter().filter_map(|target| {
                if let HirLValue::Temp(temp) = target {
                    Some(*temp)
                } else {
                    None
                }
            })),
            _ => {}
        });
    }
    let mut origins = BTreeSet::new();
    for stmt in stmts {
        visit_stmt_structure(stmt, &mut |stmt| {
            if let HirStmt::ToBeClosed(tbc) = stmt {
                let declared = match &tbc.value {
                    HirExpr::LocalRef(local) => locals.contains(local),
                    HirExpr::TempRef(temp) => temps.contains(temp),
                    _ => false,
                };
                if declared {
                    origins.insert(tbc.origin);
                }
            }
        });
    }
    origins
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
