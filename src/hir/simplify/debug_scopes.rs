//! 将已接受的源码 debug local 尾区间物化为 HIR 词法块。
//!
//! 消费 Structure 的可信区间和 LocalId 的 scope 身份，保留 `debug.getlocal` 可观察的
//! 生命周期；结合目标方言的函数边界与显式 cleanup，避免为同一尾部终点重复嵌套块。

use crate::hir::common::{HirBlock, HirDebugScope, HirExpr, HirLValue, HirProto, HirStmt};
use crate::hir::visit::visit_stmt_structure;
use crate::transformer::{CloseKind, InstrRef};
use std::collections::BTreeSet;

use super::label_refs::label_references_by_stmt;
use super::walk::{HirRewritePass, rewrite_stmts};

pub(super) fn materialize_tail_debug_scopes_in_proto(
    proto: &mut HirProto,
    dialect: crate::decompile::DecompileDialect,
) -> bool {
    let mut pass = TailDebugScopePass {
        local_debug_scopes: &proto.local_debug_scopes,
        debug_scopes: &proto.debug_scopes,
    };
    let nested_changed = rewrite_stmts(&mut proto.body.stmts, &mut pass);
    let root_changed = materialize_tail_scopes(
        &mut proto.body,
        &proto.local_debug_scopes,
        &proto.debug_scopes,
        dialect == crate::decompile::DecompileDialect::Lua51,
    );
    root_changed || nested_changed
}

struct TailDebugScopePass<'a> {
    local_debug_scopes: &'a [Option<usize>],
    debug_scopes: &'a [Option<HirDebugScope>],
}

impl HirRewritePass for TailDebugScopePass<'_> {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        materialize_tail_scopes(block, self.local_debug_scopes, self.debug_scopes, false)
    }
}

fn materialize_tail_scopes(
    block: &mut HirBlock,
    local_debug_scopes: &[Option<usize>],
    debug_scopes: &[Option<HirDebugScope>],
    function_end_closes_debug_scopes: bool,
) -> bool {
    // 只处理空终结 Return：它没有可能经物理 COPY 依赖待退出 scope 的结果。
    // 区间终点由前层证明，不能从声明位置推测其它 PC/HIR 布局。
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
                if ret.pending_cleanup_source != Some(source) {
                    // 候选拒绝[ProofIncomplete]：原始返回事务的两部分已不匹配，不能切开尾部猜词法边界。
                    return false;
                }
                body_end = index;
            }
        }
    }

    // Lua 5.1 close_func 在生成隐式 RETURN 前调用 removevars；函数根块自身
    // 就提供此 debug 终点。额外 do 会引入原本属于 RETURN 的 upvalue CLOSE。
    // 独立 CLOSE 仍要求显式词法边界；嵌套块不能借函数根块的编译规则省略边界。
    if function_end_closes_debug_scopes && explicit_cleanup.is_none() {
        return false;
    }

    // 空 Return 没有结果快照；原始 frame cleanup 的配对仍保留在新块外。
    let label_refs = std::cell::OnceCell::new();
    let first_start = block
        .stmts
        .iter()
        .enumerate()
        .take(body_end)
        .find_map(|(index, stmt)| {
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
        });
    let Some(first_start) = first_start else {
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
        // 同一尾块内的资源按原声明逆序关闭，共同拥有这条 cleanup。
        body_end = index;
    }

    let mut stmts = std::mem::take(&mut block.stmts).into_iter();
    let mut rewritten: Vec<_> = stmts.by_ref().take(first_start).collect();
    rewritten.push(HirStmt::Block(Box::new(HirBlock {
        // local 的起点由声明自身限定；相同末端无需为后续每个 local 再套一层块。
        stmts: stmts.by_ref().take(body_end - first_start).collect(),
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
