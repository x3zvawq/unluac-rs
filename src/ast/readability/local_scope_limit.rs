//! 为超大函数里的短生命周期 local 补充有限词法作用域。
//!
//! 本 pass 依赖 Deferred 阶段已经稳定的语句相邻关系和 binding mention，不补 HIR 事实，
//! 也不为减少 local 做可能改变调用或比较顺序的跨语句内联。它沿词法树
//! 携带外层 local 预算，把短生命周期、无属性的声明分批放入 `do ... end`；带属性 local
//! 与 label/goto 边界保持原状。例如同一函数内 240 个顺序临时声明会变成若干个最多 64
//! 个 local 的 `do` 块，而闭包捕获或后续仍读取的 binding 会把作用域延长到最后 mention。
//! repeat body 中被 until 条件读取的 local 必须留在正文直属作用域，不能包进 `do`。
//! Lua 5.5 的 global 声明由 `global-decl-pretty` 负责 block 级补全；本 pass 不新增
//! global 访问，只缩短连续区间，并通过 invalidation 让该 owner 在下一 Deferred 固定点
//! 修复新边界。因此 global 语句不再是永久 scope barrier。

use std::collections::BTreeMap;

use super::super::common::{
    AstBindingRef, AstBlock, AstExpr, AstFunctionExpr, AstLocalAttr, AstLocalBinding,
    AstLocalOrigin, AstModule, AstStmt,
};
use super::binding_flow::{binding_mentions_in_expr, last_binding_mentions};
use super::control_flow::BlockGotoIndex;
use super::{ReadabilityContext, walk};
use crate::ast::traverse::BlockKind;
use walk::ScopedAstRewritePass;

const SCOPE_LOCAL_TARGET: usize = 64;

pub(super) fn apply(module: &mut AstModule, _context: ReadabilityContext) -> bool {
    walk::rewrite_module_scoped(module, 0, &mut LocalScopeLimitPass)
}

struct LocalScopeLimitPass;

impl ScopedAstRewritePass for LocalScopeLimitPass {
    type Scope = usize;

    fn enter_function(&mut self, function: &mut AstFunctionExpr, scope: &mut Self::Scope) {
        *scope = function_entry_local_count(function);
    }

    fn enter_block(
        &mut self,
        block: &mut AstBlock,
        _kind: BlockKind,
        outer_locals: &mut Self::Scope,
    ) -> bool {
        enter_block_with_trailing_condition(block, None, *outer_locals)
    }

    fn enter_repeat_body(
        &mut self,
        block: &mut AstBlock,
        condition: &AstExpr,
        _lifetime: &crate::hir::HirRepeatConditionLifetimeFacts,
        outer_locals: &mut Self::Scope,
    ) -> bool {
        enter_block_with_trailing_condition(block, Some(condition), *outer_locals)
    }

    fn enter_stmt_children(&mut self, stmt: &AstStmt, outer_locals: &mut Self::Scope) {
        // for 控制变量只在 loop body 内可见；控制表达式里即使出现嵌套函数，
        // enter_function 也会重置预算，因此统一给 statement children 加上它们是精确的。
        *outer_locals = outer_locals.saturating_add(stmt_child_local_count(stmt));
    }

    fn after_stmt(&mut self, stmt: &AstStmt, outer_locals: &mut Self::Scope) {
        // Lua local 从声明语句结束后才进入当前 block 的后续词法作用域。
        *outer_locals = outer_locals.saturating_add(direct_local_count(stmt));
    }
}

fn enter_block_with_trailing_condition(
    block: &mut AstBlock,
    trailing_condition: Option<&AstExpr>,
    outer_locals: usize,
) -> bool {
    // 当前 block 的声明由 after_stmt 按源码位置激活，不能在入口一次性加入预算。
    scope_locals(
        block,
        crate::SOURCE_LOCAL_LIMIT.saturating_sub(outer_locals),
        trailing_condition,
    )
}

fn scope_locals(
    block: &mut AstBlock,
    available_locals: usize,
    trailing_condition: Option<&AstExpr>,
) -> bool {
    let direct_local_count = block.stmts.iter().map(direct_local_count).sum::<usize>();
    if available_locals == 0 {
        // 外层/参数已耗尽全部源码 local 预算；内层 `do` 只能缩短
        // 当前 block 自己的 binding，不能降低已活跃的外层数量，因而没有可执行计划。
        return false;
    }
    if direct_local_pressure(&block.stmts) <= available_locals {
        return false;
    }

    let last_mentions = last_binding_mentions(&block.stmts);
    let trailing_mentions = trailing_condition
        .map(binding_mentions_in_expr)
        .unwrap_or_default();
    let scopeable_prefix = scopeable_local_prefix(&block.stmts);
    let lifetime_limit = SCOPE_LOCAL_TARGET.min(available_locals.max(1));
    let short_lived = block
        .stmts
        .iter()
        .enumerate()
        .map(|(index, stmt)| {
            scopeable_bindings(stmt).is_some_and(|bindings| {
                bindings.ids().all(|binding| {
                    // 候选拒绝[SemanticBarrier:Scope]：repeat 的 `until binding` 在 body 直属作用域读取，包进内层 `do` 会使条件失去该 local。
                    !trailing_mentions.contains(&binding) && {
                        let last = last_mentions
                            .get(&binding)
                            .copied()
                            .expect("scopeable declaration must mention its binding");
                        // 候选拒绝[PolicyBoundary]：项目把单个生成作用域的 local 密度限制为
                        // 64；跨过更大窗口的 binding 不进入这一轮紧凑分组。
                        scopeable_prefix[last + 1] - scopeable_prefix[index] <= lifetime_limit
                    }
                })
            })
        })
        .collect::<Vec<_>>();
    let persistent_locals = direct_local_count
        - block
            .stmts
            .iter()
            .enumerate()
            .filter(|(index, _)| short_lived[*index])
            .map(|(_, stmt)| scopeable_bindings(stmt).map_or(0, ScopeableBindings::len))
            .sum::<usize>();
    if persistent_locals >= available_locals {
        // 不可缩短的同时活跃 binding 已耗尽当前 block 的源码 local 预算；
        // 新增 `do` 也不会降低该峰值，因而这里是无候选计划，不是跨 pass 的待办证明。
        return false;
    }
    let scope_target =
        SCOPE_LOCAL_TARGET.min(available_locals.saturating_sub(persistent_locals).max(1));
    let ranges = scope_ranges(&block.stmts, &last_mentions, &short_lived, scope_target);
    if ranges.is_empty() {
        // 所有形成过的 range 已在 planner 内按具体 density、scope 或 lifetime 原因拒绝；
        // 空计划不是新的候选拒绝点。
        return false;
    }

    let old_stmts = std::mem::take(&mut block.stmts);
    let mut old_stmts = old_stmts.into_iter();
    let mut scoped_stmts = Vec::with_capacity(direct_local_count + ranges.len());
    let mut cursor = 0usize;
    for (start, end) in ranges {
        scoped_stmts.extend(old_stmts.by_ref().take(start - cursor));
        let stmts = old_stmts.by_ref().take(end - start).collect();
        scoped_stmts.push(AstStmt::DoBlock(Box::new(AstBlock { stmts })));
        cursor = end;
    }
    scoped_stmts.extend(old_stmts);
    block.stmts = scoped_stmts;
    true
}

pub(super) fn function_entry_local_count(function: &AstFunctionExpr) -> usize {
    function.params.len() + usize::from(function.named_vararg.is_some())
}

pub(super) fn stmt_child_local_count(stmt: &AstStmt) -> usize {
    match stmt {
        AstStmt::NumericFor(_) => 1,
        AstStmt::GenericFor(generic_for) => generic_for.bindings.len(),
        _ => 0,
    }
}

pub(super) fn direct_local_count(stmt: &AstStmt) -> usize {
    match stmt {
        AstStmt::LocalDecl(decl) => decl.bindings.len(),
        AstStmt::LocalFunctionDecl(_) => 1,
        _ => 0,
    }
}

fn direct_local_pressure(stmts: &[AstStmt]) -> usize {
    let mut active = 0usize;
    let mut peak = 0usize;
    for stmt in stmts {
        let loop_bindings = match stmt {
            AstStmt::NumericFor(_) => 1,
            AstStmt::GenericFor(generic_for) => generic_for.bindings.len(),
            _ => 0,
        };
        peak = peak.max(active.saturating_add(loop_bindings));
        active = active.saturating_add(direct_local_count(stmt));
        peak = peak.max(active);
    }
    peak
}

#[derive(Clone, Copy)]
struct ScopeableBindings<'a> {
    locals: &'a [AstLocalBinding],
    local_function: Option<AstBindingRef>,
}

impl<'a> ScopeableBindings<'a> {
    fn ids(self) -> impl Iterator<Item = AstBindingRef> + 'a {
        self.locals
            .iter()
            .map(|binding| binding.id)
            .chain(self.local_function)
    }

    fn len(self) -> usize {
        self.locals.len() + usize::from(self.local_function.is_some())
    }
}

fn scopeable_bindings(stmt: &AstStmt) -> Option<ScopeableBindings<'_>> {
    match stmt {
        AstStmt::LocalDecl(decl)
            if !decl.bindings.is_empty()
                && decl.bindings.iter().all(|binding| {
                    binding.attr == AstLocalAttr::None
                        && binding.origin == AstLocalOrigin::Recovered
                        && binding.rewrite_authority.may_shorten_lifetime()
                }) =>
        {
            Some(ScopeableBindings {
                locals: &decl.bindings,
                local_function: None,
            })
        }
        AstStmt::LocalFunctionDecl(decl)
            if decl.origin == AstLocalOrigin::Recovered
                && decl.rewrite_authority.may_shorten_lifetime() =>
        {
            Some(ScopeableBindings {
                locals: &[],
                local_function: Some(decl.name),
            })
        }
        AstStmt::LocalDecl(_) | AstStmt::LocalFunctionDecl(_) => {
            // 候选拒绝[SemanticBarrier:Lifetime]：PhysicalRoot 与 `<close>` 若提前离开原 block，会改变 GC root/关闭时点。
            // 候选拒绝[SemanticBarrier:DebugScope]：DebugHinted local 的原词法可见期可被 debug API 观察。
            // 候选拒绝[PolicyBoundary]：`<const>` 声明身份不由 local-budget pass 重排。
            None
        }
        _ => None,
    }
}

fn scopeable_local_prefix(stmts: &[AstStmt]) -> Vec<usize> {
    let mut prefix = Vec::with_capacity(stmts.len() + 1);
    prefix.push(0);
    for stmt in stmts {
        prefix.push(
            prefix.last().copied().unwrap_or_default()
                + scopeable_bindings(stmt).map_or(0, ScopeableBindings::len),
        );
    }
    prefix
}

fn scope_ranges(
    stmts: &[AstStmt],
    last_mentions: &BTreeMap<AstBindingRef, usize>,
    short_lived: &[bool],
    scope_target: usize,
) -> Vec<(usize, usize)> {
    let goto_index = BlockGotoIndex::new(stmts);
    let mut ranges = Vec::new();
    let mut index = 0usize;
    while index < stmts.len() {
        let Some(bindings) = scopeable_bindings(&stmts[index]).filter(|_| short_lived[index])
        else {
            index += 1;
            continue;
        };

        let start = index;
        let mut required_end = bindings
            .ids()
            .map(|binding| {
                last_mentions
                    .get(&binding)
                    .copied()
                    .expect("scopeable declaration must mention its binding")
            })
            .max()
            .expect("scopeable declaration must contain a binding");
        let mut scoped_locals = 0usize;
        let mut safe_end = None;
        while index < stmts.len() && !is_scope_barrier(&stmts[index]) {
            if let Some(bindings) = scopeable_bindings(&stmts[index]) {
                if !short_lived[index] {
                    // 候选拒绝[PolicyBoundary]：当前 pass 只生成不超过 64-local 的连续
                    // laminar 作用域，不为交错生命周期引入额外嵌套层。
                    break;
                }
                if scoped_locals + bindings.len() > scope_target {
                    // 候选拒绝[PolicyBoundary]：单个生成作用域最多承载 64 个 local，控制缩进块密度并为外层活跃 binding 留余量。
                    // 声明数只增不减；尚无合法终点时，继续扫描也只能形成超预算区间。
                    break;
                }
                scoped_locals += bindings.len();
                required_end = required_end.max(
                    bindings
                        .ids()
                        .map(|binding| {
                            last_mentions
                                .get(&binding)
                                .copied()
                                .expect("scopeable declaration must mention its binding")
                        })
                        .max()
                        .expect("scopeable declaration must contain a binding"),
                );
            }
            if index >= required_end {
                let end = index + 1;
                // 候选接受：当前 pass 不生成 global 访问，只把同序连续语句放入子 do；
                // 它声明 BindingStructure/ControlFlowShape invalidation，下一 Deferred 固定点
                // 的 global-decl-pretty 会按新 block 边界、逐名/通配属性及 nested write
                // 补全后缀所需声明。regress438 锁定 declaration 与 global-function 可跨
                // local-budget range，最终生成源码仍可重编译运行。
                safe_end = Some((end, scoped_locals));
                if scoped_locals >= scope_target {
                    break;
                }
            }
            index += 1;
        }

        match safe_end {
            Some((end, safe_local_count)) if safe_local_count <= scope_target => {
                if goto_index.has_external_entry(start, end) {
                    // 候选拒绝[SemanticBarrier:Scope]：把 range 包进新 `do` 会让区间外
                    // goto 跳入该 range 内 label；Lua 禁止跳入新 local 词法作用域。
                    index = start + 1;
                } else {
                    // 候选接受：range 内部 goto/label 随整段一起移动，向外 goto 也仍是
                    // 合法的离开作用域；只有外部入边会改变 label 可见性/词法合法性。
                    ranges.push((start, end));
                    index = end;
                }
            }
            _ => {
                // 候选拒绝[PolicyBoundary]：起点到 barrier/扫描终点没有同时闭合且不超过
                // 64-local 密度的连续 laminar range；本 pass 不增加更深的交错嵌套。
                index = start + 1;
            }
        }
    }
    ranges
}

fn is_scope_barrier(stmt: &AstStmt) -> bool {
    // 属性/debug/root 声明的具体拒绝理由由 scopeable_bindings 在同一候选点分类。
    direct_local_count(stmt) != 0 && scopeable_bindings(stmt).is_none()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::common::{
        AstGenericFor, AstGoto, AstLabel, AstLabelId, AstLocalDecl, AstReturn,
    };
    use crate::hir::LocalId;

    fn recovered_local(index: usize) -> AstStmt {
        AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![AstLocalBinding {
                id: AstBindingRef::Local(LocalId(index)),
                attr: AstLocalAttr::None,
                origin: AstLocalOrigin::Recovered,
                rewrite_authority: crate::ast::common::AstRewriteAuthority::AstOwned,
            }],
            values: vec![AstExpr::Integer(index as i64)],
            initializer_merge_transaction: None,
            initializer_root_profile: None,
        }))
    }

    fn debug_local(index: usize) -> AstStmt {
        let AstStmt::LocalDecl(mut decl) = recovered_local(index) else {
            unreachable!();
        };
        decl.bindings[0].origin = AstLocalOrigin::DebugHinted;
        AstStmt::LocalDecl(decl)
    }

    fn return_binding(index: usize) -> AstStmt {
        AstStmt::Return(Box::new(AstReturn {
            values: vec![AstExpr::Var(
                AstBindingRef::Local(LocalId(index)).to_name_ref(),
            )],
        }))
    }

    fn goto(label: usize) -> AstStmt {
        AstStmt::Goto(Box::new(AstGoto {
            target: AstLabelId::Synthetic(label),
        }))
    }

    fn label(label: usize) -> AstStmt {
        AstStmt::Label(Box::new(AstLabel {
            id: AstLabelId::Synthetic(label),
        }))
    }

    #[test]
    fn scopes_preceding_locals_before_generic_for_binder_peak() {
        let mut block = AstBlock {
            stmts: (0..crate::SOURCE_LOCAL_LIMIT - 1)
                .map(recovered_local)
                .chain(std::iter::once(AstStmt::GenericFor(Box::new(
                    AstGenericFor {
                        bindings: vec![
                            AstBindingRef::Local(LocalId(1_000)),
                            AstBindingRef::Local(LocalId(1_001)),
                        ],
                        iterator: vec![AstExpr::Nil],
                        body: AstBlock::default(),
                    },
                ))))
                .collect(),
        };

        assert!(scope_locals(&mut block, crate::SOURCE_LOCAL_LIMIT, None));
        assert!(matches!(block.stmts.first(), Some(AstStmt::DoBlock(_))));
    }

    #[test]
    fn scope_ranges_only_reject_external_goto_entries() {
        let internal = vec![recovered_local(0), goto(7), label(7), return_binding(0)];
        assert_eq!(
            scope_ranges(
                &internal,
                &last_binding_mentions(&internal),
                &[true, false, false, false],
                SCOPE_LOCAL_TARGET,
            ),
            vec![(0, 4)]
        );

        let outgoing = vec![
            recovered_local(0),
            goto(8),
            return_binding(0),
            debug_local(1),
            label(8),
        ];
        assert_eq!(
            scope_ranges(
                &outgoing,
                &last_binding_mentions(&outgoing),
                &[true, false, false, false, false],
                SCOPE_LOCAL_TARGET,
            ),
            vec![(0, 3)]
        );

        let incoming = vec![goto(9), recovered_local(0), label(9), return_binding(0)];
        assert!(
            scope_ranges(
                &incoming,
                &last_binding_mentions(&incoming),
                &[false, true, false, false],
                SCOPE_LOCAL_TARGET,
            )
            .is_empty()
        );
    }
}
