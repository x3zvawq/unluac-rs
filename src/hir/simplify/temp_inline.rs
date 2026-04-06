//! 这个文件实现 HIR 的第一批 temp inlining。
//!
//! 我们故意把规则收得很保守：只折叠“单目标 temp 赋值，并且被紧邻下一条简单语句
//! 使用一次”的情况。这样可以先清掉大量机械性的寄存器搬运，又不会把求值顺序、
//! 控制流边界或 debug 语义悄悄改坏。

mod mentioned;
mod rewrite;
mod site;
mod usage;

use std::collections::BTreeSet;

use crate::hir::common::{
    HirBlock, HirCallExpr, HirExpr, HirLValue, HirProto, HirStmt, HirTableField, HirTableKey,
    TempId,
};
use crate::hir::promotion::ProtoPromotionFacts;
use crate::readability::ReadabilityOptions;

use self::mentioned::protected_temps_for_nested_stmt;
use self::rewrite::replace_temp_in_stmt;
use self::site::{expr_touches_temp, inline_site_in_stmt};
use self::usage::{
    NextStmtState, TempUseScratch, collect_stmt_temp_uses, inline_candidate,
    max_temp_index_in_block,
};

const NESTED_INLINE_MAX_COMPLEXITY: usize = 5;
const CONTROL_HEAD_INLINE_MAX_COMPLEXITY: usize = 5;

/// 对单个 proto 递归执行局部 temp 折叠。
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn inline_temps_in_proto(proto: &mut HirProto, readability: ReadabilityOptions) -> bool {
    inline_temps_in_proto_with_facts(proto, readability, &ProtoPromotionFacts::default())
}

pub(super) fn inline_temps_in_proto_with_facts(
    proto: &mut HirProto,
    readability: ReadabilityOptions,
    facts: &ProtoPromotionFacts,
) -> bool {
    let proto_temp_count = proto
        .temps
        .iter()
        .map(|temp| temp.index())
        .max()
        .map_or(0, |max_index| max_index + 1);
    let body_temp_count = max_temp_index_in_block(&proto.body).map_or(0, |max_index| max_index + 1);
    let temp_count = proto_temp_count.max(body_temp_count);
    let mut scratch = TempUseScratch::new(proto, temp_count);
    inline_temps_in_block(
        &mut proto.body,
        &mut scratch,
        readability,
        facts,
        &BTreeSet::new(),
        &BTreeSet::new(),
    )
}

fn inline_temps_in_block(
    block: &mut HirBlock,
    scratch: &mut TempUseScratch,
    readability: ReadabilityOptions,
    facts: &ProtoPromotionFacts,
    protected_temps: &BTreeSet<TempId>,
    inherited_captured_slots: &BTreeSet<usize>,
) -> bool {
    let mut changed = false;
    let mut captured_slots_before_stmt = Vec::with_capacity(block.stmts.len());
    let mut active_captured_slots = inherited_captured_slots.clone();

    for index in 0..block.stmts.len() {
        captured_slots_before_stmt.push(active_captured_slots.clone());
        let nested_protected =
            protected_temps_for_nested_stmt(&block.stmts, index, protected_temps);
        let mut nested_captured_slots = active_captured_slots.clone();
        facts.collect_prefix_captured_home_slots_in_stmt(
            &block.stmts[index],
            &mut nested_captured_slots,
        );
        let stmt = &mut block.stmts[index];
        changed |= inline_temps_in_nested_blocks(
            stmt,
            scratch,
            readability,
            facts,
            &nested_protected,
            &nested_captured_slots,
        );
        facts.collect_captured_home_slots_in_stmt(stmt, &mut active_captured_slots);
    }

    // 逆向扫描只需要维护“后缀里每个 temp 当前被用了多少次”以及最近一个保留下来的
    // 语句。这样可以在不反复重扫整个后缀的前提下，保留“只内联到最近简单语句”的约束。
    let mut suffix_use_totals = vec![0; scratch.temp_count()];
    let mut kept_rev = Vec::with_capacity(block.stmts.len());
    let mut next_stmt_state: Option<NextStmtState> = None;

    for (index, stmt) in std::mem::take(&mut block.stmts)
        .into_iter()
        .enumerate()
        .rev()
    {
        if let Some((temp, value)) = inline_candidate(&stmt)
            && !scratch.has_debug_local_hint(temp)
            && !protected_temps.contains(&temp)
            && !temp_rebinds_captured_slot(
                temp,
                facts,
                captured_slots_before_stmt
                    .get(index)
                    .expect("forward scan should record every statement"),
            )
            // `t = t + step` 这类自更新赋值表面上只在后缀里被用了一次，
            // 但它本质上承载的是跨语句/跨迭代的状态推进。
            // 一旦把它内联进下一条 `yield/return/call`，当前赋值本身就会消失，
            // 后续再也没有地方记录“状态已经更新过”。
            // 因此这里只允许折叠真正的 forwarding temp，不折叠自引用状态槽位。
            && !expr_touches_temp(value, temp)
            && suffix_use_totals.get(temp.index()).copied().unwrap_or(0) == 1
            && let Some(state) = &mut next_stmt_state
            && state.temp_uses.count(temp) == 1
            && kept_rev
                .last()
                .and_then(|next_stmt| inline_site_in_stmt(next_stmt, temp))
                .is_some_and(|site| site.allows(value, readability))
        {
            state.temp_uses.remove_from_totals(&mut suffix_use_totals);
            let next_stmt = kept_rev
                .last_mut()
                .expect("next stmt metadata must track the last kept stmt");
            replace_temp_in_stmt(next_stmt, temp, value);
            state.temp_uses = collect_stmt_temp_uses(next_stmt, scratch);
            state.temp_uses.add_to_totals(&mut suffix_use_totals);
            changed = true;
            continue;
        }

        let stmt_uses = collect_stmt_temp_uses(&stmt, scratch);
        stmt_uses.add_to_totals(&mut suffix_use_totals);
        next_stmt_state = Some(NextStmtState {
            temp_uses: stmt_uses,
        });
        kept_rev.push(stmt);
    }

    kept_rev.reverse();
    block.stmts = kept_rev;

    changed
}

fn inline_temps_in_nested_blocks(
    stmt: &mut HirStmt,
    scratch: &mut TempUseScratch,
    readability: ReadabilityOptions,
    facts: &ProtoPromotionFacts,
    protected_temps: &BTreeSet<TempId>,
    inherited_captured_slots: &BTreeSet<usize>,
) -> bool {
    match stmt {
        HirStmt::If(if_stmt) => {
            let mut changed = inline_temps_in_block(
                &mut if_stmt.then_block,
                scratch,
                readability,
                facts,
                protected_temps,
                inherited_captured_slots,
            );
            if let Some(else_block) = &mut if_stmt.else_block {
                changed |= inline_temps_in_block(
                    else_block,
                    scratch,
                    readability,
                    facts,
                    protected_temps,
                    inherited_captured_slots,
                );
            }
            changed
        }
        HirStmt::While(while_stmt) => inline_temps_in_block(
            &mut while_stmt.body,
            scratch,
            readability,
            facts,
            protected_temps,
            inherited_captured_slots,
        ),
        HirStmt::Repeat(repeat_stmt) => inline_temps_in_block(
            &mut repeat_stmt.body,
            scratch,
            readability,
            facts,
            protected_temps,
            inherited_captured_slots,
        ),
        HirStmt::NumericFor(numeric_for) => inline_temps_in_block(
            &mut numeric_for.body,
            scratch,
            readability,
            facts,
            protected_temps,
            inherited_captured_slots,
        ),
        HirStmt::GenericFor(generic_for) => inline_temps_in_block(
            &mut generic_for.body,
            scratch,
            readability,
            facts,
            protected_temps,
            inherited_captured_slots,
        ),
        HirStmt::Block(block) => inline_temps_in_block(
            block,
            scratch,
            readability,
            facts,
            protected_temps,
            inherited_captured_slots,
        ),
        HirStmt::Unstructured(unstructured) => inline_temps_in_block(
            &mut unstructured.body,
            scratch,
            readability,
            facts,
            protected_temps,
            inherited_captured_slots,
        ),
        HirStmt::LocalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => false,
    }
}

fn temp_rebinds_captured_slot(
    temp: TempId,
    facts: &ProtoPromotionFacts,
    captured_slots: &BTreeSet<usize>,
) -> bool {
    facts
        .home_slot(temp)
        .is_some_and(|slot| captured_slots.contains(&slot))
}

#[cfg(test)]
mod tests;
