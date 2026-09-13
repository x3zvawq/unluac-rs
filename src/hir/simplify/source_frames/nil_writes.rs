//! 在原写入位置恢复完整 LOADNIL 批次，不重建旧值或其退出路径。
//!
//! Promotion 保存原指令的有序 canonical 定义组；普通 HIR 完整帧收敛后，只接受仍然
//! 完整、每员单写且无 read/capture 的全 nil 赋值。源槽覆盖是原语句已有的义务，与旧
//! 根来自 CALL、循环 skip 或分支无关；源码前缀证明在原点重发整组物理写，而非猜旧值。
//! 例如 `for i=long_numeric_string(),1 do ... end; if flag then local a,b=nil,nil;
//! observe() end` 中，skip 可留下原字符串；必须原位清空全部原槽，不能在 for/if 前
//! 新建 holder，也不能只保留原 LOADNIL 的一个成员。成功后整组 LocalDecl 进入 AST，
//! 避免普通多目标赋值降低先拆散它，再把无逻辑读的 nil 当作死声明删除。
//! 声明起点不是完整生命周期证明。线性 nil/未读全局读取 run 的后继原帧若重用首槽，
//! 则在同一预览中恢复整个 run 的 do 末端；其它活出值、部分槽退休或未知前缀不借此授权。
//! 后缀也验证原声明、调用与 for 的帧，避免 `do local n=nil; local v=lookup end; f()`
//! 被扩成父块 Local，导致 v 跨过原低槽 f 的 GC 观察继续存活。
//! 候选、读写计数及声明验证均按整棵树批量处理；只在存在候选时复制一次事务预览。

use std::collections::{BTreeMap, BTreeSet};

use crate::decompile::DecompileDialect;
use crate::hir::common::{
    HirBinding, HirBlock, HirExpr, HirInlineRetentionReason, HirLValue, HirLocalDecl, HirProto,
    HirStmt, LocalId, TempId,
};
use crate::hir::promotion::ProtoPromotionFacts;
use crate::hir::simplify::mention::{BindingReadCollector, BindingWriteCollector};
use crate::hir::simplify::walk::for_each_nested_block_mut;
use crate::hir::visit::visit_stmts;

use super::{PrefixRequest, validate_prefixes};

struct NilCandidate {
    temps: Vec<TempId>,
    existing: Option<Vec<LocalId>>,
}

enum NilMaterialization {
    Declare(Vec<LocalId>),
    Existing,
}

pub(in crate::hir::simplify) fn restore_nil_writes(
    proto: &mut HirProto,
    facts: &mut ProtoPromotionFacts,
    dialect: DecompileDialect,
    is_chunk_entry: bool,
) -> bool {
    if !facts.has_nil_writes() {
        return false;
    }
    let mut read = BTreeSet::new();
    let mut writes = BTreeMap::<TempId, usize>::new();
    let mut local_read = BTreeSet::new();
    let mut local_writes = BTreeMap::<LocalId, usize>::new();
    visit_stmts(
        &proto.body.stmts,
        &mut (
            BindingReadCollector(|binding| {
                if let HirBinding::Temp(temp) = binding {
                    read.insert(temp);
                } else if let HirBinding::Local(local) = binding {
                    local_read.insert(local);
                }
            }),
            BindingWriteCollector(|binding| {
                if let HirBinding::Temp(temp) = binding {
                    *writes.entry(temp).or_default() += 1;
                } else if let HirBinding::Local(local) = binding {
                    *local_writes.entry(local).or_default() += 1;
                }
            }),
        ),
    );
    let mut candidates = BTreeMap::new();
    collect_candidates(
        &proto.body,
        facts,
        &read,
        &writes,
        &proto.temp_debug_locals,
        &mut 0,
        &mut candidates,
    );
    let original_local_groups = facts
        .nil_write_groups()
        .filter_map(|temps| {
            let locals = temps
                .iter()
                .map(|temp| facts.promoted_local_for_temp(*temp))
                .collect::<Option<Vec<_>>>()?;
            Some((locals[0], locals))
        })
        .collect::<BTreeMap<_, _>>();
    let mut nil_locals = BTreeSet::new();
    for stmt in &proto.body.stmts {
        crate::hir::visit::visit_stmt_structure(stmt, &mut |stmt| {
            let HirStmt::LocalDecl(decl) = stmt else {
                return;
            };
            let Some(first) = decl.bindings.first() else {
                return;
            };
            if original_local_groups.get(first) != Some(&decl.bindings)
                || decl.values.tail.is_some()
                || decl.values.fixed.len() != decl.bindings.len()
                || !decl
                    .values
                    .fixed
                    .iter()
                    .all(|value| matches!(value, HirExpr::Nil))
            {
                return;
            }
            let Some(base) = facts.trusted_local_home_slot(*first) else {
                return;
            };
            if decl.bindings.iter().enumerate().any(|(offset, local)| {
                local_read.contains(local)
                    || local_writes.get(local) != Some(&1)
                    || facts.trusted_local_home_slot(*local).is_none_or(|home| {
                        home.slot() != base.slot() + offset
                            || !facts
                                .complete_local_definition_write_homes(*local)
                                .iter()
                                .copied()
                                .eq(std::iter::once(home))
                    })
            }) {
                return;
            }
            nil_locals.extend(decl.bindings.iter().copied());
        });
    }
    if candidates.is_empty() && nil_locals.is_empty() {
        return false;
    }

    // 临时事实与语法一起提交：失败时不发布空 LocalId 或 Temp→Local 合并，后层也不会
    // 看见一个尚未占据原物理槽的 binding。只复制这一 proto 的事实，不建立持久第二套分析。
    let mut preview = proto.clone();
    let mut preview_facts = facts.clone();
    let mut replacements = BTreeMap::new();
    for (&index, candidate) in &candidates {
        if let Some(locals) = &candidate.existing {
            for (&temp, &local) in candidate.temps.iter().zip(locals) {
                preview_facts.record_temp_to_local_merge(temp, local);
                preview
                    .inline_dispositions
                    .promote_temp_to_local(temp, local);
                preview
                    .inline_dispositions
                    .preserve_local(local, HirInlineRetentionReason::PhysicalFramePrefix);
            }
            replacements.insert(index, NilMaterialization::Existing);
            continue;
        }
        let temps = &candidate.temps;
        let mut locals = Vec::with_capacity(temps.len());
        for &temp in temps {
            let local = materialized_local(&mut preview, &mut preview_facts, temp);
            locals.push(local);
            nil_locals.insert(local);
        }
        replacements.insert(index, NilMaterialization::Declare(locals));
    }
    let mut count = 0;
    materialize(&mut preview.body, &replacements, &mut count);
    let mut body = std::mem::take(&mut preview.body);
    let scoped = MaterializationScopes {
        proto: &mut preview,
        facts: &mut preview_facts,
        read: &read,
        writes: &writes,
        nil_locals: &nil_locals,
    }
    .block(&mut body);
    preview.body = body;
    if !scoped {
        return false;
    }
    for &local in &nil_locals {
        preview
            .inline_dispositions
            .preserve_local(local, HirInlineRetentionReason::PhysicalFramePrefix);
    }
    let mut requests = BTreeMap::new();
    count = 0;
    for stmt in &preview.body.stmts {
        crate::hir::visit::visit_stmt_structure(stmt, &mut |stmt| {
            let home = match stmt {
                HirStmt::LocalDecl(decl)
                    if decl.bindings.iter().any(|local| nil_locals.contains(local)) =>
                {
                    preview_facts.trusted_local_home_slot(decl.bindings[0])
                }
                _ => statement_frame(stmt, &preview_facts),
            };
            if let Some(home) = home {
                requests.insert(
                    count,
                    PrefixRequest {
                        home,
                        required: BTreeSet::new(),
                    },
                );
            }
            count += 1;
        });
    }
    let Ok(preserved) = validate_prefixes(
        &preview,
        &preview_facts,
        dialect,
        is_chunk_entry,
        &vec![false; count],
        &requests,
        true,
    ) else {
        // 候选拒绝[ProofIncomplete]：不补空槽，也不跨未知声明或控制流猜测源码前缀。
        return false;
    };
    for local in preserved {
        preview
            .inline_dispositions
            .preserve_local(local, HirInlineRetentionReason::PhysicalFramePrefix);
    }
    *proto = preview;
    *facts = preview_facts;
    true
}

fn materialized_local(
    proto: &mut HirProto,
    facts: &mut ProtoPromotionFacts,
    temp: TempId,
) -> LocalId {
    let local = LocalId(proto.local_count);
    proto.local_count += 1;
    proto
        .local_debug_hints
        .push(proto.temp_debug_locals.get(temp.index()).cloned().flatten());
    proto
        .local_debug_scopes
        .push(proto.temp_debug_scopes.get(temp.index()).copied().flatten());
    facts.record_local_home_slot(local, facts.trusted_temp_home_slot(temp).unwrap());
    facts.record_temp_to_local_merge(temp, local);
    proto.inline_dispositions.promote_temp_to_local(temp, local);
    proto
        .inline_dispositions
        .preserve_local(local, HirInlineRetentionReason::PhysicalFramePrefix);
    local
}

fn statement_frame(
    stmt: &HirStmt,
    facts: &ProtoPromotionFacts,
) -> Option<crate::hir::promotion::HomeSlotKey> {
    match stmt {
        HirStmt::LocalDecl(decl) => decl
            .bindings
            .first()
            .and_then(|local| facts.trusted_local_home_slot(*local)),
        HirStmt::NumericFor(for_) => facts
            .numeric_for_body_frame(for_)
            .map(|frame| frame.controls[0]),
        HirStmt::CallStmt(call) => facts.native_call_layout(&call.call).map(|frame| frame.home),
        HirStmt::GenericFor(for_) => facts
            .generic_for_body_frame(for_)
            .and_then(|frame| frame.controls.first().copied()),
        HirStmt::Return(ret) => single_call_frame(&ret.values, facts),
        HirStmt::Assign(assign) => single_call_frame(&assign.values, facts),
        HirStmt::If(if_) => expression_call_frame(&if_.cond, facts),
        HirStmt::While(while_) => expression_call_frame(&while_.cond, facts),
        _ => None,
    }
}

fn single_call_frame(
    values: &crate::hir::common::HirValuePack,
    facts: &ProtoPromotionFacts,
) -> Option<crate::hir::promotion::HomeSlotKey> {
    let value = if values.fixed.is_empty() {
        values.tail.as_ref().map(|tail| tail.as_expr())
    } else if values.fixed.len() == 1 && values.tail.is_none() {
        values.fixed.first()
    } else {
        None
    };
    value.and_then(|value| expression_call_frame(value, facts))
}

fn expression_call_frame(
    value: &HirExpr,
    facts: &ProtoPromotionFacts,
) -> Option<crate::hir::promotion::HomeSlotKey> {
    match value {
        HirExpr::Call(call) => facts.native_call_layout(call).map(|frame| frame.home),
        HirExpr::Unary(unary) if unary.op == crate::hir::common::HirUnaryOpKind::Not => {
            expression_call_frame(&unary.expr, facts)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            // while 的 break 合并可把原条件接成短路链；首项仍无条件先求值，
            // 原 CALL 的入口槽不因后续谓词变化。右项不能证明整条语句的入口。
            expression_call_frame(&logical.lhs, facts)
        }
        HirExpr::Binary(binary) => {
            // 二元运算也先求左操作数；只消费其原调用入口，不跨过左侧去猜右侧帧。
            expression_call_frame(&binary.lhs, facts)
        }
        _ => None,
    }
}

struct MaterializationScopes<'a> {
    proto: &'a mut HirProto,
    facts: &'a mut ProtoPromotionFacts,
    read: &'a BTreeSet<TempId>,
    writes: &'a BTreeMap<TempId, usize>,
    nil_locals: &'a BTreeSet<LocalId>,
}

impl MaterializationScopes<'_> {
    fn block(&mut self, block: &mut HirBlock) -> bool {
        let mut run: Option<(usize, usize, usize)> = None;
        let mut scopes = BTreeMap::new();
        for (index, stmt) in block.stmts.iter_mut().enumerate() {
            if let Some((start, base, next)) = run
                && let Some(frame) = statement_frame(stmt, self.facts)
                && frame.slot() < next
            {
                if frame.slot() != base {
                    return false;
                }
                // 后继原帧重用整段的首槽。这里只包住新 nil 与无 read/capture 的
                // 直接全局读取声明；没有活出区间的 binding，也不提前发出任何清零。
                scopes.insert(start, index);
                run = None;
            }
            if let HirStmt::LocalDecl(decl) = stmt
                && !decl.bindings.is_empty()
                && decl
                    .bindings
                    .iter()
                    .all(|local| self.nil_locals.contains(local))
            {
                let base = self
                    .facts
                    .trusted_local_home_slot(decl.bindings[0])
                    .unwrap()
                    .slot();
                if let Some((start, first, next)) = run {
                    if next != base {
                        return false;
                    }
                    run = Some((start, first, next + decl.bindings.len()));
                } else {
                    run = Some((index, base, base + decl.bindings.len()));
                }
            } else if let Some((start, base, next)) = run {
                if let Some((temp, HirExpr::GlobalRef(_))) = stmt.scalar_temp_assignment()
                    && !self.read.contains(&temp)
                    && self.writes.get(&temp) == Some(&1)
                    && self
                        .proto
                        .temp_debug_locals
                        .get(temp.index())
                        .is_none_or(Option::is_none)
                    && let Some(home) = self.facts.trusted_temp_home_slot(temp)
                    && home.slot() == next
                    && self
                        .facts
                        .complete_temp_definition_write_homes(temp)
                        .iter()
                        .copied()
                        .eq(std::iter::once(home))
                {
                    let local = materialized_local(self.proto, self.facts, temp);
                    let HirStmt::Assign(assign) = stmt else {
                        unreachable!()
                    };
                    *stmt = HirStmt::LocalDecl(Box::new(HirLocalDecl {
                        bindings: vec![local],
                        values: assign.values.clone(),
                        initializer_merge_transaction: None,
                    }));
                    run = Some((start, base, next + 1));
                } else {
                    run = None;
                }
            }
            let mut valid = true;
            for_each_nested_block_mut(stmt, &mut |child| valid &= self.block(child));
            if !valid {
                return false;
            }
        }
        if !scopes.is_empty() {
            let old = std::mem::take(&mut block.stmts);
            let mut remaining = old.into_iter().enumerate().peekable();
            while let Some((index, stmt)) = remaining.next() {
                if let Some(&end) = scopes.get(&index) {
                    let mut stmts = vec![stmt];
                    while remaining.peek().is_some_and(|(index, _)| *index < end) {
                        stmts.push(remaining.next().unwrap().1);
                    }
                    block
                        .stmts
                        .push(HirStmt::Block(Box::new(HirBlock { stmts })));
                } else {
                    block.stmts.push(stmt);
                }
            }
        }
        true
    }
}

fn collect_candidates(
    block: &HirBlock,
    facts: &ProtoPromotionFacts,
    read: &BTreeSet<TempId>,
    writes: &BTreeMap<TempId, usize>,
    debug_hints: &[Option<String>],
    cursor: &mut usize,
    candidates: &mut BTreeMap<usize, NilCandidate>,
) {
    for (index, stmt) in block.stmts.iter().enumerate() {
        if let Some(temps) = original_nil_write(stmt, facts, read, writes) {
            let existing = temps
                .iter()
                .all(|temp| debug_hints.get(temp.index()).is_none_or(Option::is_none))
                .then(|| block.stmts.get(index + 1))
                .flatten()
                .and_then(|next| {
                    crate::hir::simplify::carried_locals::adjacent_nil_initializer_bindings(
                        temps, next, facts,
                    )
                });
            candidates.insert(
                *cursor,
                NilCandidate {
                    temps: temps.to_vec(),
                    existing,
                },
            );
        }
        *cursor += 1;
        crate::hir::visit::for_each_nested_block(stmt, &mut |child| {
            collect_candidates(child, facts, read, writes, debug_hints, cursor, candidates);
        });
    }
}

fn original_nil_write<'a>(
    stmt: &HirStmt,
    facts: &'a ProtoPromotionFacts,
    read: &BTreeSet<TempId>,
    writes: &BTreeMap<TempId, usize>,
) -> Option<&'a [TempId]> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let HirLValue::Temp(first) = assign.targets.first()? else {
        return None;
    };
    let temps = facts.nil_write_temps(*first)?;
    if assign.values.tail.is_some()
        || assign.targets.len() != temps.len()
        || assign.values.fixed.len() != temps.len()
        || !assign
            .values
            .fixed
            .iter()
            .all(|value| matches!(value, HirExpr::Nil))
    {
        return None;
    }
    let base = facts.trusted_temp_home_slot(*first)?.slot();
    for (offset, (&temp, target)) in temps.iter().zip(&assign.targets).enumerate() {
        let home = facts.trusted_temp_home_slot(temp)?;
        let definition_homes = facts.complete_temp_definition_write_homes(temp);
        if *target != HirLValue::Temp(temp)
            || read.contains(&temp)
            || writes.get(&temp) != Some(&1)
            || home.slot() != base + offset
            || definition_homes.len() != 1
            || !definition_homes.contains(&home)
        {
            // 候选拒绝[ProofIncomplete]：不能漏掉原批次成员、捕获、合并身份或隐藏 MOVE 写。
            return None;
        }
    }
    Some(temps)
}

fn materialize(
    block: &mut HirBlock,
    replacements: &BTreeMap<usize, NilMaterialization>,
    cursor: &mut usize,
) {
    let old = std::mem::take(&mut block.stmts);
    for mut stmt in old {
        let replacement = replacements.get(cursor);
        if let Some(NilMaterialization::Declare(locals)) = replacement {
            let HirStmt::Assign(assign) = &stmt else {
                unreachable!("original nil write must remain an assignment");
            };
            stmt = HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: locals.clone(),
                values: assign.values.clone(),
                initializer_merge_transaction: None,
            }));
        }
        *cursor += 1;
        for_each_nested_block_mut(&mut stmt, &mut |child| {
            materialize(child, replacements, cursor)
        });
        if !matches!(replacement, Some(NilMaterialization::Existing)) {
            block.stmts.push(stmt);
        }
    }
}
