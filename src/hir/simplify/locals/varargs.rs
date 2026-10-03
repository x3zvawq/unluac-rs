//! 恢复固定变参包的声明和整包重赋值。
//! 消费原 COPY 事务，验证当前读写与源码前缀后一次提交，不逐个合并跨槽身份。

use super::*;
use crate::hir::common::HirInlineRetentionReason;
use crate::hir::simplify::mention::{BindingReadCollector, BindingWriteCollector};
use crate::hir::simplify::source_frames::{PrefixRequest, coordinates, validate_prefixes};
use crate::hir::visit::visit_stmt_header;

/// 固定 VARARG 原结果留在声明区，高槽 COPY 是后续准备；保留全部写域供消费者验证。
pub(super) fn has_upward_preparation_copies(
    facts: &ProtoPromotionFacts,
    temp: TempId,
    home: HomeSlotKey,
    end: usize,
) -> bool {
    facts
        .complete_temp_non_move_write_homes(temp)
        .iter()
        .copied()
        .eq([home])
        && facts.trusted_immediate_moves(temp).is_some_and(|copies| {
            !copies.is_empty()
                && copies.iter().all(|copy| {
                    copy.source == Some(temp)
                        && copy.source_home == home
                        && copy.target_home.slot() >= end
                })
        })
}

#[derive(Default)]
struct Touches {
    reads: Vec<usize>,
    writes: Vec<usize>,
}

pub(super) fn restore(
    proto: &mut HirProto,
    facts: &mut ProtoPromotionFacts,
    dialect: crate::decompile::DecompileDialect,
    is_chunk_entry: bool,
    sensitive: &BTreeSet<TempId>,
) -> bool {
    let mut points = Vec::new();
    let mut count = 0;
    coordinates::visit(&proto.body, &mut count, &mut |index, kind, stmt| {
        points.push((index, kind, stmt));
    });
    let candidates = points
        .windows(2)
        .filter_map(|pair| {
            let [
                (index, coordinates::PointKind::Statement, HirStmt::Assign(first)),
                (next, coordinates::PointKind::Statement, HirStmt::Assign(second)),
            ] = pair
            else {
                return None;
            };
            if *next != index + 1
                || !direct_fixed_initializer(first)
                || !direct_fixed_initializer(second)
                || !fixed_vararg_initializer(first)
                || !fixed_vararg_initializer(second)
            {
                return None;
            }
            let HirLValue::Temp(result) = *second.targets.first()? else {
                return None;
            };
            let frame = facts.vararg_copy_frame(result)?;
            (first
                .targets
                .iter()
                .cloned()
                .eq(frame.initial.iter().copied().map(HirLValue::Temp))
                && second.targets.iter().cloned().eq(frame
                    .results
                    .iter()
                    .copied()
                    .map(HirLValue::Temp)))
            .then_some((*index, frame.clone()))
        })
        .collect::<Vec<_>>();
    if candidates.is_empty() {
        return false;
    }
    if points
        .iter()
        .any(|(_, _, stmt)| matches!(stmt, HirStmt::Label(_) | HirStmt::Goto(_)))
    {
        // 候选拒绝[ProofIncomplete:Scope]：线性定义不能证明跳入声明中部时的绑定可见性。
        return false;
    }
    let mut touches = BTreeMap::<TempId, Touches>::new();
    let mut statements = BTreeMap::new();
    for &(index, kind, stmt) in &points {
        if kind == coordinates::PointKind::Boundary {
            continue;
        }
        statements.insert(index, stmt);
        visit_stmt_header(
            stmt,
            &mut BindingReadCollector(|binding| {
                if let HirBinding::Temp(temp) = binding {
                    touches.entry(temp).or_default().reads.push(index);
                }
            }),
        );
        visit_stmt_header(
            stmt,
            &mut BindingWriteCollector(|binding| {
                if let HirBinding::Temp(temp) = binding {
                    touches.entry(temp).or_default().writes.push(index);
                }
            }),
        );
    }
    let ends = coordinates::owner_ends(&proto.body, count);
    let mut preview = proto.clone();
    let mut owners = vec![0; count];
    coordinates::visit_mut(&mut preview.body, &mut 0, &mut |index, owner, _| {
        owners[index] = owner;
        Some(())
    });
    let mut preview_facts = facts.clone();
    let mut removed = vec![false; count];
    let mut declarations = BTreeMap::new();
    let mut mapping = BTreeMap::new();
    let mut requests = BTreeMap::new();
    for (index, frame) in candidates {
        let end = ends[owners[index]];
        let valid = frame
            .initial
            .iter()
            .chain(&frame.results)
            .chain(frame.writes.iter().map(|write| &write.target))
            .all(|temp| {
                !sensitive.contains(temp)
                    && !mapping.contains_key(temp)
                    && proto
                        .temp_debug_locals
                        .get(temp.index())
                        .is_none_or(Option::is_none)
                    && proto
                        .temp_debug_scopes
                        .get(temp.index())
                        .is_none_or(Option::is_none)
                    && touches.get(temp).is_none_or(|touch| {
                        touch
                            .reads
                            .iter()
                            .chain(&touch.writes)
                            .all(|at| *at >= index && *at < end)
                    })
            });
        if !valid {
            // 候选拒绝[ProofIncomplete:Lifetime]：debug/capture 或词法范围外的身份尚无整包证明。
            continue;
        }
        let mut copies = Vec::new();
        let mut valid = true;
        for (offset, write) in frame.writes.iter().enumerate() {
            let seed = touches.get(&frame.initial[offset]);
            let result = touches.get(&frame.results[offset]);
            valid &= seed.is_some_and(|touch| touch.reads.is_empty() && touch.writes == [index])
                && result.is_some_and(|touch| touch.writes == [index + 1]);
            if let Some(touch) = touches.get(&write.target) {
                // 已折叠 COPY 可以完全消失；仍存在时必须完整匹配原 target/source，
                // 不能把它在其它位置的写入也重定向到新 local。
                if let [at] = touch.writes.as_slice()
                    && *at > index + 1
                    && statements.get(at).is_some_and(|stmt| {
                        stmt.scalar_temp_assignment()
                            == Some((write.target, &HirExpr::TempRef(write.source)))
                    })
                {
                    copies.push(*at);
                } else if !touch.writes.is_empty() || !touch.reads.is_empty() {
                    valid = false;
                }
            }
        }
        copies.sort_unstable();
        valid &= copies
            .iter()
            .enumerate()
            .all(|(offset, at)| *at == index + 2 + offset);
        if !valid {
            // 候选拒绝[ProofIncomplete:Protocol]：多写、缺失定义或夹杂其它操作不能局部消费 COPY。
            continue;
        }
        let mut locals = Vec::with_capacity(frame.initial.len());
        for (offset, write) in frame.writes.iter().enumerate() {
            let local = LocalId(preview.local_count);
            preview.local_count += 1;
            preview.local_debug_hints.push(None);
            preview.local_debug_scopes.push(None);
            preview_facts.record_local_home_slot(local, write.home);
            for temp in [frame.initial[offset], frame.results[offset], write.target] {
                mapping.insert(temp, local);
                preview_facts.record_temp_local_binding(temp, local);
                let homes = facts
                    .complete_temp_definition_write_homes(temp)
                    .into_owned();
                preview_facts.merge_local_definition_write_homes(local, homes);
                preview
                    .inline_dispositions
                    .promote_temp_to_local(temp, local);
            }
            preview
                .inline_dispositions
                .preserve_local(local, HirInlineRetentionReason::PhysicalFramePrefix);
            locals.push(local);
        }
        requests.insert(
            index,
            PrefixRequest {
                home: frame.writes[0].home,
                required: BTreeSet::new(),
            },
        );
        requests.insert(
            index + 1,
            PrefixRequest {
                home: frame.scratch,
                required: locals.iter().copied().collect(),
            },
        );
        declarations.insert(index, locals);
        for at in copies {
            removed[at] = true;
        }
    }
    if declarations.is_empty() {
        return false;
    }
    rewrite::bindings(&mut preview, &mapping);
    coordinates::visit_mut(&mut preview.body, &mut 0, &mut |index, _, stmt| {
        if let Some(bindings) = declarations.remove(&index) {
            let HirStmt::Assign(assign) = stmt else {
                unreachable!()
            };
            *stmt = HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings,
                values: assign.values.clone(),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
            }));
        }
        Some(())
    });
    let Ok(preserved) = validate_prefixes(
        &preview,
        &preview_facts,
        dialect,
        is_chunk_entry,
        &removed,
        &requests,
        true,
    ) else {
        // 候选拒绝[ProofIncomplete:PhysicalFrame]：新增低槽声明必须与整个后缀的原帧共存。
        return false;
    };
    for local in preserved {
        preview
            .inline_dispositions
            .preserve_local(local, HirInlineRetentionReason::PhysicalFramePrefix);
    }
    coordinates::compact(&mut preview.body, &removed, &mut 0);
    preview_facts.rewrite_copy_assignment_bindings(|binding| match binding {
        HirBinding::Temp(temp) => mapping
            .get(&temp)
            .copied()
            .map(HirBinding::Local)
            .unwrap_or(binding),
        _ => binding,
    });
    // 原子提交：原两次 VARARG、完整宽度及低槽写回一同恢复，scratch 写事实继续保留。
    *proto = preview;
    *facts = preview_facts;
    true
}
