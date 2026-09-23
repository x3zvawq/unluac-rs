//! 恢复原 LOADNIL 批次、闭包声明及槽复用所需的词法末端。
//!
//! 消费 Promotion 的原定义组与源码前缀事实，在完整帧收敛后批量预览声明和作用域；
//! 不从 HIR 名字、逻辑死值或单个声明起点猜物理生命周期。
//! 例如 do local v=lookup end; local function f() ... end; f() 中，
//! 原 CLOSURE 复用 v 的槽时，必须同时恢复 do 末端，避免 v 活过 f 内的 GC 观察。

use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet, BinaryHeap};

use crate::decompile::DecompileDialect;
use crate::hir::common::{
    HirAssign, HirBinding, HirBlock, HirCaptureMode, HirExpr, HirInlineRetentionReason, HirLValue,
    HirLocalDecl, HirProto, HirStmt, LocalId, TempId,
};
use crate::hir::promotion::ProtoPromotionFacts;
use crate::hir::simplify::mention::{
    BindingReadCollector, BindingWriteCollector, CaptureCollector,
};
use crate::hir::simplify::walk::for_each_nested_block_mut;
use crate::hir::visit::visit_stmts;

use super::{PrefixRequest, validate_prefixes};

/// 末次完整 CALL 已退休自己的准备声明；此前只持有非资源值的匿名根块声明可原位结束。
/// 不移动其中的计算和原槽覆盖，亦不修改内层调用。新 CALL 仍须从真实形参前缀开始，
/// 不能借值域事实批准任意帧平移，或删除其内部某一次 scratch 写。
pub(in crate::hir::simplify) fn close_gc_inert_terminal_prefix(
    proto: &mut HirProto,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    is_chunk_entry: bool,
) -> bool {
    // 候选拒绝[ProofIncomplete:Lifetime]：PUC/LuaJIT 的回调还可经 debug.setlocal
    // 改写未捕获 local；当前显式写值域只覆盖 Luau 的 lexical/capture 写入入口。
    if dialect != DecompileDialect::Luau {
        return false;
    }
    let mut end = proto.body.stmts.len();
    if matches!(proto.body.stmts.last(), Some(HirStmt::Return(ret))
        if ret.values.is_empty() && ret.pending_cleanup_source.is_none())
    {
        end -= 1;
    }
    let Some(call_index) = end.checked_sub(1) else {
        return false;
    };
    let HirStmt::CallStmt(call) = &proto.body.stmts[call_index] else {
        return false;
    };
    let Some(layout) = facts.native_call_layout(&call.call) else {
        return false;
    };
    if call_index == 0
        || layout.home.slot() != proto.params.len()
        || proto.vararg_param_local.is_some()
    {
        return false;
    }
    let mut locals = BTreeSet::new();
    for stmt in &proto.body.stmts[..call_index] {
        if let HirStmt::LocalDecl(decl) = stmt {
            locals.extend(decl.bindings.iter().copied());
        }
    }
    if locals.is_empty()
        || locals.iter().any(|local| {
            proto
                .local_debug_scopes
                .get(local.index())
                .is_some_and(Option::is_some)
                || proto
                    .local_debug_hints
                    .get(local.index())
                    .is_some_and(Option::is_some)
        })
    {
        return false;
    }
    let mut invalid_control = false;
    let mut temporary_writes = BTreeSet::new();
    for stmt in &proto.body.stmts[..call_index] {
        crate::hir::visit::visit_stmt_structure(stmt, &mut |stmt| {
            invalid_control |= !matches!(
                stmt,
                HirStmt::LocalDecl(_)
                    | HirStmt::Assign(_)
                    | HirStmt::If(_)
                    | HirStmt::CallStmt(_)
                    | HirStmt::Block(_)
            );
        });
        visit_stmts(
            std::slice::from_ref(stmt),
            &mut BindingWriteCollector(|binding| {
                if let HirBinding::Temp(_) = binding {
                    temporary_writes.insert(binding);
                }
            }),
        );
    }
    let mut escapes = false;
    visit_stmts(
        &proto.body.stmts[call_index..],
        &mut BindingReadCollector(|binding| {
            escapes |= matches!(binding, HirBinding::Local(local) if locals.contains(&local))
                || matches!(binding, HirBinding::Temp(_));
        }),
    );
    if invalid_control || escapes {
        return false;
    }
    let inert = super::super::object_flow::gc_inert_bindings(
        proto,
        crate::hir::expr_safety::HirExprSafety::for_dialect(dialect),
    );
    if !temporary_writes.is_subset(&inert)
        || locals
            .iter()
            .any(|local| !inert.contains(&HirBinding::Local(*local)))
    {
        // 候选拒绝[ProofIncomplete:Lifetime]：未知/资源结果或引用捕获仍需要原词法根。
        return false;
    }
    let tail = proto.body.stmts.split_off(call_index);
    let prefix = std::mem::replace(&mut proto.body.stmts, tail);
    proto
        .body
        .stmts
        .insert(0, HirStmt::Block(Box::new(HirBlock { stmts: prefix })));
    let call = &proto.body.stmts[1];
    let mut count = 0;
    let mut requests = BTreeMap::new();
    super::coordinates::visit(&proto.body, &mut count, &mut |index, kind, stmt| {
        if kind == super::coordinates::PointKind::Statement && std::ptr::eq(stmt, call) {
            requests.insert(
                index,
                PrefixRequest {
                    home: layout.home,
                    required: BTreeSet::new(),
                },
            );
        }
    });
    let Ok(preserved) = validate_prefixes(
        proto,
        facts,
        dialect,
        is_chunk_entry,
        &vec![false; count],
        &requests,
        false,
    ) else {
        return false;
    };
    // 此事务只结束词法区间；AST 不能借新的块末端再删除/移动其中的原覆盖写。
    for local in preserved.into_iter().chain(locals) {
        proto
            .inline_dispositions
            .preserve_local(local, HirInlineRetentionReason::PhysicalFramePrefix);
    }
    for binding in temporary_writes {
        let HirBinding::Temp(temp) = binding else {
            unreachable!()
        };
        proto
            .inline_dispositions
            .preserve_temp(temp, HirInlineRetentionReason::PhysicalFramePrefix);
    }
    true
}

struct NilCandidate {
    temps: Vec<TempId>,
    existing: Option<Vec<LocalId>>,
}

enum NilMaterialization {
    Declare(Vec<LocalId>),
    Existing,
}

/// 原完整 nil 组若紧接同一源码声明前缀的全局读取，须等词法末端 owner 审理。
/// 这里只延期删除，不签发永久保留；是否无读/capture、能否恢复原 scope 和整个后缀，
/// 仍由 restore_materializations 判断，Final 对未消费项沿用原死写清理。
pub(in crate::hir::simplify) fn pending_nil_prefix_temps(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
) -> BTreeSet<TempId> {
    fn collect(block: &HirBlock, facts: &ProtoPromotionFacts, pending: &mut BTreeSet<TempId>) {
        for window in block.stmts.windows(2) {
            let Some(temps) = original_nil_write_shape(&window[0], facts) else {
                continue;
            };
            let Some((temp, HirExpr::GlobalRef(global))) = window[1].scalar_temp_assignment()
            else {
                continue;
            };
            let Some(home) = facts.trusted_temp_home_slot(temp) else {
                continue;
            };
            if facts
                .trusted_temp_home_slot(temps[0])
                .is_some_and(|base| home.slot() == base.slot() + temps.len())
                && global
                    .sources
                    .try_for_each_known(|source| {
                        (facts.direct_global_read_home(source) == Some(home)).then_some(())
                    })
                    .is_some()
            {
                pending.extend(temps.iter().copied());
            }
        }
        for stmt in &block.stmts {
            crate::hir::visit::for_each_nested_block(stmt, &mut |child| {
                collect(child, facts, pending)
            });
        }
    }
    let mut pending = BTreeSet::new();
    collect(&proto.body, facts, &mut pending);
    pending
}

pub(in crate::hir::simplify) fn restore_materializations(
    proto: &mut HirProto,
    facts: &mut ProtoPromotionFacts,
    dialect: DecompileDialect,
    is_chunk_entry: bool,
) -> bool {
    if close_inert_carrier_scopes(proto, facts, dialect, is_chunk_entry) {
        return true;
    }
    let mut has_scope_candidate = false;
    for stmt in &proto.body.stmts {
        crate::hir::visit::visit_stmt_structure(stmt, &mut |stmt| {
            has_scope_candidate |= matches!(stmt, HirStmt::Assign(assign)
                if matches!((assign.targets.as_slice(), assign.values.fixed.as_slice(), &assign.values.tail),
                    ([HirLValue::Temp(_) | HirLValue::Local(_)], [HirExpr::GlobalRef(_) | HirExpr::Unary(_)], None)))
                || matches!(stmt, HirStmt::Block(_))
                || matches!(stmt, HirStmt::LocalDecl(decl)
                // 已物化 nil 的最后一次 ByValue capture 也能结束原声明段；
                // CALL 准备被完整内联后，不能再靠剩余 scratch 触发末端恢复。
                if matches!(decl.values.fixed.as_slice(), [HirExpr::Nil | HirExpr::Closure(_)])
                    || decl.bindings.len() > 1 && decl.values.tail.as_ref()
                        .is_some_and(|tail| matches!(tail.as_expr(), HirExpr::Call(_))));
        });
    }
    if !facts.has_nil_writes() && !has_scope_candidate {
        return false;
    }
    // 调用/比较/循环准备和词法末端相互依赖，必须在同一事务中完成。native owner
    // 只交出已消费原槽/事件与 value epoch 的预览；下面重新编号并验证全部源码前缀。
    let mut prepared_facts = facts.clone();
    let mut prepared_proto = proto.clone();
    let restored_targets =
        restore_call_target_declarations(&mut prepared_proto, &mut prepared_facts)
            | (dialect == DecompileDialect::Luau
                && restore_closure_target_declarations(&mut prepared_proto, &mut prepared_facts));
    let mut frames_changed = false;
    if restored_targets {
        // 先退休 CALL 结果的额外声明及其 root-release，再让后继 dispatch 看见新的
        // 原槽定义。两者都留在当前 preview，最后统一核对完整源码前缀。
        let Some((results, changed)) = crate::hir::simplify::call_frames::prepare_source_frames(
            prepared_proto,
            &mut prepared_facts,
            dialect,
        ) else {
            return false;
        };
        prepared_proto = results;
        frames_changed |= changed;
    }
    let Some((prepared, changed)) = crate::hir::simplify::call_frames::prepare_source_frames(
        prepared_proto,
        &mut prepared_facts,
        dialect,
    ) else {
        return false;
    };
    frames_changed |= changed;
    let original_facts = facts;
    let facts = &prepared_facts;
    let mut read = BTreeSet::new();
    let mut writes = BTreeMap::<TempId, usize>::new();
    let mut local_read = BTreeMap::<LocalId, usize>::new();
    let mut local_writes = BTreeMap::<LocalId, usize>::new();
    let mut captures = CaptureCollector::new(HirCaptureMode::ByReference);
    visit_stmts(&prepared.body.stmts, &mut captures);
    visit_stmts(
        &prepared.body.stmts,
        &mut (
            BindingReadCollector(|binding| {
                if let HirBinding::Temp(temp) = binding {
                    read.insert(temp);
                } else if let HirBinding::Local(local) = binding {
                    *local_read.entry(local).or_default() += 1;
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
        &prepared.body,
        facts,
        &read,
        &writes,
        &prepared.temp_debug_locals,
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
    for stmt in &prepared.body.stmts {
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
                local_read.contains_key(local)
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
    if candidates.is_empty() && nil_locals.is_empty() && !has_scope_candidate && !restored_targets {
        return false;
    }

    // 临时事实与语法一起提交：失败时不发布空 LocalId 或 Temp→Local 合并，后层也不会
    // 看见一个尚未占据原物理槽的 binding。只复制这一 proto 的事实，不建立持久第二套分析。
    let mut preview = prepared;
    let mut preview_facts = prepared_facts;
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
    let constants_fit_rk = crate::hir::simplify::call_frames::constants_fit_rk(&preview);
    let mut body = std::mem::take(&mut preview.body);
    let access_order = ScopeAccessOrder::new(&body);
    let mut scopes = MaterializationScopes {
        proto: &mut preview,
        facts: &mut preview_facts,
        read: &read,
        writes: &writes,
        local_read: &local_read,
        local_writes: &local_writes,
        access_order: &access_order,
        captured_locals: &captures.bindings.locals,
        nil_locals: &nil_locals,
        dialect,
        constants_fit_rk,
        closed_run: false,
    };
    let scoped = scopes.block(&mut body, &mut 0);
    let closed_run = scopes.closed_run;
    preview.body = body;
    let merged_nil_scopes =
        merge_adjacent_nil_scopes(&mut preview, &mut preview_facts, &nil_locals);
    if !scoped
        || (candidates.is_empty() && nil_locals.is_empty() && !closed_run && !restored_targets)
    {
        return false;
    }
    for &local in &nil_locals {
        preview
            .inline_dispositions
            .preserve_local(local, HirInlineRetentionReason::PhysicalFramePrefix);
    }
    let mut requests = BTreeMap::new();
    count = 0;
    super::coordinates::visit(&preview.body, &mut count, &mut |index, kind, stmt| {
        if kind == super::coordinates::PointKind::Boundary
            || (kind == super::coordinates::PointKind::Statement
                && matches!(stmt, HirStmt::Repeat(_)))
        {
            return;
        }
        let home = match stmt {
            HirStmt::LocalDecl(decl)
                if decl.bindings.iter().any(|local| nil_locals.contains(local)) =>
            {
                preview_facts.trusted_local_home_slot(decl.bindings[0])
            }
            _ => statement_frame(stmt, &preview_facts, dialect),
        };
        if let Some(home) = home {
            requests.insert(
                index,
                PrefixRequest {
                    home,
                    required: match stmt {
                        HirStmt::Assign(assign) => assign
                            .targets
                            .iter()
                            .filter_map(|target| {
                                if let HirLValue::Local(local) = target {
                                    Some(*local)
                                } else {
                                    None
                                }
                            })
                            .collect(),
                        _ => BTreeSet::new(),
                    },
                },
            );
        }
    });
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
    // 已物化的 LOADNIL 仍可参与前缀验证；成功验证不是一次改写。按实际提交的
    // 事务记账，不能比较含 f64 的整棵树：NaN 会使未修改的克隆也永远不相等。
    let changed = restored_targets
        || frames_changed
        || merged_nil_scopes
        || !replacements.is_empty()
        || closed_run
        || proto.local_count != preview.local_count
        || proto.inline_dispositions != preview.inline_dispositions;
    *proto = preview;
    *original_facts = preview_facts;
    changed
}

/// 合流结果读完后，后继 CALL 可复用其原槽；只结束无资源、且 debug 区间已结束的声明。
/// 原分支、写回和消费条件全部留在块中，不凭常量结果删除显式检查。
fn close_inert_carrier_scopes(
    proto: &mut HirProto,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    is_chunk_entry: bool,
) -> bool {
    // Luau 没有 debug.setlocal；引用捕获的外部写由共享值域分析排除。
    if dialect != DecompileDialect::Luau {
        return false;
    }
    let carriers = (0..proto.temp_count)
        .map(TempId)
        .filter(|&temp| facts.is_phi_carrier_temp(temp))
        .filter_map(|temp| facts.promoted_local_for_temp(temp))
        .collect::<BTreeSet<_>>();
    let mut declarations = Vec::new();
    for (index, stmt) in proto.body.stmts.iter().enumerate() {
        if let HirStmt::LocalDecl(decl) = stmt
            && let [local] = decl.bindings.as_slice()
            && (decl.values.is_empty()
                || matches!(
                    (decl.values.fixed.as_slice(), &decl.values.tail),
                    ([HirExpr::Nil], None)
                ))
            && decl.initializer_merge_transaction.is_none()
            && carriers.contains(local)
        {
            declarations.push((index, *local));
        }
    }
    if declarations.is_empty() {
        return false;
    }
    let mut last_touch = BTreeMap::new();
    let mut declaration_count = vec![0];
    let mut invalid_count = vec![0];
    for (index, stmt) in proto.body.stmts.iter().enumerate() {
        let mut touched = BTreeSet::new();
        visit_stmts(
            std::slice::from_ref(stmt),
            &mut BindingReadCollector(|binding| {
                if let HirBinding::Local(local) = binding {
                    touched.insert(local);
                }
            }),
        );
        visit_stmts(
            std::slice::from_ref(stmt),
            &mut BindingWriteCollector(|binding| {
                if let HirBinding::Local(local) = binding {
                    touched.insert(local);
                }
            }),
        );
        last_touch.extend(touched.into_iter().map(|local| (local, index)));
        declaration_count.push(
            declaration_count.last().unwrap() + usize::from(matches!(stmt, HirStmt::LocalDecl(_))),
        );
        let mut invalid = false;
        crate::hir::visit::visit_stmt_structure(stmt, &mut |stmt| {
            invalid |= !matches!(
                stmt,
                HirStmt::LocalDecl(_)
                    | HirStmt::Assign(_)
                    | HirStmt::If(_)
                    | HirStmt::CallStmt(_)
                    | HirStmt::Block(_)
            );
        });
        invalid_count.push(invalid_count.last().unwrap() + usize::from(invalid));
    }
    let mut windows = BTreeMap::new();
    let mut previous_end = 0;
    for (start, local) in declarations {
        let Some(end) = last_touch.get(&local).map(|last| last + 1) else {
            continue;
        };
        if start < previous_end
            || end <= start + 1
            || declaration_count[end] - declaration_count[start] != 1
            || invalid_count[end] != invalid_count[start]
        {
            continue;
        }
        let call = match proto.body.stmts.get(end) {
            Some(HirStmt::CallStmt(call)) => Some(&call.call),
            Some(HirStmt::LocalDecl(decl)) => match (
                decl.bindings.as_slice(),
                decl.values.fixed.as_slice(),
                &decl.values.tail,
            ) {
                ([_], [HirExpr::Call(call)], None) => Some(call.as_ref()),
                _ => None,
            },
            _ => None,
        };
        let Some(call) = call else {
            continue;
        };
        let Some(layout) = facts.native_call_layout(call) else {
            continue;
        };
        if facts.trusted_local_home_slot(local) != Some(layout.home) {
            continue;
        }
        // 重编译会给原 do 块中的 carrier 记录 nil 初始化及 debug 身份；不能因此
        // 把已经结束的声明延长到整个函数。只有明确的原末端才能关闭有名 local。
        if let Some(scope) = proto.local_debug_scopes[local.index()] {
            if !proto.debug_scopes[scope].is_some_and(|scope| {
                scope
                    .end_instr
                    .zip(call.source_site)
                    .is_some_and(|(end, site)| end.index() <= site.instr.index())
            }) {
                continue;
            }
        } else if proto.local_debug_hints[local.index()].is_some() {
            continue;
        }
        windows.insert(start, (end, local, layout.home));
        previous_end = end;
    }
    if windows.is_empty() {
        return false;
    }
    let inert = super::super::object_flow::gc_inert_bindings(
        proto,
        crate::hir::expr_safety::HirExprSafety::for_dialect(dialect),
    );
    windows.retain(|_, (_, local, _)| inert.contains(&HirBinding::Local(*local)));
    if windows.is_empty() {
        return false;
    }
    let mut preview = proto.clone();
    let mut statements = std::mem::take(&mut preview.body.stmts)
        .into_iter()
        .enumerate();
    let mut requests_at = BTreeMap::new();
    while let Some((index, stmt)) = statements.next() {
        if let Some(&(end, _, home)) = windows.get(&index) {
            let mut stmts = vec![stmt];
            stmts.extend(
                statements
                    .by_ref()
                    .take(end - index - 1)
                    .map(|(_, stmt)| stmt),
            );
            preview
                .body
                .stmts
                .push(HirStmt::Block(Box::new(HirBlock { stmts })));
            requests_at.insert(preview.body.stmts.len(), home);
        } else {
            preview.body.stmts.push(stmt);
        }
    }
    let mut count = 0;
    let mut requests = BTreeMap::new();
    for (index, stmt) in preview.body.stmts.iter().enumerate() {
        if let Some(&home) = requests_at.get(&index) {
            requests.insert(
                count,
                PrefixRequest {
                    home,
                    required: BTreeSet::new(),
                },
            );
        }
        count += 1;
        crate::hir::visit::for_each_nested_block(stmt, &mut |child| {
            super::coordinates::visit(child, &mut count, &mut |_, _, _| {});
        });
        if matches!(stmt, HirStmt::Repeat(_)) {
            count += 1;
        }
    }
    let Ok(preserved) = validate_prefixes(
        &preview,
        facts,
        dialect,
        is_chunk_entry,
        &vec![false; count],
        &requests,
        false,
    ) else {
        return false;
    };
    for local in preserved
        .into_iter()
        .chain(windows.values().map(|&(_, local, _)| local))
    {
        preview
            .inline_dispositions
            .preserve_local(local, HirInlineRetentionReason::PhysicalFramePrefix);
    }
    *proto = preview;
    true
}

/// 帧恢复可能先结束原 nil 的作用域，稍后才把条件准备内联到下一条 if。
/// 再次相邻时，仍按原 LOADNIL 组与精确 home 交接初始化，不留下机械的 nil 小块。
fn merge_adjacent_nil_scopes(
    proto: &mut HirProto,
    facts: &mut ProtoPromotionFacts,
    nil_locals: &BTreeSet<LocalId>,
) -> bool {
    let groups = facts
        .nil_write_groups()
        .filter_map(|temps| {
            let first = facts.promoted_local_for_temp(*temps.first()?)?;
            Some((first, temps.to_vec()))
        })
        .collect::<BTreeMap<_, _>>();
    let mut merges = Vec::new();
    let mut body = std::mem::take(&mut proto.body);
    merge_nil_scope_blocks(&mut body, proto, facts, nil_locals, &groups, &mut merges);
    proto.body = body;
    for &(temp, local) in &merges {
        facts.record_temp_to_local_merge(temp, local);
        proto.inline_dispositions.promote_temp_to_local(temp, local);
        proto
            .inline_dispositions
            .preserve_local(local, HirInlineRetentionReason::PhysicalFramePrefix);
    }
    !merges.is_empty()
}

fn merge_nil_scope_blocks(
    block: &mut HirBlock,
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    nil_locals: &BTreeSet<LocalId>,
    groups: &BTreeMap<LocalId, Vec<TempId>>,
    merges: &mut Vec<(TempId, LocalId)>,
) {
    let mut removed = BTreeSet::new();
    for (index, pair) in block.stmts.windows(2).enumerate() {
        let HirStmt::Block(scope) = &pair[0] else {
            continue;
        };
        let [HirStmt::LocalDecl(decl)] = scope.stmts.as_slice() else {
            continue;
        };
        let Some(temps) = decl.bindings.first().and_then(|first| groups.get(first)) else {
            continue;
        };
        if decl.values.tail.is_some()
            || decl.values.fixed.len() != decl.bindings.len()
            || !decl
                .values
                .fixed
                .iter()
                .all(|value| matches!(value, HirExpr::Nil))
            || decl.bindings.len() != temps.len()
            || decl.bindings.iter().zip(temps).any(|(&local, &temp)| {
                !nil_locals.contains(&local)
                    || facts.promoted_local_for_temp(temp) != Some(local)
                    || proto.local_debug_hints[local.index()].is_some()
                    || proto.local_debug_scopes[local.index()].is_some()
            })
        {
            continue;
        }
        let Some(locals) = crate::hir::simplify::carried_locals::adjacent_nil_initializer_bindings(
            temps,
            &block.stmts[index + 1..],
            facts,
        ) else {
            continue;
        };
        merges.extend(temps.iter().copied().zip(locals));
        removed.insert(index);
    }
    let mut index = 0;
    block.stmts.retain(|_| {
        let keep = !removed.contains(&index);
        index += 1;
        keep
    });
    for stmt in &mut block.stmts {
        for_each_nested_block_mut(stmt, &mut |child| {
            merge_nil_scope_blocks(child, proto, facts, nil_locals, groups, merges);
        });
    }
}

/// 原 nil 初始化与 CALL 后低槽 COPY 共用一个源码身份；高槽结果仍由完整帧消费。
/// 这里只恢复声明归属，不移动 COPY 的运行时写入，失败随外层 preview 一起撤回。
fn restore_call_target_declarations(proto: &mut HirProto, facts: &mut ProtoPromotionFacts) -> bool {
    let mut reads = BTreeSet::new();
    let mut writes = BTreeMap::<TempId, usize>::new();
    visit_stmts(
        &proto.body.stmts,
        &mut (
            BindingReadCollector(|binding| {
                if let HirBinding::Temp(temp) = binding {
                    reads.insert(temp);
                }
            }),
            BindingWriteCollector(|binding| {
                if let HirBinding::Temp(temp) = binding {
                    *writes.entry(temp).or_default() += 1;
                }
            }),
        ),
    );
    let mut body = std::mem::take(&mut proto.body);
    let changed = restore_call_targets_in_block(&mut body, proto, facts, &reads, &writes);
    proto.body = body;
    changed
}

/// CLOSURE 可直接写回已初始化的槽；nil 前缀及相邻 COPY 都保留原写入位置。
/// 恢复声明归属后，scope owner 才能结束快照作用域，而不把返回的闭包一并关入其中。
fn restore_closure_target_declarations(
    proto: &mut HirProto,
    facts: &mut ProtoPromotionFacts,
) -> bool {
    let mut reads = BTreeSet::new();
    let mut writes = BTreeMap::new();
    visit_stmts(
        &proto.body.stmts,
        &mut (
            BindingReadCollector(|binding| {
                reads.insert(binding);
            }),
            BindingWriteCollector(|binding| {
                *writes.entry(binding).or_insert(0usize) += 1;
            }),
        ),
    );
    let nils = facts
        .nil_write_groups()
        .filter_map(|temps| {
            let [temp] = temps else {
                return None;
            };
            let binding = facts
                .promoted_local_for_temp(*temp)
                .map_or(HirBinding::Temp(*temp), HirBinding::Local);
            (!reads.contains(&binding)
                && writes.get(&binding) == Some(&1)
                && proto.temp_debug_locals[temp.index()].is_none()
                && proto.temp_debug_scopes[temp.index()].is_none()
                && !matches!(binding, HirBinding::Local(local)
                if proto.local_debug_hints[local.index()].is_some()
                    || proto.local_debug_scopes[local.index()].is_some()))
            .then_some((binding, *temp))
        })
        .collect::<BTreeMap<_, _>>();
    fn block(
        body: &mut HirBlock,
        proto: &mut HirProto,
        facts: &mut ProtoPromotionFacts,
        nils: &BTreeMap<HirBinding, TempId>,
        reads: &BTreeSet<HirBinding>,
        writes: &BTreeMap<HirBinding, usize>,
    ) -> bool {
        let mut pending = BTreeMap::new();
        let mut plans = Vec::new();
        for (index, stmt) in body.stmts.iter().enumerate() {
            let scalar = match stmt {
                HirStmt::LocalDecl(decl) if decl.initializer_merge_transaction.is_none() => {
                    match (
                        decl.bindings.as_slice(),
                        decl.values.fixed.as_slice(),
                        &decl.values.tail,
                    ) {
                        ([local], [value], None) => Some((HirBinding::Local(*local), value)),
                        _ => None,
                    }
                }
                _ => stmt
                    .scalar_temp_assignment()
                    .map(|(temp, value)| (HirBinding::Temp(temp), value)),
            };
            if let Some((binding, value)) = scalar {
                let home = match binding {
                    HirBinding::Local(local) => facts.trusted_local_home_slot(local),
                    HirBinding::Temp(temp) => facts.trusted_temp_home_slot(temp),
                    _ => None,
                };
                if let Some(home) = home {
                    let previous = pending.remove(&home);
                    if matches!(value, HirExpr::Nil)
                        && let Some(&temp) = nils.get(&binding)
                    {
                        pending.insert(home, (index, temp, false));
                    } else if let HirBinding::Temp(temp) = binding
                        && matches!(value, HirExpr::LocalRef(_) | HirExpr::ParamRef(_))
                        && matches!(stmt, HirStmt::Assign(assign)
                            if !assign.is_phi_transfer
                                && assign.initializer_merge_transaction.is_none()
                                && assign.generic_for_initializer_producer.is_none()
                                && assign.generic_for_dispatch_release.is_none()
                                && assign.method_rewrite_transaction.is_none())
                        && !reads.contains(&binding)
                        && writes.get(&binding) == Some(&1)
                        && proto.temp_debug_locals[temp.index()].is_none()
                        && proto.temp_debug_scopes[temp.index()].is_none()
                        && facts
                            .complete_temp_definition_write_homes(temp)
                            .iter()
                            .copied()
                            .eq([home])
                    {
                        // COPY 可能在闭包分配前清除旧 root，不能按无读删除。
                        // 仅恢复紧邻同 home 的初始化归属，仍由整批源码帧预览核对声明。
                        pending.insert(home, (index, temp, true));
                    } else if let (
                        HirBinding::Local(local),
                        HirExpr::Closure(closure),
                        Some((start, temp, adjacent)),
                    ) = (binding, value, previous)
                        && (!adjacent || start + 1 == index)
                        && !matches!(body.stmts[start].scalar_temp_assignment(),
                            Some((_, HirExpr::LocalRef(source))) if *source == local)
                        && proto.local_debug_hints[local.index()].is_none()
                        && proto.local_debug_scopes[local.index()].is_none()
                        && writes.get(&binding) == Some(&1)
                        && closure
                            .source_site
                            .and_then(|site| facts.operation_result_home(site))
                            == Some(home)
                        && closure_target_writes_remain(
                            local,
                            closure,
                            home,
                            body.stmts.get(index + 1),
                            facts,
                        )
                    {
                        plans.push((start, index, temp, local));
                    }
                    continue;
                }
            }
            // 候选拒绝[ProofIncomplete:ControlFlow]：只在同一连续声明段配对原 nil 与 CLOSURE。
            pending.clear();
        }
        let mut changed = !plans.is_empty();
        for (start, end, temp, local) in plans {
            let values = match &body.stmts[start] {
                HirStmt::LocalDecl(decl) => decl.values.clone(),
                HirStmt::Assign(assign) => assign.values.clone(),
                _ => unreachable!(),
            };
            body.stmts[start] = HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: vec![local],
                values,
                initializer_merge_transaction: None,
            }));
            let HirStmt::LocalDecl(decl) = &body.stmts[end] else {
                unreachable!()
            };
            body.stmts[end] = HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Local(local)],
                values: decl.values.clone(),
                luau_compound_global: false,
                upvalue_write_source: None,
                is_phi_transfer: false,
                parallel_nil_frame: None,
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                generic_for_dispatch_release: None,
                method_rewrite_transaction: None,
            }));
            facts.record_temp_to_local_merge(temp, local);
            proto.inline_dispositions.promote_temp_to_local(temp, local);
            proto
                .inline_dispositions
                .preserve_local(local, HirInlineRetentionReason::PhysicalFramePrefix);
        }
        for stmt in &mut body.stmts {
            for_each_nested_block_mut(stmt, &mut |child| {
                changed |= block(child, proto, facts, nils, reads, writes);
            });
        }
        changed
    }
    let mut body = std::mem::take(&mut proto.body);
    let changed = block(&mut body, proto, facts, &nils, &reads, &writes);
    proto.body = body;
    changed
}

/// 声明归属恢复不退休 CLOSURE 后仍显式存在的 COPY；只承认同一原 Def 的下一次写。
fn closure_target_writes_remain(
    local: LocalId,
    closure: &crate::hir::common::HirClosureExpr,
    home: crate::hir::promotion::HomeSlotKey,
    next: Option<&HirStmt>,
    facts: &ProtoPromotionFacts,
) -> bool {
    let writes = facts.complete_local_definition_write_homes(local);
    if writes.iter().copied().eq([home]) {
        return true;
    }
    let Some(HirStmt::LocalDecl(decl)) = next else {
        return false;
    };
    let ([target], [HirExpr::LocalRef(source)], None) = (
        decl.bindings.as_slice(),
        decl.values.fixed.as_slice(),
        &decl.values.tail,
    ) else {
        return false;
    };
    if *source != local || decl.initializer_merge_transaction.is_some() {
        return false;
    }
    let Some(result) = closure
        .source_site
        .and_then(|site| facts.operation_result_temp(site))
    else {
        return false;
    };
    let Some([copy]) = facts.trusted_immediate_moves(result) else {
        return false;
    };
    facts.promoted_local_for_temp(result) == Some(local)
        && copy.source == Some(result)
        && copy.source_home == home
        && facts.promoted_local_for_temp(copy.target) == Some(*target)
        && facts.trusted_local_home_slot(*target) == Some(copy.target_home)
        && writes
            .iter()
            .all(|write| *write == home || *write == copy.target_home)
}

fn call_target_declarations(
    stmts: &[HirStmt],
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    reads: &BTreeSet<TempId>,
    writes: &BTreeMap<TempId, usize>,
) -> Option<(Vec<TempId>, Vec<LocalId>)> {
    let temps = original_nil_write(stmts.first()?, facts, reads, writes)?;
    if temps.iter().any(|temp| {
        proto.temp_debug_locals[temp.index()].is_some()
            || proto.temp_debug_scopes[temp.index()].is_some()
    }) {
        return None;
    }
    let HirStmt::LocalDecl(results) = stmts.get(1)? else {
        return None;
    };
    let HirStmt::Assign(initializer) = stmts.get(2)? else {
        return None;
    };
    let HirExpr::Call(call) = initializer.values.tail.as_ref()?.as_expr() else {
        return None;
    };
    let writes = facts.native_result_writebacks(call)?;
    if !results.values.is_empty()
        || results.bindings.len() != temps.len()
        || initializer.targets.len() != temps.len()
        || writes.len() != temps.len()
        || !initializer.values.fixed.is_empty()
        || initializer.values.tail.as_ref()?.exact_width() != Some(temps.len())
    {
        return None;
    }
    let positions = temps
        .iter()
        .enumerate()
        .map(|(index, &temp)| (temp, index))
        .collect::<BTreeMap<_, _>>();
    let mut locals = vec![None; temps.len()];
    for (offset, write) in writes.iter().enumerate() {
        let previous = write.previous?;
        let position = *positions.get(&previous)?;
        let HirStmt::LocalDecl(copy) = stmts.get(offset + 3)? else {
            return None;
        };
        let ([target], [HirExpr::LocalRef(source)], None) = (
            copy.bindings.as_slice(),
            copy.values.fixed.as_slice(),
            &copy.values.tail,
        ) else {
            return None;
        };
        if copy.initializer_merge_transaction.is_some()
            || results.bindings[write.result_index] != *source
            || initializer.targets[write.result_index] != HirLValue::Local(*source)
            || facts.promoted_local_for_temp(write.writeback) != Some(*target)
            || facts.trusted_local_home_slot(*target) != Some(write.target_home)
            || facts.trusted_temp_home_slot(previous) != Some(write.target_home)
            || proto.local_debug_hints[target.index()].is_some()
            || proto.local_debug_scopes[target.index()].is_some()
            || locals[position].replace(*target).is_some()
        {
            return None;
        }
    }
    Some((
        temps.to_vec(),
        locals.into_iter().collect::<Option<Vec<_>>>()?,
    ))
}

fn restore_call_targets_in_block(
    block: &mut HirBlock,
    proto: &mut HirProto,
    facts: &mut ProtoPromotionFacts,
    reads: &BTreeSet<TempId>,
    writes: &BTreeMap<TempId, usize>,
) -> bool {
    let mut changed = false;
    let mut index = 0;
    while index < block.stmts.len() {
        if let Some((temps, locals)) =
            call_target_declarations(&block.stmts[index..], proto, facts, reads, writes)
        {
            let HirStmt::Assign(nil) = &block.stmts[index] else {
                unreachable!()
            };
            block.stmts[index] = HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: locals.clone(),
                values: nil.values.clone(),
                initializer_merge_transaction: None,
            }));
            for (temp, local) in temps.into_iter().zip(&locals) {
                facts.record_temp_to_local_merge(temp, *local);
                proto
                    .inline_dispositions
                    .promote_temp_to_local(temp, *local);
                proto
                    .inline_dispositions
                    .preserve_local(*local, HirInlineRetentionReason::PhysicalFramePrefix);
            }
            for stmt in &mut block.stmts[index + 3..index + 3 + locals.len()] {
                let HirStmt::LocalDecl(copy) = stmt else {
                    unreachable!()
                };
                *stmt = HirStmt::Assign(Box::new(HirAssign {
                    luau_compound_global: false,
                    upvalue_write_source: None,
                    is_phi_transfer: false,
                    parallel_nil_frame: None,
                    targets: copy
                        .bindings
                        .iter()
                        .copied()
                        .map(HirLValue::Local)
                        .collect(),
                    values: copy.values.clone(),
                    initializer_merge_transaction: None,
                    generic_for_initializer_producer: None,
                    generic_for_dispatch_release: None,
                    method_rewrite_transaction: None,
                }));
            }
            changed = true;
            index += 3 + locals.len();
        } else {
            for_each_nested_block_mut(&mut block.stmts[index], &mut |child| {
                changed |= restore_call_targets_in_block(child, proto, facts, reads, writes);
            });
            index += 1;
        }
    }
    changed
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
    dialect: DecompileDialect,
) -> Option<crate::hir::promotion::HomeSlotKey> {
    match stmt {
        HirStmt::LocalDecl(decl) => decl
            .bindings
            .first()
            .and_then(|local| facts.trusted_local_home_slot(*local)),
        HirStmt::NumericFor(for_) => facts
            .numeric_for_body_frame(for_)
            .map(|frame| frame.controls[0]),
        HirStmt::CallStmt(call) => facts
            .native_call_layout(&call.call)
            .map(|frame| frame.home)
            .or_else(|| {
                facts
                    .native_fastcall_frame(&call.call)
                    .map(|frame| frame.home)
            }),
        HirStmt::GenericFor(for_) => facts
            .generic_for_body_frame(for_)
            .and_then(|frame| frame.controls.first().copied()),
        HirStmt::Return(ret) => single_value_frame(&ret.values, facts, dialect),
        HirStmt::GlobalDecl(decl) => single_value_frame(&decl.values, facts, dialect),
        HirStmt::Assign(assign) => {
            if let Some(home) = assign.parallel_nil_frame {
                return Some(home);
            }
            if let Some(home) = closure_table_write_frame(assign, facts, dialect) {
                return Some(home);
            }
            if let ([HirLValue::TableAccess(access)], [value], None) = (
                assign.targets.as_slice(),
                assign.values.fixed.as_slice(),
                &assign.values.tail,
            ) && matches!(
                value,
                HirExpr::Nil
                    | HirExpr::Boolean(_)
                    | HirExpr::Integer(_)
                    | HirExpr::Number(_)
                    | HirExpr::String(_)
            ) && let Some(layout) = facts.native_table_write_layout(access)
                && layout.value.is_none()
                && match access.base {
                    HirExpr::LocalRef(local) => facts.trusted_local_home_slot(local),
                    HirExpr::ParamRef(param) => facts.trusted_param_home_slot(param),
                    _ => None,
                } == Some(layout.base)
                && let Some(key) = expression_frame(&access.key, facts, dialect)
                && layout.key == Some(key)
                && layout.base.slot() < key.slot()
            {
                return Some(key);
            }
            if dialect == DecompileDialect::Luau
                && let ([HirLValue::TableAccess(access)], [value], None) = (
                    assign.targets.as_slice(),
                    assign.values.fixed.as_slice(),
                    &assign.values.tail,
                )
                && let Some(home) = facts
                    .luau_literal_table_write_frame(access, value)
                    .or_else(|| facts.luau_allocation_table_write_frame(access, value))
            {
                return Some(home);
            }
            let entry = single_value_frame(&assign.values, facts, dialect)?;
            if let ([HirLValue::Local(local)], [HirExpr::GlobalRef(_)], None) = (
                assign.targets.as_slice(),
                assign.values.fixed.as_slice(),
                &assign.values.tail,
            ) && facts.trusted_local_home_slot(*local) == Some(entry)
                && matches!(
                    dialect,
                    DecompileDialect::Lua51
                        | DecompileDialect::Lua52
                        | DecompileDialect::Lua53
                        | DecompileDialect::Lua54
                        | DecompileDialect::Lua55
                )
            {
                // 原 GETTABLE/GETTABUP 可直接写回已声明 local，不占 freereg；
                // CALL 即使目标相同仍有独立准备区，不能套用这项直接写回许可。
                None
            } else {
                Some(entry)
            }
        }
        HirStmt::If(if_) => expression_frame(&if_.cond, facts, dialect).or_else(|| {
            let input = match if_.cond {
                HirExpr::LocalRef(local) => facts.trusted_local_home_slot(local)?,
                HirExpr::ParamRef(param) => facts.trusted_param_home_slot(param)?,
                _ => return None,
            };
            let then_stmt = if_.then_block.stmts.first()?;
            let else_stmt = if_.else_block.as_ref()?.stmts.first()?;
            if matches!(then_stmt, HirStmt::If(_)) || matches!(else_stmt, HirStmt::If(_)) {
                return None;
            }
            let then_frame = statement_frame(then_stmt, facts, dialect)?;
            let else_frame = statement_frame(else_stmt, facts, dialect)?;
            // 直接低槽检查不占准备区；两臂均从同一原槽开始，才可在分支前结束旧声明。
            (then_frame == else_frame && input.slot() < then_frame.slot()).then_some(then_frame)
        }),
        HirStmt::While(while_) => expression_frame(&while_.cond, facts, dialect),
        HirStmt::Repeat(repeat) => expression_frame(&repeat.cond, facts, dialect),
        _ => None,
    }
}

/// 与赋值 owner 共用入口，包含上值目标在 CLOSURE 前准备的原快照槽。
fn closure_table_write_frame(
    assign: &crate::hir::common::HirAssign,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
) -> Option<crate::hir::promotion::HomeSlotKey> {
    if dialect != DecompileDialect::Luau {
        return None;
    }
    let ([HirLValue::TableAccess(access)], [value @ HirExpr::Closure(_)], None) = (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) else {
        return None;
    };
    facts.luau_allocation_table_write_frame(access, value)
}

fn single_value_frame(
    values: &crate::hir::common::HirValuePack,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
) -> Option<crate::hir::promotion::HomeSlotKey> {
    let value = if values.fixed.is_empty() {
        values.tail.as_ref().map(|tail| tail.as_expr())
    } else if values.fixed.len() == 1 && values.tail.is_none() {
        values.fixed.first()
    } else {
        None
    };
    value.and_then(|value| expression_frame(value, facts, dialect))
}

fn expression_frame(
    value: &HirExpr,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
) -> Option<crate::hir::promotion::HomeSlotKey> {
    match value {
        HirExpr::Call(call) => facts.native_call_layout(call).map(|frame| frame.home),
        HirExpr::GlobalRef(global) => facts.global_read_frame(global, dialect),
        HirExpr::TableAccess(access) => {
            if let Some(home) = facts.upvalue_table_read_frame(access) {
                return Some(home);
            }
            if let Some(home) = facts.table_preparation_frame(access, dialect) {
                return Some(home);
            }
            let layout = facts.native_table_read_layout(access)?;
            let result = facts.table_read_result_home(access)?;
            if layout.key.is_none()
                && matches!(access.key, HirExpr::String(_) | HirExpr::Integer(_))
                && let Some(base) = expression_frame(&access.base, facts, dialect)
                && layout.base == base
                && result == base
            {
                // 连续字段读取复用同一暂存槽；首 GETTABLE 的入口来自原来源，
                // 后续 GETFIELD 原位覆写，不另造永久 base local。
                return Some(base);
            }
            let base = match &access.base {
                HirExpr::LocalRef(local) => facts.trusted_local_home_slot(*local)?,
                HirExpr::ParamRef(param) => facts.trusted_param_home_slot(*param)?,
                _ => return None,
            };
            // 原低槽 base 不另行求值，key 的完整入口与结果都在同一 scratch。
            // 例如 object[global_key] 先观察全局 key，再原位写表读取结果；不同槽的
            // base/key 准备或仅知道最终结果的访问，不能从此处取得整条条件入口。
            let key = expression_frame(&access.key, facts, dialect)?;
            (layout.base == base
                && base.slot() < key.slot()
                && layout.key == Some(key)
                && result == key)
                .then_some(key)
        }
        HirExpr::Unary(unary) if unary.op == crate::hir::common::HirUnaryOpKind::Not => {
            expression_frame(&unary.expr, facts, dialect)
        }
        HirExpr::Unary(unary) => {
            let home = facts.unary_operand_home(unary)?;
            if facts.unary_result_home(unary) != Some(home) {
                return None;
            }
            expression_frame(&unary.expr, facts, dialect)
                .or_else(|| facts.operation_operand_preparation(unary.source_site?, &unary.expr))
                .filter(|entry| *entry == home)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            // while 的 break 合并可把原条件接成短路链；首项仍无条件先求值，
            // 原 CALL 的入口槽不因后续谓词变化。右项不能证明整条语句的入口。
            expression_frame(&logical.lhs, facts, dialect)
        }
        HirExpr::Binary(binary) => {
            if let Some(home) = expression_frame(&binary.lhs, facts, dialect) {
                return Some(home);
            }
            if let Some(source) = binary.source_site
                && let Some(home) = facts.operation_operand_preparation(source, &binary.lhs)
                && if binary.op == crate::hir::common::HirBinaryOpKind::Concat {
                    facts.native_concat_buffer(binary)?.start.index() == home.slot()
                } else {
                    facts.native_binary_layout(binary)?.lhs == Some(home)
                }
            {
                return Some(home);
            }
            if let Some(home) = facts.comparison_preparation_frame(binary) {
                return Some(home);
            }
            // 只有原比较内嵌的字面量才不占准备槽。大数字/字符串即使已经内联为
            // 字面量，也可能有原 LOADK；不能据 HIR 外形跨过它。右侧保留整个外层
            // CALL 的 callee 入口，例如 tonumber(f()) 从 tonumber 而非内层 f 开始。
            if !matches!(
                binary.op,
                crate::hir::common::HirBinaryOpKind::Eq
                    | crate::hir::common::HirBinaryOpKind::Lt
                    | crate::hir::common::HirBinaryOpKind::Le
            ) {
                return None;
            }
            let layout = facts.native_binary_layout(binary)?;
            let home = expression_frame(&binary.rhs, facts, dialect)?;
            if layout.rhs != Some(home) {
                return None;
            }
            let direct = match &binary.lhs {
                HirExpr::LocalRef(local) => facts.trusted_local_home_slot(*local),
                HirExpr::ParamRef(param) => facts.trusted_param_home_slot(*param),
                _ => None,
            };
            if let Some(direct) = direct {
                // 已在源码前缀中的同一低槽直接参与比较，不产生新的 operand scratch。
                // Temp 可能尚待物化，Upvalue 则需要 GETUPVAL；两者不能借这个许可。
                return (layout.lhs == Some(direct) && direct.slot() < home.slot()).then_some(home);
            }
            (layout.lhs.is_none()
                && matches!(
                    binary.lhs,
                    HirExpr::Nil
                        | HirExpr::Boolean(_)
                        | HirExpr::Integer(_)
                        | HirExpr::Number(_)
                        | HirExpr::String(_)
                ))
            .then_some(home)
        }
        _ => None,
    }
}

struct MaterializationScopes<'a> {
    proto: &'a mut HirProto,
    facts: &'a mut ProtoPromotionFacts,
    read: &'a BTreeSet<TempId>,
    writes: &'a BTreeMap<TempId, usize>,
    local_read: &'a BTreeMap<LocalId, usize>,
    local_writes: &'a BTreeMap<LocalId, usize>,
    access_order: &'a ScopeAccessOrder,
    captured_locals: &'a BTreeSet<LocalId>,
    nil_locals: &'a BTreeSet<LocalId>,
    dialect: DecompileDialect,
    constants_fit_rk: bool,
    closed_run: bool,
}

/// 本次预览的 DFS 读写末端；包装作用域只在子树处理完后提交，不重扫嵌套块。
struct ScopeAccessOrder {
    last_touch: BTreeMap<LocalId, usize>,
    subtree_end: Vec<usize>,
}

fn boolean_write_value(mut value: &HirExpr) -> bool {
    if matches!(value, HirExpr::Nil | HirExpr::Boolean(_)) {
        return true;
    }
    let mut has_not = false;
    while let HirExpr::Unary(unary) = value
        && unary.op == crate::hir::common::HirUnaryOpKind::Not
    {
        has_not = true;
        value = &unary.expr;
    }
    has_not
        && matches!(
            value,
            HirExpr::LocalRef(_) | HirExpr::ParamRef(_) | HirExpr::Nil | HirExpr::Boolean(_)
        )
}

impl ScopeAccessOrder {
    fn new(body: &HirBlock) -> Self {
        let mut order = Self {
            last_touch: BTreeMap::new(),
            subtree_end: Vec::new(),
        };
        order.collect(body);
        order
    }

    fn collect(&mut self, block: &HirBlock) {
        for stmt in &block.stmts {
            let index = self.subtree_end.len();
            self.subtree_end.push(0);
            if !matches!(stmt, HirStmt::Repeat(_)) {
                self.header(stmt, index);
            }
            crate::hir::visit::for_each_nested_block(stmt, &mut |child| self.collect(child));
            // until 在 body 后求值；归到子树末端，不能提前结束被它读取的 body local。
            if matches!(stmt, HirStmt::Repeat(_)) {
                self.header(stmt, self.subtree_end.len() - 1);
            }
            self.subtree_end[index] = self.subtree_end.len();
        }
    }

    fn header(&mut self, stmt: &HirStmt, index: usize) {
        crate::hir::visit::visit_stmt_header(
            stmt,
            &mut BindingReadCollector(|binding| {
                if let HirBinding::Local(local) = binding {
                    self.last_touch.insert(local, index);
                }
            }),
        );
        crate::hir::visit::visit_stmt_header(
            stmt,
            &mut BindingWriteCollector(|binding| {
                if let HirBinding::Local(local) = binding {
                    self.last_touch.insert(local, index);
                }
            }),
        );
    }
}

impl MaterializationScopes<'_> {
    /// 未使用的原一元结果仍需占据输出槽，后继 CALL 不能借它无读而左移。
    /// 只接收直接低槽输入；嵌套求值和其它写域继续由完整操作帧 owner 证明。
    fn unused_unary_result(&self, stmt: &HirStmt) -> Option<(HirBinding, usize)> {
        let (binding, unary, home, writes) =
            if let Some((temp, HirExpr::Unary(unary))) = stmt.scalar_temp_assignment() {
                if self.read.contains(&temp) || self.writes.get(&temp) != Some(&1) {
                    return None;
                }
                (
                    HirBinding::Temp(temp),
                    unary,
                    self.facts.trusted_temp_home_slot(temp)?,
                    self.facts.complete_temp_definition_write_homes(temp),
                )
            } else {
                let HirStmt::LocalDecl(decl) = stmt else {
                    return None;
                };
                let ([local], [HirExpr::Unary(unary)], None) = (
                    decl.bindings.as_slice(),
                    decl.values.fixed.as_slice(),
                    &decl.values.tail,
                ) else {
                    return None;
                };
                if decl.initializer_merge_transaction.is_some()
                    || self.local_read.contains_key(local)
                    || self.local_writes.get(local) != Some(&1)
                    || self.captured_locals.contains(local)
                {
                    return None;
                }
                (
                    HirBinding::Local(*local),
                    unary,
                    self.facts.trusted_local_home_slot(*local)?,
                    self.facts.complete_local_definition_write_homes(*local),
                )
            };
        let input = match unary.expr {
            HirExpr::LocalRef(local) => self.facts.trusted_local_home_slot(local)?,
            HirExpr::ParamRef(param) => self.facts.trusted_param_home_slot(param)?,
            _ => return None,
        };
        (input.slot() < home.slot()
            && self.facts.unary_operand_home(unary) == Some(input)
            && self.facts.unary_result_home(unary) == Some(home)
            && writes.iter().copied().eq(std::iter::once(home)))
        .then_some((binding, home.slot()))
    }

    /// PUC 的低槽表写不占当前空闲前缀，且所有操作数的原布局仍一致；元方法
    /// 可以观察旧闭包，因此把原语句留在 run 中，不把关闭作用域当作提前清零。
    fn is_low_table_write(&self, stmt: &HirStmt, floor: usize) -> bool {
        if !self.constants_fit_rk
            || matches!(
                self.dialect,
                DecompileDialect::Luau | DecompileDialect::Luajit
            )
        {
            return false;
        }
        let HirStmt::Assign(assign) = stmt else {
            return false;
        };
        let ([HirLValue::TableAccess(access)], [value], None) = (
            assign.targets.as_slice(),
            assign.values.fixed.as_slice(),
            &assign.values.tail,
        ) else {
            return false;
        };
        let Some(layout) = self.facts.native_table_write_layout(access) else {
            return false;
        };
        let operand = |value: &HirExpr, original: Option<crate::hir::promotion::HomeSlotKey>| {
            let home = match value {
                HirExpr::LocalRef(local) => self.facts.trusted_local_home_slot(*local),
                HirExpr::ParamRef(param) => self.facts.trusted_param_home_slot(*param),
                HirExpr::Nil
                | HirExpr::Boolean(_)
                | HirExpr::Integer(_)
                | HirExpr::Number(_)
                | HirExpr::String(_) => return original.is_none(),
                _ => return false,
            };
            home.is_some_and(|home| home.slot() < floor && Some(home) == original)
        };
        operand(&access.base, Some(layout.base))
            && (operand(&access.key, layout.key)
                || expression_frame(&access.key, self.facts, self.dialect)
                    .is_some_and(|key| key.slot() == floor && layout.key == Some(key)))
            && operand(value, layout.value)
    }

    /// 临时结果写入外部目标后，后继原帧复用其首槽；只结束声明，不合并或重排 COPY。
    fn result_copy_scope(&self, stmts: &[HirStmt], start: usize) -> Option<usize> {
        let HirStmt::LocalDecl(decl) = &stmts[start] else {
            return None;
        };
        let width = decl.bindings.len();
        // 单个 nil 的 GLOBAL 写同样占用一段临时声明；其值不是可收集根，
        // 但该写仍必须在原槽覆盖旧根，不能直接删掉 carrier 的初始化。
        if let ([local], [HirExpr::Nil], None) = (
            decl.bindings.as_slice(),
            decl.values.fixed.as_slice(),
            &decl.values.tail,
        ) {
            let home = self.facts.trusted_local_home_slot(*local)?;
            let HirStmt::Assign(copy) = stmts.get(start + 1)? else {
                return None;
            };
            let ([HirLValue::Global(target)], [HirExpr::LocalRef(source)], None) = (
                copy.targets.as_slice(),
                copy.values.fixed.as_slice(),
                &copy.values.tail,
            ) else {
                return None;
            };
            return (*source == *local
                && self.local_read.get(local) == Some(&1)
                && self.local_writes.get(local) == Some(&1)
                && !self.captured_locals.contains(local)
                && self.facts.global_write_value_home(target, self.dialect) == Some(home)
                && statement_frame(stmts.get(start + 2)?, self.facts, self.dialect)
                    .is_some_and(|next| next.slot() == home.slot()))
            .then_some(start + 2);
        }
        if width < 2 || !decl.values.fixed.is_empty() {
            return None;
        }
        let tail = decl.values.tail.as_ref()?;
        let HirExpr::Call(call) = tail.as_expr() else {
            return None;
        };
        let frame = self.facts.native_call_layout(call)?;
        if tail.exact_width() != Some(width)
            || !matches!(frame.results, Some(crate::transformer::ResultPack::Fixed(pack))
                if pack.start.index() == frame.home.slot() && pack.len == width)
        {
            return None;
        }
        let end = start + width + 1;
        if statement_frame(stmts.get(end)?, self.facts, self.dialect) != Some(frame.home) {
            return None;
        }
        let sources = decl
            .bindings
            .iter()
            .enumerate()
            .map(|(offset, &local)| {
                let home = self.facts.trusted_local_home_slot(local)?;
                // 同一 Local 后续准备可另有低槽 COPY；收尾只消费此 CALL 结果的写域，
                // 不把已经被完整帧接管的其它值版本重新归给当前声明。
                let result = self.facts.fixed_call_result(call, offset)?;
                (home.slot() == frame.home.slot() + offset
                    && self.facts.promoted_local_for_temp(result) == Some(local)
                    && self.local_read.get(&local) == Some(&1)
                    && self.local_writes.get(&local) == Some(&1))
                .then_some((local, (home, result)))
            })
            .collect::<Option<BTreeMap<_, _>>>()?;
        let mut copied = BTreeSet::new();
        for stmt in &stmts[start + 1..end] {
            let HirStmt::Assign(assign) = stmt else {
                return None;
            };
            let ([target], [HirExpr::LocalRef(source)], None) = (
                assign.targets.as_slice(),
                assign.values.fixed.as_slice(),
                &assign.values.tail,
            ) else {
                return None;
            };
            let (home, result) = *sources.get(source)?;
            let target_home = match target {
                HirLValue::Local(target) => Some(self.facts.trusted_local_home_slot(*target)?),
                HirLValue::Global(_) if self.dialect == DecompileDialect::Lua51 => None,
                _ => return None,
            };
            if target_home.is_some_and(|home| home.slot() >= frame.home.slot())
                || !copied.insert(*source)
                || !self
                    .facts
                    .complete_temp_definition_write_homes(result)
                    .iter()
                    .all(|written| *written == home || Some(*written) == target_home)
            {
                // 候选拒绝[ProofIncomplete]：不能丢弃其它物理写、别名读取或部分结果。
                return None;
            }
        }
        Some(end)
    }

    /// 后继声明、调用或词法块从原首槽重新开始时，结束前面的无捕获声明段；不插入清零或移动求值。
    /// 新旧段的全部原帧还须通过事务末尾的 prefix 验证，不能仅凭无后续读取退休 GC 根。
    fn closed_prefix_scopes(&self, block: &HirBlock, mut cursor: usize) -> BTreeMap<usize, usize> {
        let mut scopes = BTreeMap::new();
        let mut starts = BTreeMap::new();
        let mut locals = BTreeSet::new();
        let mut declaration_top = 0;
        let mut blocked = BTreeSet::new();
        let mut pending_accesses = BinaryHeap::<Reverse<(usize, usize)>>::new();
        for (index, stmt) in block.stmts.iter().enumerate() {
            let position = cursor;
            cursor = self.access_order.subtree_end[position];
            while pending_accesses
                .peek()
                .is_some_and(|Reverse((last, _))| *last < position)
            {
                let Reverse((_, declaration)) = pending_accesses.pop().unwrap();
                blocked.remove(&declaration);
            }
            let next_frame = match stmt {
                HirStmt::Block(child) => child.stmts.first(),
                HirStmt::LocalDecl(_) | HirStmt::CallStmt(_) | HirStmt::If(_) => Some(stmt),
                _ => None,
            };
            if let Some(first) = next_frame
                .and_then(|stmt| statement_frame(stmt, self.facts, self.dialect))
                .and_then(|home| starts.get(&home.slot()).copied())
                && blocked.range(first..).next().is_none()
            {
                // 此处证明旧声明段结束、新帧复用物理位置，并不合并新旧 cell。
                // CLOSE 正会改变 epoch；要求相等反而排除了应恢复的词法末端。
                scopes.insert(first, index);
                // 已选窗口保持不重叠；前面的活跃声明留在外围，不把内层末端再次包入旧段。
                starts.clear();
                locals.clear();
                declaration_top = 0;
                blocked.clear();
                pending_accesses.clear();
            }
            match stmt {
                HirStmt::LocalDecl(decl) => {
                    if let Some(home) = statement_frame(stmt, self.facts, self.dialect) {
                        starts.entry(home.slot()).or_insert(index);
                    }
                    locals.extend(decl.bindings.iter().copied());
                    for local in &decl.bindings {
                        if let Some(home) = self.facts.trusted_local_home_slot(*local) {
                            declaration_top = declaration_top.max(home.slot() + 1);
                        }
                    }
                    let mut can_retire = true;
                    let mut last_touch = None;
                    for local in &decl.bindings {
                        can_retire &= !self.captured_locals.contains(local)
                            && (self.local_writes.get(local) == Some(&1)
                            || self.facts.trusted_local_home_slot(*local).is_some_and(|home|
                                self.facts.complete_local_definition_write_homes(*local)
                                    .iter().copied().eq([home])));
                        last_touch = last_touch.max(self.access_order.last_touch.get(local).copied());
                    }
                    if !can_retire {
                        blocked.insert(index);
                    } else if let Some(last) = last_touch.filter(|last| *last >= position) {
                        blocked.insert(index);
                        // 每组声明只进入/退出一次；不为每个调用重扫所有后缀读取。
                        pending_accesses.push(Reverse((last, index)));
                    }
                }
                HirStmt::CallStmt(_) if !starts.is_empty() => {}
                // 子块已负责其捕获 cell 的关闭；外层无捕获 local 可在其中读取。
                // 把这些读取计入整段末端证明，不能因遇到子块而遗失外层 debug 声明。
                HirStmt::Block(_) if !starts.is_empty() => {}
                HirStmt::Assign(assign) if !starts.is_empty()
                    && matches!((assign.targets.as_slice(), assign.values.fixed.as_slice(), &assign.values.tail),
                        ([HirLValue::Local(local)], [value], None)
                            if locals.contains(local) && boolean_write_value(value)) => {}
                // CLOSURE 原位覆盖已声明的低槽目标，不增加局部前缀；ByValue 捕获
                // 的最后一次读取仍由 access_order 计入，ByReference 则继续阻止结束作用域。
                HirStmt::Assign(assign) if !starts.is_empty()
                    && matches!((assign.targets.as_slice(), assign.values.fixed.as_slice(), &assign.values.tail),
                        ([HirLValue::Local(local)], [HirExpr::Closure(closure)], None)
                            if self.facts.trusted_local_home_slot(*local).is_some_and(|home|
                                home.slot() < declaration_top
                                    && closure.source_site.and_then(|site| self.facts.operation_result_home(site)) == Some(home))) => {}
                // debug 表构造器可能仍保留独立字段写；它不另建槽或改变声明段边界。
                HirStmt::Assign(assign) if !assign.targets.is_empty()
                    && assign.targets.iter().all(|target| matches!(target,
                        HirLValue::TableAccess(access)
                            if matches!(access.base, HirExpr::LocalRef(local) if locals.contains(&local)))) => {}
                // 写入外部表不结束声明段：原 RK/低槽操作数布局仍不占额外帧，
                // RHS 对段内对象的读取已进入末端索引；弱表及元方法观察仍留在原位置。
                HirStmt::Assign(_) if !starts.is_empty()
                    && self.is_low_table_write(stmt, declaration_top) => {}
                _ => {
                    starts.clear();
                    locals.clear();
                    declaration_top = 0;
                    blocked.clear();
                    pending_accesses.clear();
                    continue;
                }
            }
        }
        scopes
    }

    fn block(&mut self, block: &mut HirBlock, cursor: &mut usize) -> bool {
        let mut run: Option<(usize, usize, usize)> = None;
        let mut unused_operation: Option<(usize, usize)> = None;
        let mut scopes = self.closed_prefix_scopes(block, *cursor);
        self.closed_run |= !scopes.is_empty();
        for index in 0..block.stmts.len() {
            if let Some(end) = self.result_copy_scope(&block.stmts, index) {
                scopes.insert(index, end);
                self.closed_run = true;
            }
        }
        for (index, window) in block.stmts.windows(3).enumerate() {
            let HirStmt::LocalDecl(decl) = &window[0] else {
                continue;
            };
            let ([local], [HirExpr::Closure(closure)], None) = (
                decl.bindings.as_slice(),
                decl.values.fixed.as_slice(),
                &decl.values.tail,
            ) else {
                continue;
            };
            let exported = !matches!(window[1], HirStmt::CallStmt(_));
            let home = if let HirStmt::CallStmt(call) = &window[1] {
                (call.call.callee == HirExpr::LocalRef(*local)
                    && self.local_read.get(local) == Some(&1))
                .then(|| {
                    self.facts
                        .closure_statement_home(*local, closure, &call.call)
                })
                .flatten()
            } else {
                self.facts.trusted_local_home_slot(*local).filter(|home| {
                    !self.captured_locals.contains(local)
                        && closure
                            .source_site
                            .and_then(|source| self.facts.operation_result_home(source))
                            == Some(*home)
                        && self
                            .facts
                            .complete_local_definition_write_homes(*local)
                            .iter()
                            .copied()
                            .eq(std::iter::once(*home))
                        && matches!(&window[1], HirStmt::Assign(assign)
                            if closure_table_write_frame(assign, self.facts, self.dialect)
                                .is_some_and(|frame| frame.slot() == home.slot() + 1))
                })
            };
            let Some(home) = home else {
                continue;
            };
            if self.local_writes.get(local) != Some(&1) {
                continue;
            }
            let mut end = index + 2;
            while block
                .stmts
                .get(end)
                .is_some_and(|stmt| self.is_low_table_write(stmt, home.slot()))
            {
                end += 1;
            }
            if block
                .stmts
                .get(end)
                .and_then(|stmt| statement_frame(stmt, self.facts, self.dialect))
                != Some(home)
            {
                continue;
            }
            if exported {
                let mut reads = 0;
                visit_stmts(
                    &block.stmts[index..end],
                    &mut BindingReadCollector(|binding| {
                        reads += usize::from(binding == HirBinding::Local(*local));
                    }),
                );
                if self.local_read.get(local).copied().unwrap_or(0) != reads {
                    // 候选拒绝[SemanticBarrier:Scope]：引用捕获或窗口外读取仍需要旧 binding。
                    continue;
                }
                // ByValue 导出的闭包值独立于本地声明；新帧在同一槽覆盖旧根时，可结束
                // 单写 CLOSURE 的词法域。整批 prefix 仍验证新帧全部准备与后继声明。
            }
            scopes.insert(index, end);
            self.closed_run = true;
        }
        for (index, stmt) in block.stmts.iter_mut().enumerate() {
            *cursor += 1;
            if let Some((start, slot)) = unused_operation {
                if statement_frame(stmt, self.facts, self.dialect)
                    .or_else(|| {
                        let HirStmt::CallStmt(call) = stmt else {
                            return None;
                        };
                        self.facts
                            .native_fastcall_frame(&call.call)
                            .map(|frame| frame.home)
                    })
                    .is_some_and(|home| home.slot() == slot)
                {
                    // 中间调用仍在结果上方准备；后继帧从结果槽开始时，原位结束
                    // 这个无读、无捕获声明，不让它抬高已复用该槽的后续调用。
                    scopes.insert(start, index);
                    self.closed_run = true;
                    unused_operation = None;
                } else if !matches!(stmt, HirStmt::CallStmt(_)) {
                    unused_operation = None;
                }
            }
            if let Some((binding, slot)) = self.unused_unary_result(stmt) {
                unused_operation = Some((index, slot));
                // locals 已物化的同一结果仍有原槽末端；不因 pass 顺序不同遗失退休点。
                if let HirBinding::Temp(temp) = binding {
                    let local = materialized_local(self.proto, self.facts, temp);
                    let HirStmt::Assign(assign) = stmt else {
                        unreachable!()
                    };
                    *stmt = HirStmt::LocalDecl(Box::new(HirLocalDecl {
                        bindings: vec![local],
                        values: assign.values.clone(),
                        initializer_merge_transaction: None,
                    }));
                    self.closed_run = true;
                }
            }
            if let Some((start, base, next)) = run
                && let Some(frame) = statement_frame(stmt, self.facts, self.dialect)
                && frame.slot() < next
            {
                if frame.slot() != base {
                    return false;
                }
                // 后继原帧重用整段的首槽。这里只包住新 nil 与无 read/capture 的
                // 直接全局读取声明；没有活出区间的 binding，也不提前发出任何清零。
                scopes.insert(start, index);
                self.closed_run = true;
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
            } else {
                if let Some((temp, HirExpr::GlobalRef(global))) = stmt.scalar_temp_assignment()
                    && !self.read.contains(&temp)
                    && self.writes.get(&temp) == Some(&1)
                    && self
                        .proto
                        .temp_debug_locals
                        .get(temp.index())
                        .is_none_or(Option::is_none)
                    && let Some(home) = self.facts.trusted_temp_home_slot(temp)
                    && self.facts.global_read_frame(global, self.dialect) == Some(home)
                    && run.is_none_or(|(_, _, next)| home.slot() == next)
                    && self
                        .facts
                        .complete_temp_definition_write_homes(temp)
                        .iter()
                        .copied()
                        .eq(std::iter::once(home))
                {
                    let (start, base, next) = run.unwrap_or((index, home.slot(), home.slot()));
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
            for_each_nested_block_mut(stmt, &mut |child| valid &= self.block(child, cursor));
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
                .then(|| block.stmts.get(index + 1..))
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
    let temps = original_nil_write_shape(stmt, facts)?;
    temps
        .iter()
        .all(|temp| !read.contains(temp) && writes.get(temp) == Some(&1))
        .then_some(temps)
}

fn original_nil_write_shape<'a>(
    stmt: &HirStmt,
    facts: &'a ProtoPromotionFacts,
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
