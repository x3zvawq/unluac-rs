//! 在资源作用域建立前恢复完整初始化帧。
//!
//! 消费 TBC origin、原 CALL 结果与 HIR 声明配对，保留资源的初始化和激活位置。

use super::*;
use crate::hir::common::HirTbcDeclaration;

pub(in crate::hir::simplify) fn restore(
    proto: &mut HirProto,
    facts: &mut ProtoPromotionFacts,
    dialect: DecompileDialect,
    is_chunk_entry: bool,
) -> bool {
    if !matches!(dialect, DecompileDialect::Lua54 | DecompileDialect::Lua55) {
        return false;
    }
    let mut flat = Vec::new();
    let mut count = 0;
    let mut registrations = BTreeMap::<HomeSlotKey, usize>::new();
    prefix::coordinates::visit(&proto.body, &mut count, &mut |id, kind, stmt| {
        if kind != PointKind::Statement || matches!(stmt, HirStmt::Block(_)) {
            flat.push(None);
            return;
        }
        if let HirStmt::ToBeClosed(tbc) = stmt {
            *registrations.entry(facts.tbc_home(tbc.origin)).or_default() += 1;
        }
        flat.push(Some(FlatStmt { id, stmt }));
    });
    if registrations.is_empty() {
        return false;
    }
    let mut restrictions = frame_restrictions(proto, facts);
    let constants_fit_rk = tables::constants_fit_rk(proto);
    let mut plans = Vec::new();
    let mut start = 0;
    for (index, entry) in flat.iter().enumerate() {
        let Some(entry) = entry else {
            start = index + 1;
            continue;
        };
        if let HirStmt::ToBeClosed(tbc) = entry.stmt {
            if index > start
                && let Some(sink) = flat[index - 1]
                && let Some(HirTbcDeclaration::Local { local, declaration }) =
                    tbc.declaration(sink.stmt)
                && let ([HirExpr::Call(call)], None) = (
                    declaration.values.fixed.as_slice(),
                    &declaration.values.tail,
                )
                && let Some(frame) = facts.native_call_frame(call)
                && facts.trusted_local_home_slot(local) == Some(frame.home)
                && facts.tbc_home(tbc.origin) == frame.home
                && registrations.get(&frame.home) == Some(&1)
                && call.source_site.is_some_and(|source| {
                    source.proto == proto.id
                        && source.instr.0 < tbc.origin.0
                        && facts
                            .operation_result_temp(source)
                            .and_then(|temp| facts.promoted_local_for_temp(temp))
                            == Some(local)
                })
            {
                // 唯一注册点尚未到达；只排除其原 home 的未来激活保护。
                // 其他 home 仍禁止消费，原结果宽度、producer 和完整事件树由 plan 核对。
                restrictions.closed.remove(&frame.home);
                let stmts = flat[start..index]
                    .iter()
                    .map(|entry| entry.unwrap().stmt)
                    .collect::<Vec<_>>();
                let candidate = plan(
                    NativeFrameContext {
                        rk_literals: None,
                        expanded_callees: None,
                        retired_roots: None,
                        proto,
                        barred: &restrictions.barred,
                        closed: &restrictions.closed,
                        callee_aliases: &restrictions.callee_aliases,
                        constants_fit_rk,
                    },
                    &stmts,
                    facts,
                    dialect,
                    stmts.len() - 1,
                    call,
                    CallWidth::Single,
                );
                restrictions.closed.insert(frame.home);
                if let Some(mut plan) = candidate {
                    plan.removed = flat[start + plan.start..index - 1]
                        .iter()
                        .map(|entry| entry.unwrap().id)
                        .collect();
                    plan.start = plan.removed.first().copied().unwrap_or(sink.id);
                    plan.sink = sink.id;
                    plans.push(plan);
                }
            }
            start = index + 1;
        } else if !(matches!(entry.stmt, HirStmt::LocalDecl(_))
            && scalar_binding(entry.stmt).is_some()
            || matches!(scalar_binding(entry.stmt), Some((HirBinding::Temp(_), _))))
            && super::super::super::table_constructors::constructor_write(entry.stmt).is_none()
            && !matches!(entry.stmt, HirStmt::LocalRootRelease(_))
        {
            // 普通 Local 赋值可能更新回边状态；只消费新声明和原 Temp 准备，
            // 不把 repeat 中下一轮仍需读取的旧 binding 写入退休。
            start = index + 1;
        }
    }
    commit_plans(proto, facts, dialect, is_chunk_entry, plans, count)
}
