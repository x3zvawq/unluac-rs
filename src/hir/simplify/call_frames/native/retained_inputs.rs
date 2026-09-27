//! 保持完整条件 initializer 留在高槽的原输入根，直到原覆盖或 frame exit。
//!
//! Promotion 提供 canonical 覆盖端点，FrameBuilder 证明整条计划重发原事件，prefix
//! owner 核对未吸收声明的实际源码槽。这里只在一次后缀扫描中连接这些证明，不重建 CFG。
//! 例如 `local n=({make()}) and 7 or 7; local v=poll()+1` 必须同时恢复 poll 的高槽帧；
//! 拆成低槽 callee 声明会在 poll 观察前覆盖表根。未知观察或控制转移拒绝整个依赖事务。
//! FASTCALL 的 fallback callee 写不是所有路径的覆盖，不消费它来关闭待保留根。

use super::*;
use crate::hir::common::HirOperationSources;
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::simplify::root_lifetimes;

pub(super) fn require_suffix_frames(
    proto: &mut HirProto,
    removed: &[bool],
    plans: &[Plan],
    facts: &ProtoPromotionFacts,
    candidates: &mut BTreeMap<usize, prefix::PrefixRequest>,
) -> Result<Option<usize>, usize> {
    let Some(first) = plans
        .iter()
        .filter(|plan| plan.continuing_root.is_some())
        .map(|plan| plan.start)
        .min()
    else {
        return Ok(None);
    };
    let by_sink = plans
        .iter()
        .map(|plan| (plan.sink, plan))
        .collect::<BTreeMap<_, _>>();
    let mut pending = BTreeMap::<HomeSlotKey, TempId>::new();
    let mut active_owner = None;
    let safety = HirExprSafety::for_dialect(DecompileDialect::Luau);
    let closure_writes = closure_initializers(proto, facts);
    visit_scope_mut(&mut proto.body, &mut 0, &mut |index, owner, stmt| {
        if removed[index] {
            return Some(());
        }
        let plan = by_sink.get(&index).copied();
        if pending.is_empty() && plan.is_none_or(|plan| plan.continuing_root.is_none()) {
            return Some(());
        }
        if !pending.is_empty() && active_owner != Some(owner) {
            return None;
        }
        // 先序位置不代表路径；尚有根义务时不跨子域、回边或未知退出。
        if !matches!(
            stmt,
            HirStmt::LocalDecl(_) | HirStmt::Assign(_) | HirStmt::CallStmt(_) | HirStmt::Return(_)
        ) {
            return None;
        }
        if let HirStmt::Return(ret) = stmt {
            facts.native_return_frame(ret)?;
            if plan.is_none() && !ret.values.is_empty() {
                return None;
            }
            pending.clear();
            return Some(());
        }
        if let Some(plan) = plan {
            if plan.only_preserves_call_prefix() {
                let (index, request) = plan.prefix_request();
                candidates.insert(index, request);
            }
            if let Some(result) = plan.continuing_root {
                // 两臂必须共同覆盖同一个旧根；看到单臂 endpoint 不能代表所有路径。
                let mut ended = result
                    .writes
                    .iter()
                    .flatten()
                    .map(|write| facts.conditional_root_ended_by(*write));
                if let Some(Some(root)) = ended.next()
                    && ended.all(|other| other == Some(root))
                    && let Some(home) = facts.trusted_temp_home_slot(root)
                    && pending.get(&home) == Some(&root)
                    && result
                        .writes
                        .iter()
                        .flatten()
                        .all(|write| facts.trusted_temp_home_slot(*write) == Some(home))
                {
                    pending.remove(&home);
                }
                let home = facts.trusted_temp_home_slot(result.input)?;
                // 仍有同槽旧根时需要其独立覆盖证明，不能由新根悄悄替换。
                if pending.insert(home, result.input).is_some() {
                    return None;
                }
                active_owner = Some(owner);
                return Some(());
            }
            if let Some((local, value)) = scalar_local(stmt) {
                let source = match value {
                    HirExpr::Binary(binary) => binary.source_site,
                    HirExpr::Unary(unary) => unary.source_site,
                    HirExpr::Call(call) => call.source_site,
                    _ => return None,
                }?;
                let result = facts.operation_result_temp(source)?;
                if !(plan.result_locals.as_slice() == [local]
                    || plan.assignment_targets.as_slice() == [HirLValue::Local(local)])
                    || facts.promoted_local_for_temp(result) != Some(local)
                {
                    return None;
                }
                close_endpoint(&mut pending, result, facts);
                return Some(());
            }
            if let HirStmt::CallStmt(call_stmt) = stmt {
                let call = &call_stmt.call;
                if call.fastcall.is_none()
                    && let Some(frame) = facts.native_call_frame(call)
                    && let HirExpr::GlobalRef(global) = &call.callee
                    && let HirOperationSources::Single(source) = global.sources
                    && facts.operation_result_temp(source) == Some(frame.callee)
                {
                    close_endpoint(&mut pending, frame.callee, facts);
                }
                return Some(());
            }
            return None;
        }
        let (local, value) = scalar_local(stmt)?;
        let home = facts.trusted_local_home_slot(local)?;
        if !facts
            .complete_local_definition_write_homes(local)
            .iter()
            .copied()
            .eq(std::iter::once(home))
        {
            return None;
        }
        let closure_write = closure_writes.get(&index).copied();
        if closure_write.is_none()
            && (!matches!(
                value,
                HirExpr::Nil
                    | HirExpr::Boolean(_)
                    | HirExpr::Integer(_)
                    | HirExpr::Number(_)
                    | HirExpr::LocalRef(_)
                    | HirExpr::ParamRef(_)
            ) || root_lifetimes::stmt_may_observe_gc_roots(stmt, safety))
        {
            return None;
        }
        if let Some(endpoint) = closure_write {
            close_endpoint(&mut pending, endpoint, facts);
        }
        // 完整 initializer 已证明原写时点；即使最早 endpoint 经其它完整帧退休而失联，
        // 仍可重发这次写。保留过近似义务直到精确 endpoint/exit，不宣称旧根还活着。
        if pending.contains_key(&home) && closure_write.is_none() {
            return None;
        }
        if matches!(stmt, HirStmt::LocalDecl(_)) {
            candidates.insert(
                index,
                prefix::PrefixRequest {
                    home,
                    required: BTreeSet::new(),
                },
            );
        }
        Some(())
    })
    .ok_or(first)?;
    // 到作用域尾还未出现原 frame exit，不猜测隐式的跨域根释放。
    if !pending.is_empty() {
        return Err(first);
    }
    Ok(Some(first))
}

/// 已有独立 Closure 声明也消费原 builder 的创建/捕获/写域证明；不把无捕获外形
/// 当作可跨 GC 观察的特许。这里只索引实际单条 initializer，不为每个 pending 重扫。
fn closure_initializers(proto: &HirProto, facts: &ProtoPromotionFacts) -> BTreeMap<usize, TempId> {
    let restrictions = frame_restrictions(proto, facts);
    let context = NativeFrameContext {
        rk_literals: None,
        expanded_callees: None,
        retired_roots: None,
        proto,
        barred: &restrictions.barred,
        closed: &restrictions.closed,
        callee_aliases: &restrictions.callee_aliases,
        constants_fit_rk: tables::constants_fit_rk(proto),
    };
    let mut flat = Vec::new();
    flatten_scope(&proto.body, &mut 0, &mut flat);
    flat.iter()
        .flatten()
        .filter_map(|entry| {
            let (local, value @ HirExpr::Closure(closure)) = scalar_local(entry.stmt)? else {
                return None;
            };
            let result = facts.operation_result_temp(closure.source_site?)?;
            let home = facts.trusted_temp_home_slot(result)?;
            if !matches!(entry.stmt, HirStmt::LocalDecl(_))
                || facts.promoted_local_for_temp(result) != Some(local)
            {
                return None;
            }
            let run = [entry.stmt];
            let mut builder =
                frame_builder(context, &run, facts, DecompileDialect::Luau, home.slot())?;
            if !builder.homes_match(local, 0, home.slot(), None, Some(result)) {
                return None;
            }
            builder.expr(value, 0, home.slot(), None, false, true, Some(result))?;
            builder.finish_event(0)?;
            Some((entry.id, result))
        })
        .collect()
}

fn close_endpoint(
    pending: &mut BTreeMap<HomeSlotKey, TempId>,
    endpoint: TempId,
    facts: &ProtoPromotionFacts,
) {
    if let Some(root) = facts.conditional_root_ended_by(endpoint)
        && let Some(home) = facts.trusted_temp_home_slot(endpoint)
        && facts.trusted_temp_home_slot(root) == Some(home)
        && pending.get(&home) == Some(&root)
    {
        pending.remove(&home);
    }
}
