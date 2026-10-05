//! 恢复捕获表追加与 cell 交接组成的固定返回实参。
//! 候选按返回值建立索引，原 table/COPY/参数 Def 与事件顺序由同一调用帧消费。

use super::*;
use crate::hir::common::{HirBinaryOpKind, HirOperationSources, HirSourceSite, HirUnaryOpKind};

pub(in crate::hir::simplify::call_frames) struct Frames<'a> {
    indexed: BTreeMap<crate::LuaString, Option<(&'a Callee, &'a crate::LuaString)>>,
    appends: BTreeSet<(LocalId, crate::LuaString)>,
}

pub(super) fn frames<'a>(
    callees: &'a Callees,
    templates: &'a [Option<(crate::LuaString, crate::LuaString)>],
) -> Frames<'a> {
    let mut indexed = BTreeMap::new();
    let mut appends = BTreeSet::new();
    for callee in callees.values() {
        if let HirLuauInliningBody::CapturedAppendTransfer { template } = callee.body
            && let Some((label, result)) = &templates[template]
        {
            appends.insert((callee.capture_locals[0], label.clone()));
            indexed
                .entry(result.clone())
                .and_modify(|entry| *entry = None)
                .or_insert(Some((callee, label)));
        }
    }
    Frames { indexed, appends }
}

pub(super) fn is_append(context: NativeFrameContext<'_>, stmt: &HirStmt) -> bool {
    let Some(frames) = context.captured_transfers else {
        return false;
    };
    let Some((access, label)) = append(stmt) else {
        return false;
    };
    let HirExpr::LocalRef(base) = access.base else {
        return false;
    };
    frames.appends.contains(&(base, label.clone()))
}

fn append(stmt: &HirStmt) -> Option<(&crate::hir::HirTableAccess, &crate::LuaString)> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let ([HirLValue::TableAccess(access)], [HirExpr::String(label)], None) = (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) else {
        return None;
    };
    Some((access, label))
}

/// 调用签证绑定最后的字面量写；前两条已配对副作用必须随同一计划重放。
pub(super) fn replayed(
    proto: &HirProto,
    roots: &[usize],
    plan: &Plan,
    sites: &BTreeSet<HirSourceSite>,
) -> Vec<usize> {
    let mut output = Vec::new();
    for &index in &plan.removed {
        let Ok(root) = roots.binary_search(&index) else {
            continue;
        };
        let Some((access, _)) = append(&proto.body.stmts[root]) else {
            continue;
        };
        let HirOperationSources::Single(site) = access.sources else {
            continue;
        };
        let result = HirSourceSite {
            instr: crate::transformer::InstrRef(site.instr.index() + 2),
            ..site
        };
        if sites.contains(&result) && plan.removed.binary_search(&roots[root + 1]).is_ok() {
            output.extend([index, roots[root + 1]]);
        }
    }
    output
}

impl FrameBuilder<'_> {
    pub(in crate::hir::simplify::call_frames) fn expanded_captured_transfer_argument(
        &mut self,
        call: &HirCallExpr,
        argument: usize,
        before: usize,
        slot: usize,
    ) -> Option<HirExpr> {
        let context = self.native?;
        let frames = context.captured_transfers?;
        let HirExpr::LocalRef(result) = *call.args.fixed.get(argument)? else {
            return None;
        };
        let end = self.definition(result, before)?;
        let (_, HirExpr::String(returned)) = scalar_local(self.run[end])? else {
            return None;
        };
        let &(callee, label) = frames.indexed.get(returned)?.as_ref()?;
        let [trace, target, source] = callee.capture_locals.as_slice() else {
            return None;
        };
        let start = end.checked_sub(2)?;
        let (access, actual_label) = append(self.run[start])?;
        let HirExpr::Binary(key) = &access.key else {
            return None;
        };
        let HirExpr::Unary(length) = &key.lhs else {
            return None;
        };
        let HirOperationSources::Single(write) = access.sources else {
            return None;
        };
        let site = HirSourceSite {
            instr: crate::transformer::InstrRef(write.instr.index() + 2),
            ..write
        };
        let transfer_site = HirSourceSite {
            instr: crate::transformer::InstrRef(write.instr.index() + 1),
            ..write
        };
        let copy = self.facts.captured_copy_binding(transfer_site)?;
        let layout = self.facts.native_table_write_layout(access)?;
        let binary = self.facts.native_binary_layout(key)?;
        let trace_home = self.facts.trusted_local_home_slot(*trace)?;
        let source_home = self.facts.trusted_local_home_slot(*source)?;
        let target_home = self.facts.trusted_local_home_slot(*target)?;
        let producer = self.facts.call_argument_value(call, argument)?;
        let literal_site = HirSourceSite {
            instr: crate::transformer::InstrRef(write.instr.index().checked_sub(1)?),
            ..write
        };
        let literal = self
            .facts
            .table_write_value_preparation(access, &HirExpr::String(label.clone()))?;
        // 候选拒绝[ProofIncomplete:Identity]：完整捕获、各原 Def 和相邻副作用必须一致；
        // 不能仅凭相同标签及槽号把未知 cell 写换成闭包调用。
        if self.dialect != DecompileDialect::Luau
            || start < self.next_event
            || actual_label != label
            || access.base != HirExpr::LocalRef(*trace)
            || key.op != HirBinaryOpKind::Add
            || crate::hir::luau_inlining::small_integer(&key.rhs) != Some(1)
            || length.op != HirUnaryOpKind::Length
            || length.expr != HirExpr::LocalRef(*trace)
            || scalar_local(self.run[start + 1]) != Some((*target, &HirExpr::LocalRef(*source)))
            || copy.source != HirBinding::Local(*source)
            || copy.target != HirBinding::Local(*target)
            || copy.source_home != source_home
            || copy.target_home != target_home
            || [trace_home, source_home, target_home]
                .iter()
                .any(|home| home.slot() >= self.base)
            || self.facts.trusted_local_home_slot(callee.local)?.slot() >= self.base
            || callee.creation.proto != site.proto
            || callee.creation.instr.index() >= length.source_site?.instr.index()
            || length.source_site?.instr.index() + 1 != key.source_site?.instr.index()
            || key.source_site?.instr.index() + 2 != write.instr.index()
            || self.facts.unary_operand_home(length) != Some(trace_home)
            || self.facts.unary_result_home(length) != Some(HomeSlotKey::new(slot + 2, 0))
            || self.facts.operation_result_home(key.source_site?)
                != Some(HomeSlotKey::new(slot + 1, 0))
            || binary.lhs != Some(HomeSlotKey::new(slot + 2, 0))
            || binary.rhs.is_some()
            || self.facts.operation_result_temp(literal_site) != Some(literal.0)
            || literal.1 != HomeSlotKey::new(slot + 2, 0)
            || layout.base != trace_home
            || layout.key != Some(HomeSlotKey::new(slot + 1, 0))
            || layout.value != Some(HomeSlotKey::new(slot + 2, 0))
            || self.facts.operation_result_temp(site) != Some(producer)
            || self.facts.operation_result_home(site) != Some(HomeSlotKey::new(slot, 0))
            || !self.homes_match(result, end, slot, None, Some(producer))
            || context.proto.local_debug_hints[result.index()].is_some()
            || context.proto.local_debug_scopes[result.index()].is_some()
            || (slot..slot + 3).any(|slot| {
                context.closed.contains(&HomeSlotKey::new(slot, 0))
                    || context.barred.contains(&HomeSlotKey::new(slot, 0))
            })
            || call.source_site?.instr.index() != site.instr.index() + 1
        {
            return None;
        }
        let cursor = (self.first_event, self.next_event);
        for event in start..=end {
            if self.finish_event(event).is_none() {
                (self.first_event, self.next_event) = cursor;
                return None;
            }
        }
        Some(factories::factory_call(
            callee.local,
            Some(site),
            HirValuePack::default(),
        ))
    }
}
