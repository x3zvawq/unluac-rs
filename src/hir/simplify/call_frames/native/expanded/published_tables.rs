//! 配对先发布再返回新表的 Luau 内联体。
//!
//! 分配、捕获表写入与低槽 COPY 必须属于同一原值版本；外层调用帧消费全部事件，
//! Generate 再核对现存工厂必定内联，不能用普通 CALL 改变高槽根的存活时间。

use super::*;
use crate::hir::common::{HirOperationSources, HirTableAccess, UpvalueId};

fn publication(stmt: &HirStmt) -> Option<(&HirTableAccess, LocalId)> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let ([HirLValue::TableAccess(access)], [HirExpr::LocalRef(value)], None) = (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) else {
        return None;
    };
    Some((access, *value))
}

pub(in crate::hir::simplify::call_frames::native) fn is_publication(
    context: NativeFrameContext<'_>,
    stmt: &HirStmt,
) -> bool {
    let Some(callees) = context.expanded_callees else {
        return false;
    };
    let Some((access, _)) = publication(stmt) else {
        return false;
    };
    let HirExpr::Integer(key) = access.key else {
        return false;
    };
    callees
        .get(&(
            HirLuauInliningBody::PublishedTableFactory { key },
            "".into(),
        ))
        .and_then(|callee| callee.capture)
        .is_some_and(|capture| access.base == HirExpr::LocalRef(capture))
}

fn empty_table(table: &HirTableConstructor) -> bool {
    table.fields.is_empty()
        && table.trailing_multivalue.is_none()
        && table.implicit_template_fields.is_empty()
        && matches!(&table.allocation, HirTableAllocation::Luau(size)
            if size.array_capacity == 0 && size.hash_capacity == 0)
}

pub(super) fn body_key(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
) -> Option<(HirLuauInliningBody, crate::LuaString)> {
    if proto.signature.is_vararg
        || !proto.params.is_empty()
        || proto.upvalues.len() != 1
        || !proto.children.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    let [
        initial @ HirStmt::LocalDecl(_),
        install,
        HirStmt::Return(ret),
    ] = proto.body.stmts.as_slice()
    else {
        return None;
    };
    let (object, HirExpr::TableConstructor(table)) = scalar_local(initial)? else {
        return None;
    };
    let (access, value) = publication(install)?;
    let HirExpr::Integer(key) = access.key else {
        return None;
    };
    let HirOperationSources::Single(allocation) = table.sources else {
        return None;
    };
    let HirOperationSources::Single(write) = access.sources else {
        return None;
    };
    let layout = facts.native_table_write_layout(access)?;
    if !(1..=256).contains(&key)
        || !empty_table(table)
        || value != object
        || access.base != HirExpr::UpvalueRef(UpvalueId(0))
        || allocation.instr.index() != 0
        || write.instr.index() != 2
        || facts.allocation_result_home(table) != Some(HomeSlotKey::new(0, 0))
        || layout.base != HomeSlotKey::new(1, 0)
        || layout.key.is_some()
        || layout.value != Some(HomeSlotKey::new(0, 0))
        || ret.values.fixed != [HirExpr::LocalRef(object)]
        || ret.values.tail.is_some()
        || !matches!(facts.native_return_frame(ret)?.values,
            ValuePack::Fixed(range) if range.start.index() == 0 && range.len == 1)
    {
        return None;
    }
    Some((
        HirLuauInliningBody::PublishedTableFactory { key },
        "".into(),
    ))
}

impl FrameBuilder<'_> {
    pub(in crate::hir::simplify::call_frames) fn expanded_published_table_argument(
        &mut self,
        call: &HirCallExpr,
        argument: usize,
        before: usize,
        slot: usize,
    ) -> Option<HirExpr> {
        let context = self.native?;
        let callees = context.expanded_callees?;
        let copy = self.facts.call_argument_copy(call, argument)?;
        let object = self.facts.promoted_local_for_temp(copy.source)?;
        let HirExpr::LocalRef(result) = *call.args.fixed.get(argument)? else {
            return None;
        };
        if self.dialect != DecompileDialect::Luau
            || (result != object && self.facts.promoted_local_for_temp(copy.target) != Some(result))
            || copy.target_home != HomeSlotKey::new(slot, 0)
            || copy.source_home != HomeSlotKey::new(slot + 1, 0)
        {
            return None;
        }
        let copied = self.definition(result, before)?;
        let seed = if object == result {
            copied
        } else {
            self.definition(object, copied)?
        };
        let (_, HirExpr::TableConstructor(table)) = scalar_local(self.run[seed])? else {
            return None;
        };
        let (access, value) = publication(self.run.get(seed + 1)?)?;
        let HirExpr::Integer(key) = access.key else {
            return None;
        };
        let callee = callees.get(&(
            HirLuauInliningBody::PublishedTableFactory { key },
            "".into(),
        ))?;
        let captured = callee.capture?;
        let HirOperationSources::Single(allocation) = table.sources else {
            return None;
        };
        let HirOperationSources::Single(write) = access.sources else {
            return None;
        };
        let layout = self.facts.native_table_write_layout(access)?;
        let debug_object = context.proto.local_debug_scopes[object.index()]
            .and_then(|scope| context.proto.debug_scopes[scope].as_ref())
            .is_some_and(|scope| {
                callee.result_name.is_some()
                    && context.proto.local_debug_hints[object.index()] == callee.result_name
                    && scope.initializer_temp == Some(copy.source)
                    && scope.initializer_end_instr == Some(allocation.instr)
                    && scope
                        .end_instr
                        .is_some_and(|end| end.index() == copy.instruction.index() + 1)
            });
        if !empty_table(table)
            || value != object
            || access.base != HirExpr::LocalRef(captured)
            || self.facts.trusted_local_home_slot(captured)? != layout.base
            || layout.base.slot() >= self.base
            || layout.value != Some(copy.source_home)
            || layout.key.is_some()
            || self.facts.operation_result_temp(allocation) != Some(copy.source)
            || self.facts.allocation_result_home(table) != Some(copy.source_home)
            || callee.creation.proto != allocation.proto
            || callee.creation.instr.index() >= allocation.instr.index()
            || write.instr.index() != allocation.instr.index() + 1
            || copy.instruction.index() != write.instr.index() + 1
            || call.source_site?.instr.index() <= copy.instruction.index()
            || (copied != seed
                && (copied != seed + 2
                    || scalar_local(self.run[copied])?.1 != &HirExpr::LocalRef(object)))
            || [copy.source_home, copy.target_home].iter().any(|home| {
                (context.barred.contains(home) && !(debug_object && *home == copy.source_home))
                    || context.closed.contains(home)
            })
            || (!debug_object
                && (context.proto.local_debug_hints[object.index()].is_some()
                    || context.proto.local_debug_scopes[object.index()].is_some()))
        {
            return None;
        }
        // 原高槽分配与低槽 COPY 连同字段写一起恢复；失败不得污染普通帧的事件游标。
        let cursor = (self.first_event, self.next_event);
        if self.finish_event(seed).is_none()
            || self.finish_event(seed + 1).is_none()
            || (copied != seed && self.finish_event(copied).is_none())
        {
            (self.first_event, self.next_event) = cursor;
            return None;
        }
        Some(factories::factory_call(
            callee.local,
            Some(allocation),
            HirValuePack::default(),
        ))
    }
}
