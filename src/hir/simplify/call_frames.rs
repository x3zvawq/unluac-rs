//! 将已证明属于同一 PUC 调用帧的终结物化序列树化，保留槽覆盖与 dispatch 的根交接。
//!
//! Promotion 提供完整写入 home，method setup 提供原 callee home；这里核对当前定义版本、
//! 原求值顺序与源码调用帧的相对位置，不从 AST 反推寄存器。仅处理末尾普通调用中的方法链，
//! 不越过控制流、debug/capture/TBC 身份或独立的低槽 root。
//! 例如 `f=print; a=obj:make(); b=a:next(); a=b.finish; f(a(b))` 的 a 若原本就是
//! 下一次 SELF 覆盖的 callee 槽，应恢复 `print(obj:make():next():finish())`；保留 a 为
//! 源码 local 反而会在 next 清空 self 后延长旧对象寿命。方法 receiver 树化后只持有一次。

use std::collections::{BTreeMap, BTreeSet};

use super::mention::{CaptureCollector, ProtectedLocalCollector, ToBeClosedHomeCollector};
use crate::decompile::DecompileDialect;
use crate::hir::common::{
    HirBlock, HirCallExpr, HirCallRootHandoff, HirCaptureMode, HirExpr, HirLValue, HirMethodCall,
    HirProto, HirStmt, LocalId,
};
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

pub(super) fn restore_terminal_call_frame(
    proto: &mut HirProto,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
) {
    if matches!(dialect, DecompileDialect::Luajit | DecompileDialect::Luau) {
        return;
    }
    let mut collectors = (
        (
            CaptureCollector::new(HirCaptureMode::ByReference),
            CaptureCollector::new(HirCaptureMode::ByValue),
        ),
        (
            ProtectedLocalCollector::default(),
            ToBeClosedHomeCollector {
                facts,
                homes: BTreeSet::new(),
            },
        ),
    );
    crate::hir::visit::visit_stmts(&proto.body.stmts, &mut collectors);
    let ((reference, value), (protected, closed)) = collectors;
    let mut barred = reference.bindings.complete_home_slots(facts);
    barred.extend(value.bindings.complete_home_slots(facts));
    barred.extend(closed.homes);
    for local in protected.locals {
        barred.extend(facts.complete_local_home_slots(local).iter().copied());
    }
    let mut body = std::mem::take(&mut proto.body);
    rewrite_terminal(&mut body, proto, facts, dialect, &barred);
    proto.body = body;
}

fn terminal_index(block: &HirBlock) -> Option<usize> {
    let index = block.stmts.len().checked_sub(1)?;
    if matches!(&block.stmts[index], HirStmt::Return(ret) if ret.values.is_empty()) {
        index.checked_sub(1)
    } else {
        Some(index)
    }
}

fn rewrite_terminal(
    block: &mut HirBlock,
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    barred: &BTreeSet<HomeSlotKey>,
) {
    let Some(end) = terminal_index(block) else {
        return;
    };
    if let HirStmt::Block(child) = &mut block.stmts[end] {
        rewrite_terminal(child, proto, facts, dialect, barred);
        return;
    }
    let Some((start, end, call)) = plan(block, proto, facts, dialect, barred) else {
        return;
    };
    let HirStmt::CallStmt(sink) = &mut block.stmts[end] else {
        unreachable!()
    };
    sink.call = call;
    block.stmts.drain(start..end);
}

fn scalar_local(stmt: &HirStmt) -> Option<(LocalId, &HirExpr)> {
    match stmt {
        HirStmt::LocalDecl(decl) => match (
            decl.bindings.as_slice(),
            decl.values.fixed.as_slice(),
            &decl.values.tail,
        ) {
            ([local], [value], None) => Some((*local, value)),
            _ => None,
        },
        HirStmt::Assign(assign) => match (
            assign.targets.as_slice(),
            assign.values.fixed.as_slice(),
            &assign.values.tail,
        ) {
            ([HirLValue::Local(local)], [value], None) => Some((*local, value)),
            _ => None,
        },
        _ => None,
    }
}

fn plan(
    block: &HirBlock,
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    barred: &BTreeSet<HomeSlotKey>,
) -> Option<(usize, usize, HirCallExpr)> {
    let end = terminal_index(block)?;
    let HirStmt::CallStmt(sink) = &block.stmts[end] else {
        return None;
    };
    if sink.call.is_method() || sink.call.fastcall.is_some() {
        return None;
    }
    let HirExpr::LocalRef(callee) = sink.call.callee else {
        return None;
    };
    let start = (0..end).rfind(|index| {
        scalar_local(&block.stmts[*index]).is_some_and(|(local, _)| local == callee)
    })?;
    if !matches!(scalar_local(&block.stmts[start])?.1, HirExpr::GlobalRef(_)) {
        return None;
    }
    let base = facts.trusted_local_home_slot(callee)?;
    let run = &block.stmts[start..end];
    let mut definitions = BTreeMap::<LocalId, Vec<usize>>::new();
    let mut declared = BTreeSet::new();
    for (index, stmt) in run.iter().enumerate() {
        let (local, _) = scalar_local(stmt)?;
        if matches!(stmt, HirStmt::LocalDecl(_)) {
            if !declared.insert(local) {
                return None;
            }
        } else if !declared.contains(&local) {
            return None;
        }
        if proto
            .local_debug_hints
            .get(local.index())
            .is_some_and(Option::is_some)
            || proto
                .local_debug_scopes
                .get(local.index())
                .is_some_and(Option::is_some)
            || proto.inline_dispositions.local(local).must_preserve()
        {
            return None;
        }
        let homes = facts.complete_local_definition_write_homes(local);
        if homes.is_empty() || !homes.is_disjoint(barred) {
            return None;
        }
        definitions.entry(local).or_default().push(index);
    }
    let mut builder = FrameBuilder {
        run,
        definitions,
        facts,
        dialect,
        base: base.slot(),
        next_event: 0,
        methods: 0,
    };
    let call = builder.call(&sink.call, run.len(), base.slot(), true)?;
    // 每个原 producer 必须恰好求值一次，且位置顺序相同；同时排除捕获、自更新和遗漏写入。
    if builder.methods == 0 || builder.next_event != run.len() {
        return None;
    }
    Some((start, end, call))
}

struct FrameBuilder<'a> {
    run: &'a [HirStmt],
    definitions: BTreeMap<LocalId, Vec<usize>>,
    facts: &'a ProtoPromotionFacts,
    dialect: DecompileDialect,
    base: usize,
    next_event: usize,
    methods: usize,
}

impl FrameBuilder<'_> {
    fn finish_event(&mut self, index: usize) -> Option<()> {
        if index != self.next_event {
            return None;
        }
        self.next_event += 1;
        Some(())
    }

    fn definition(&self, local: LocalId, before: usize) -> Option<usize> {
        let indices = self.definitions.get(&local)?;
        indices
            .get(
                indices
                    .partition_point(|index| *index < before)
                    .checked_sub(1)?,
            )
            .copied()
    }

    fn homes_match(&self, local: LocalId, slot: usize, receiver: bool) -> bool {
        let homes = self.facts.complete_local_definition_write_homes(local);
        !homes.is_empty()
            && homes.iter().all(|home| {
                *home == HomeSlotKey::new(slot, 0)
                    || (receiver && *home == HomeSlotKey::new(slot + 1, 0))
            })
    }

    fn expr(
        &mut self,
        expr: &HirExpr,
        before: usize,
        slot: usize,
        receiver: bool,
    ) -> Option<HirExpr> {
        match expr {
            HirExpr::LocalRef(local) => {
                if let Some(index) = self.definition(*local, before) {
                    if index < self.next_event || !self.homes_match(*local, slot, receiver) {
                        return None;
                    }
                    let value = scalar_local(&self.run[index])?.1;
                    let result = self.expr(value, index, slot, receiver)?;
                    self.finish_event(index)?;
                    Some(result)
                } else {
                    let home = self.facts.trusted_local_home_slot(*local)?;
                    (home.slot() < self.base).then(|| expr.clone())
                }
            }
            HirExpr::ParamRef(param) => (self.facts.trusted_param_home_slot(*param)?.slot()
                < self.base)
                .then(|| expr.clone()),
            HirExpr::Call(call) => self
                .call(call, before, slot, false)
                .map(|call| HirExpr::Call(Box::new(call))),
            HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::GlobalRef(_) => Some(expr.clone()),
            // 其它操作有各自的目标槽和分配协议，不能借当前调用帧证明一并移动。
            _ => None,
        }
    }

    fn call(
        &mut self,
        call: &HirCallExpr,
        before: usize,
        slot: usize,
        outer: bool,
    ) -> Option<HirCallExpr> {
        let mut result = call.clone();
        let first_arg = if outer {
            result.callee = self.expr(&call.callee, before, slot, false)?;
            0
        } else {
            let HirCallRootHandoff::MethodCallee(protocol_id) = call.callee_root_handoff?;
            let protocol = self.facts.method_setup_protocol(protocol_id)?;
            if call.method != HirMethodCall::Explicit
                || call.fastcall.is_some()
                || self.facts.trusted_temp_home_slot(protocol.callee_temp)?
                    != HomeSlotKey::new(slot, 0)
                || !protocol
                    .method_key
                    .as_utf8()
                    .is_some_and(|key| self.dialect.is_identifier_name(key))
                || !call.argument_roots.iter().any(|root| {
                    root.argument == 0
                        && self.facts.trusted_temp_home_slot(root.producer)
                            == Some(HomeSlotKey::new(slot + 1, 0))
                })
            {
                return None;
            }
            let (access, lookup_index) = match &call.callee {
                HirExpr::TableAccess(access) => (access.as_ref(), None),
                HirExpr::LocalRef(local) => {
                    let index = self.definition(*local, before)?;
                    if index < self.next_event
                        || self.facts.trusted_local_home_slot(*local)? != HomeSlotKey::new(slot, 0)
                    {
                        return None;
                    }
                    let HirExpr::TableAccess(access) = scalar_local(&self.run[index])?.1 else {
                        return None;
                    };
                    (access.as_ref(), Some(index))
                }
                _ => return None,
            };
            if super::method_protocol::match_method_setup_pair(access, &call.callee, call)?
                != protocol_id
            {
                return None;
            }
            let lookup_before = lookup_index.unwrap_or(before);
            if let HirExpr::LocalRef(receiver) = access.base
                && self.definition(receiver, lookup_before) != self.definition(receiver, before)
            {
                return None;
            }
            let mut access = access.clone();
            access.base = self.expr(&access.base, lookup_before, slot, true)?;
            result.callee = HirExpr::TableAccess(Box::new(access));
            if let Some(index) = lookup_index {
                self.finish_event(index)?;
            }
            result.method = HirMethodCall::Implicit;
            result.method_rewrite_transaction = None;
            self.methods += 1;
            1
        };
        result.args.fixed = call
            .args
            .fixed
            .iter()
            .enumerate()
            .skip(first_arg)
            .map(|(index, arg)| self.expr(arg, before, slot + 1 + index, false))
            .collect::<Option<Vec<_>>>()?;
        if let Some(tail) = &mut result.args.tail {
            let expr = self.expr(
                tail.as_expr(),
                before,
                slot + 1 + call.args.fixed.len(),
                false,
            )?;
            let HirExpr::Call(call) = expr else {
                return None;
            };
            *tail.call_mut()? = *call;
        }
        // 已整体消费原帧事实；最终 AST 不需要物理槽或已退役 temp 身份。
        result.argument_roots.clear();
        result.frame_root_ends.clear();
        Some(result)
    }
}
