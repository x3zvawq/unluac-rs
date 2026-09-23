//! 在原槽被下一次调用准备覆盖时，恢复匿名声明的词法末端。
//!
//! 根的保活与覆盖来自共享 lifetime 分析；窗口内身份不得逃逸。先结束旧声明，
//! 避免 promotion 把后继 callee 合入旧 local 后永久占据它自己的调用准备槽。

use super::*;
use crate::hir::common::HirCallExpr;
use crate::hir::simplify::mention::BindingReadCollector;
use crate::hir::simplify::walk::{HirRewritePass, rewrite_proto};
use crate::hir::visit::visit_stmts;

pub(super) fn restore(
    proto: &mut HirProto,
    facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
    sensitive: &BTreeSet<TempId>,
) -> bool {
    let mut reads = BTreeMap::<TempId, usize>::new();
    visit_stmts(
        &proto.body.stmts,
        &mut BindingReadCollector(|binding| {
            if let HirBinding::Temp(temp) = binding {
                *reads.entry(temp).or_default() += 1;
            }
        }),
    );
    let debug = proto
        .temp_debug_scopes
        .iter()
        .enumerate()
        .filter_map(|(index, scope)| scope.is_some().then_some(TempId(index)))
        .chain(
            proto
                .temp_debug_locals
                .iter()
                .enumerate()
                .filter_map(|(index, name)| name.is_some().then_some(TempId(index))),
        )
        .collect();
    let mut pass = ScopePass {
        facts,
        safety,
        sensitive,
        reads,
        debug,
        call_results: BTreeSet::new(),
    };
    let changed = rewrite_proto(proto, &mut pass);
    proto.physical_root_temps.extend(pass.call_results);
    changed
}

struct ScopePass<'a> {
    facts: &'a ProtoPromotionFacts,
    safety: HirExprSafety,
    sensitive: &'a BTreeSet<TempId>,
    reads: BTreeMap<TempId, usize>,
    debug: BTreeSet<TempId>,
    call_results: BTreeSet<TempId>,
}

impl HirRewritePass for ScopePass<'_> {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        // 只处理真实根覆盖；控制流、捕获和 debug 身份仍由原 owner 恢复。
        // 只在直线块建立快照，避免父块为每个嵌套层重复分析整棵子树。
        if block.stmts.iter().any(|stmt| {
            !matches!(
                stmt,
                HirStmt::Assign(_) | HirStmt::CallStmt(_) | HirStmt::Return(_)
            )
        }) {
            return false;
        }
        let snapshot = RootLifetimeFacts::new(&block.stmts, self.facts, self.safety);
        let roots = collect_call_root_lifetimes(
            &snapshot,
            self.facts,
            self.safety,
            true,
            |temp| !self.sensitive.contains(&temp) && !self.debug.contains(&temp),
            |_| RootOverwritePolicy::Reuse,
        );
        let mut windows = BTreeMap::new();
        let call_floors = CallFloors::new(&block.stmts, self.facts);
        let mut scanned = 0;
        let mut callees = BTreeMap::new();
        let mut definitions = BTreeMap::new();
        let mut last_definitions = BTreeMap::new();
        for (index, stmt) in block.stmts.iter().enumerate() {
            if let Some((temp, value)) = stmt.scalar_temp_assignment() {
                let previous = self
                    .facts
                    .trusted_temp_home_slot(temp)
                    .and_then(|home| last_definitions.get(&home).copied());
                callees
                    .entry(temp)
                    .and_modify(|entry| *entry = None)
                    .or_insert_with(|| {
                        let source_home = match value {
                            HirExpr::TempRef(source) => self.facts.trusted_temp_home_slot(*source),
                            HirExpr::LocalRef(source) => {
                                self.facts.trusted_local_home_slot(*source)
                            }
                            HirExpr::ParamRef(source) => {
                                self.facts.trusted_param_home_slot(*source)
                            }
                            _ => None,
                        };
                        let low_copy = source_home
                            .zip(self.facts.trusted_temp_home_slot(temp))
                            .is_some_and(|(source, target)| source.slot() < target.slot());
                        (matches!(value, HirExpr::GlobalRef(_)) || low_copy)
                            .then_some((index, previous))
                    });
            }
            if let HirStmt::Assign(assign) = stmt {
                for target in &assign.targets {
                    if let HirLValue::Temp(temp) = target {
                        definitions
                            .entry(*temp)
                            .and_modify(|entry| *entry = None)
                            .or_insert(Some(index));
                        if let Some(home) = self.facts.trusted_temp_home_slot(*temp) {
                            last_definitions.insert(home, index);
                        }
                    }
                }
            }
            let call = match stmt {
                HirStmt::CallStmt(stmt) => &stmt.call,
                stmt => match stmt.scalar_temp_assignment() {
                    Some((_, HirExpr::Call(call))) => call,
                    _ => continue,
                },
            };
            let HirExpr::TempRef(callee) = call.callee else {
                continue;
            };
            let Some(Some((callee_start, previous))) = callees.get(&callee).copied() else {
                continue;
            };
            let Some(frame) = self
                .facts
                .native_call_frame(call)
                .or_else(|| self.facts.native_fastcall_frame(call))
            else {
                continue;
            };
            if frame.callee != callee || self.reads.get(&callee) != Some(&1) {
                continue;
            }
            let Some(end) = self.preparation_start(call, frame.home, index, &definitions) else {
                continue;
            };
            let literal_start = previous.filter(|&start| {
                block.stmts[start]
                    .scalar_temp_assignment()
                    .is_some_and(|(_, value)| {
                        matches!(
                            value,
                            HirExpr::Nil
                                | HirExpr::Boolean(_)
                                | HirExpr::Integer(_)
                                | HirExpr::Number(_)
                                | HirExpr::String(_)
                                | HirExpr::Int64(_)
                                | HirExpr::UInt64(_)
                                | HirExpr::Complex { .. }
                                | HirExpr::Vector(_)
                        )
                    })
            });
            let Some(mut start) = literal_start.or_else(|| {
                roots
                    .overwrite_pair_for_home(callee_start, frame.home)
                    .map(|root| root.root_index())
            }) else {
                continue;
            };
            if start < scanned || start >= end {
                continue;
            }
            // lifetime 索引也包含 callee lookup 和多槽 owner；这里仅结束原单值
            // CALL 结果的声明域，不能把调用准备本身或多结果写回切成独立词法块。
            if literal_start.is_none() {
                let Some((result, HirExpr::Call(producer))) =
                    block.stmts[start].scalar_temp_assignment()
                else {
                    continue;
                };
                if self.facts.trusted_temp_home_slot(result) != Some(frame.home)
                    || self.facts.native_call_frame(producer).is_none_or(|producer|
                        producer.home != frame.home
                            || !matches!(producer.results, Some(crate::transformer::ResultPack::Fixed(pack))
                                if pack.start.index() == frame.home.slot() && pack.len == 1))
                {
                    continue;
                }
                // callee COPY 与嵌套参数的尚存准备必须一起进入旧域；FASTCALL 的
                // 参数也可能先于 callee。仅移动词法边界，完整调用仍由帧 owner 重建。
                let Some(preparation) =
                    self.preparation_start(producer, frame.home, start, &definitions)
                else {
                    continue;
                };
                start = preparation;
            }
            if start < scanned || start >= end {
                continue;
            }
            if literal_start.is_some() && call_floors.minimum(start, end) <= frame.home.slot() {
                // 常量不承载独立 GC 身份；其词法槽仍须在窗口中的每次调用下方。
                // 若中途调用已复用该槽，不能把原准备临时量猜成跨调用声明。
                // 这类参数准备不是可扫描窗口，不能推进 scanned 而屏蔽外围完整结果域。
                continue;
            }
            // 闭合性扫描不重复覆盖旧窗口；调用下界查询独立走区间索引，嵌套的
            // 失败参数候选不会反复遍历大段语句，也不会抢占真正的作用域候选。
            scanned = end;
            if self.closed_window(&block.stmts[start..end], frame.home) {
                windows.insert(start, end);
                // 窗口中的原单值 CALL 结果仍占据对应槽；不能先丢掉未使用结果，
                // 再要求后续源码帧验证一个尚无声明的 Temp。只在这个已闭合窗口保留它。
                for stmt in &block.stmts[start..end] {
                    if let Some((temp, HirExpr::Call(call))) = stmt.scalar_temp_assignment()
                        && let Some(frame) = self.facts.native_call_frame(call)
                        && self.facts.trusted_temp_home_slot(temp) == Some(frame.home)
                        && matches!(frame.results, Some(crate::transformer::ResultPack::Fixed(pack))
                            if pack.start.index() == frame.home.slot() && pack.len == 1)
                    {
                        self.call_results.insert(temp);
                    }
                }
            }
        }
        if windows.is_empty() {
            return false;
        }
        let old = std::mem::take(&mut block.stmts);
        let mut remaining = old.into_iter().enumerate().peekable();
        while let Some((index, stmt)) = remaining.next() {
            if let Some(&end) = windows.get(&index) {
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
        true
    }
}

impl ScopePass<'_> {
    fn preparation_start(
        &self,
        call: &HirCallExpr,
        base: HomeSlotKey,
        consumer: usize,
        definitions: &BTreeMap<TempId, Option<usize>>,
    ) -> Option<usize> {
        let mut start = consumer;
        let mut valid = true;
        crate::hir::visit::visit_call(
            call,
            &mut BindingReadCollector(|binding| {
                let HirBinding::Temp(temp) = binding else {
                    return;
                };
                let Some(home) = self.facts.trusted_temp_home_slot(temp) else {
                    valid = false;
                    return;
                };
                if home.slot() >= base.slot() {
                    if let Some(Some(index)) = definitions
                        .get(&temp)
                        .filter(|entry| entry.is_some_and(|index| index < consumer))
                    {
                        start = start.min(*index);
                    } else {
                        valid = false;
                    }
                }
            }),
        );
        valid.then_some(start)
    }

    fn closed_window(&self, stmts: &[HirStmt], base: HomeSlotKey) -> bool {
        let mut definitions = BTreeSet::new();
        for stmt in stmts {
            match stmt {
                HirStmt::Assign(assign) => {
                    for target in &assign.targets {
                        // 表写入不声明或重绑定 local；整个语句保持原顺序进入词法域，
                        // 其 base/key/value 读取仍参加下方闭合性检查。原写入布局必须可追溯，
                        // 不能把未知物理副作用当作仅有表达式读取的语句。
                        if let HirLValue::TableAccess(access) = target {
                            if self.facts.native_table_write_layout(access).is_none() {
                                return false;
                            }
                            continue;
                        }
                        let HirLValue::Temp(temp) = target else {
                            return false;
                        };
                        if self.sensitive.contains(temp)
                            || self.debug.contains(temp)
                            || self
                                .facts
                                .trusted_temp_home_slot(*temp)
                                .is_none_or(|home| home.slot() < base.slot())
                            || !definitions.insert(*temp)
                        {
                            return false;
                        }
                    }
                }
                HirStmt::CallStmt(_) => {}
                _ => return false,
            }
        }
        let mut reads = BTreeMap::<TempId, usize>::new();
        visit_stmts(
            stmts,
            &mut BindingReadCollector(|binding| {
                if let HirBinding::Temp(temp) = binding {
                    *reads.entry(temp).or_default() += 1;
                }
            }),
        );
        // 候选拒绝[SemanticBarrier:Scope]：任何窗口外读取仍依赖旧身份，不能缩短其声明。
        definitions
            .iter()
            .all(|temp| reads.get(temp) == self.reads.get(temp))
    }
}

/// 一次索引本块的原 CALL 下界；失败字面量窗口可以相互包含，查询不能重复扫描。
struct CallFloors {
    leaves: usize,
    minimum: Vec<usize>,
}

impl CallFloors {
    fn new(stmts: &[HirStmt], facts: &ProtoPromotionFacts) -> Self {
        struct Calls<'a> {
            facts: &'a ProtoPromotionFacts,
            floor: usize,
        }
        impl crate::hir::visit::HirVisitor<'_> for Calls<'_> {
            fn visit_call(&mut self, call: &HirCallExpr) {
                self.floor = self.floor.min(
                    self.facts
                        .native_call_frame(call)
                        .map_or(0, |frame| frame.home.slot()),
                );
            }
        }
        let leaves = stmts.len().next_power_of_two();
        let mut minimum = vec![usize::MAX; leaves * 2];
        for (index, stmt) in stmts.iter().enumerate() {
            let mut calls = Calls {
                facts,
                floor: usize::MAX,
            };
            visit_stmts(std::slice::from_ref(stmt), &mut calls);
            minimum[leaves + index] = calls.floor;
        }
        for index in (1..leaves).rev() {
            minimum[index] = minimum[index * 2].min(minimum[index * 2 + 1]);
        }
        Self { leaves, minimum }
    }

    fn minimum(&self, start: usize, end: usize) -> usize {
        let (mut left, mut right) = (self.leaves + start, self.leaves + end);
        let mut result = usize::MAX;
        while left < right {
            if left % 2 == 1 {
                result = result.min(self.minimum[left]);
                left += 1;
            }
            if right % 2 == 1 {
                right -= 1;
                result = result.min(self.minimum[right]);
            }
            left /= 2;
            right /= 2;
        }
        result
    }
}
