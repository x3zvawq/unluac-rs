//! 在原槽被后继调用准备或独立环境读取覆盖时，恢复匿名声明的词法末端。
//!
//! 根的保活与覆盖来自共享 lifetime 分析；窗口内身份不得逃逸。先结束旧声明，
//! 避免 promotion 把后继 callee 合入旧 local 后永久占据它自己的调用准备槽。

use super::*;
use crate::hir::common::HirCallExpr;
use crate::hir::simplify::mention::{BindingReadCollector, BindingWriteCollector};
use crate::hir::simplify::root_lifetimes::direct_call_in_stmt;
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
        root_results: BTreeSet::new(),
    };
    let changed = rewrite_proto(proto, &mut pass);
    proto.physical_root_temps.extend(pass.root_results);
    changed
}

struct ScopePass<'a> {
    facts: &'a ProtoPromotionFacts,
    safety: HirExprSafety,
    sensitive: &'a BTreeSet<TempId>,
    reads: BTreeMap<TempId, usize>,
    debug: BTreeSet<TempId>,
    root_results: BTreeSet<TempId>,
}

impl HirRewritePass for ScopePass<'_> {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        // 只为跨本块直属调用的匿名身份建窗。纯分支不自行索引，避免每层嵌套 if
        // 重复遍历同一子树；包含调用的子域会在下面的分支边界检查中截断父级扫描。
        if !block
            .stmts
            .iter()
            .any(|stmt| direct_call_in_stmt(stmt).is_some())
        {
            return false;
        }
        let scan_end = block
            .stmts
            .iter()
            .position(|stmt| {
                !scope_statement(stmt)
                    && !matches!(
                        stmt,
                        HirStmt::Block(_)
                            | HirStmt::NumericFor(_)
                            | HirStmt::ToBeClosed(_)
                            | HirStmt::Close(_)
                    )
            })
            .unwrap_or(block.stmts.len());
        // 数值 for 已有封闭控制协议，只分隔前后窗口；其内部仍独立递归处理。
        // 未闭合协议阻止扫描其自身及后缀，但不阻止之前已由原覆盖端点闭合的窗口。
        // 全 proto 读取索引仍拒绝任何逃逸到后缀的定义；不在未知节点之后重新起窗。
        let stmts = &block.stmts[..scan_end];
        let mut windows = BTreeMap::new();
        let mut start = 0;
        for end in 0..=stmts.len() {
            if end < stmts.len() && scope_statement(&stmts[end]) {
                continue;
            }
            if start < end {
                windows.extend(
                    self.scope_windows(&stmts[start..end])
                        .into_iter()
                        .map(|(first, last)| (start + first, start + last)),
                );
            }
            start = end + 1;
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

/// 已闭合的表写/Boolean 分支和直线循环可留在扫描区；候选窗口另行核对身份与写域。
/// 已闭合词法子块及显式资源激活/关闭分隔候选区，未支持结构截断后缀；每条语句至多在自身及父区各索引一次。
fn scope_statement(stmt: &HirStmt) -> bool {
    match stmt {
        // 已有声明留在扫描区，候选窗口仍拒绝包含它；不把声明当分隔符切断跨语句协议。
        HirStmt::Assign(_) | HirStmt::LocalDecl(_) | HirStmt::CallStmt(_) | HirStmt::Return(_) => {
            true
        }
        HirStmt::GenericFor(for_) => scope_loop_body(&for_.body),
        HirStmt::While(while_) => scope_loop_body(&while_.body),
        HirStmt::Repeat(repeat) => scope_loop_body(&repeat.body),
        HirStmt::If(branch) => scope_branch(branch),
        _ => false,
    }
}

fn scope_loop_body(body: &HirBlock) -> bool {
    // 整个已结构化循环留在窗口内；不移动退出条件或把零/多次执行改成直线执行。
    // 规范化的单臂 break 只退出这个循环，不离开包住整个循环的候选窗口。
    // 资源、其它转移及未完成嵌套协议仍拒绝，原调用下界和全部临时读写另行核对。
    body.stmts
        .iter()
        .all(|stmt| matches!(stmt, HirStmt::Assign(_) | HirStmt::CallStmt(_))
            // 空循环没有内部声明或跨语句准备；条件读取及调用仍由窗口索引核对，
            // 循环整体留在原位置，不改变其零次执行或不终止的行为。
            || matches!(stmt, HirStmt::While(inner) if inner.body.stmts.is_empty())
            || matches!(stmt, HirStmt::Repeat(inner) if inner.body.stmts.is_empty())
            || matches!(stmt, HirStmt::If(branch)
                if branch.else_block.is_none() && matches!(branch.then_block.stmts.as_slice(), [HirStmt::Break])))
}

fn scope_branch(branch: &crate::hir::common::HirIf) -> bool {
    let bodies = || std::iter::once(&branch.then_block).chain(branch.else_block.as_ref());
    let operand = |value: &HirExpr| {
        matches!(
            value,
            HirExpr::TempRef(_)
                | HirExpr::LocalRef(_)
                | HirExpr::ParamRef(_)
                | HirExpr::UpvalueRef(_)
                | HirExpr::Nil
                | HirExpr::Boolean(_)
                | HirExpr::Integer(_)
                | HirExpr::Number(_)
                | HirExpr::String(_)
        )
    };
    // 先检查直属节点，再进入嵌套分支。含独立分配、调用或 COPY 的子域仍由自己的
    // owner 处理；父扫描不会为它反复遍历整个后代，或切开尚未闭合的准备协议。
    if !bodies().all(|body| body.stmts.iter().all(|stmt| {
        matches!(stmt, HirStmt::If(_))
            || matches!(stmt.scalar_temp_assignment(), Some((_, HirExpr::Boolean(_))))
            || matches!(stmt, HirStmt::Assign(assign)
                if !assign.targets.is_empty()
                    && assign.values.tail.is_none()
                    && assign.values.fixed.iter().all(operand)
                    && assign.targets.iter().all(|target| matches!(target, HirLValue::TableAccess(access)
                        if operand(&access.base) && operand(&access.key))))
    })) {
        // 候选拒绝[LayerBoundary]：未闭合的分支准备仍属于原表达式/展开帧 owner。
        return false;
    }
    bodies().all(|body| {
        body.stmts.iter().all(|stmt| {
            if let HirStmt::If(nested) = stmt {
                scope_branch(nested)
            } else {
                true
            }
        })
    })
}

impl ScopePass<'_> {
    fn scope_windows(&mut self, stmts: &[HirStmt]) -> BTreeMap<usize, usize> {
        let snapshot = RootLifetimeFacts::new(stmts, self.facts, self.safety);
        let roots = collect_call_root_lifetimes(
            &snapshot,
            self.facts,
            self.safety,
            true,
            |temp| !self.sensitive.contains(&temp) && !self.debug.contains(&temp),
            |_| RootOverwritePolicy::Reuse,
        );
        let scalar_roots =
            collect_scalar_gc_root_lifetimes(&snapshot, self.facts, self.safety, |temp| {
                !self.sensitive.contains(&temp) && !self.debug.contains(&temp)
            });
        let mut windows = BTreeMap::new();
        let call_floors = CallFloors::new(stmts, self.facts);
        // 直接 callee 的词法末端仍由完整调用准备决定，尤其是参数先于 callee 的 FASTCALL。
        let callees_in_calls = stmts
            .iter()
            .filter_map(direct_call_in_stmt)
            .filter_map(|call| match call.callee {
                HirExpr::TempRef(temp) => Some(temp),
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        let mut scanned = 0;
        let mut callees = BTreeMap::new();
        let mut definitions = BTreeMap::new();
        let mut last_definitions = BTreeMap::new();
        for (index, stmt) in stmts.iter().enumerate() {
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
                        (matches!(value, HirExpr::GlobalRef(_) | HirExpr::UpvalueRef(_))
                            || low_copy)
                            .then_some((index, previous))
                    });
            }
            // 参数的 Boolean 结果可仍由互斥分支写入；整个分支是同一个准备位置。
            // 不把两臂当作两个无关定义，也不把前面的 callee 截在旧词法域内。
            visit_stmts(
                std::slice::from_ref(stmt),
                &mut BindingWriteCollector(|binding| {
                    if let HirBinding::Temp(temp) = binding {
                        definitions
                            .entry(temp)
                            .and_modify(|entry| {
                                if *entry != Some(index) {
                                    *entry = None;
                                }
                            })
                            .or_insert(Some(index));
                        if let Some(home) = self.facts.trusted_temp_home_slot(temp) {
                            last_definitions.insert(home, index);
                        }
                    }
                }),
            );
            let (home, overwrite, end, previous) =
                if matches!(stmt, HirStmt::Assign(_) | HirStmt::CallStmt(_))
                    && let Some(call) = direct_call_in_stmt(stmt)
                {
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
                    let Some(end) = self.preparation_start(call, frame.home, index, &definitions)
                    else {
                        continue;
                    };
                    (frame.home, callee_start, end, previous)
                } else if let Some((temp, HirExpr::GlobalRef(global))) =
                    stmt.scalar_temp_assignment()
                {
                    let crate::hir::common::HirOperationSources::Single(source) = global.sources
                    else {
                        continue;
                    };
                    let Some(home) = self.facts.trusted_temp_home_slot(temp) else {
                        continue;
                    };
                    let previous = callees
                        .get(&temp)
                        .copied()
                        .flatten()
                        .and_then(|(_, previous)| previous);
                    let closes_closure =
                        previous.is_some_and(|index| self.closure_root_at(stmts, index, home));
                    if (self.reads.get(&temp).is_none_or(|&reads| reads < 2) && !closes_closure)
                        || callees_in_calls.contains(&temp)
                        || self.facts.operation_result_temp(source) != Some(temp)
                        || self.facts.direct_global_read_home(source) != Some(home)
                    {
                        // 候选拒绝[LayerBoundary]：单次环境读取可能仍在完整外层调用的准备中；
                        // 不能让其局部候选先推进扫描，屏蔽包含整个准备区的原调用端点。
                        continue;
                    }
                    // 原低槽环境读取可开始新的独立身份，不必随后作为 callee 使用。
                    // 单指令来源排除旧域中的输入准备；原 CLOSURE 的同槽后继即使只读一次，
                    // 也可与完整调用下界、读写闭合性共同证明旧声明末端。其它覆盖沿用 root 分析。
                    (home, index, index, previous)
                } else {
                    continue;
                };
            let literal_start = previous.filter(|&start| {
                stmts[start]
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
            let closure_start = previous.filter(|&index| self.closure_root_at(stmts, index, home));
            let Some(mut start) = literal_start.or(closure_start).or_else(|| {
                roots
                    .overwrite_pair_for_home(overwrite, home)
                    .or_else(|| scalar_roots.overwrite_pair_for_home(overwrite, home))
                    .map(|root| root.root_index())
            }) else {
                continue;
            };
            if start < scanned || start >= end {
                continue;
            }
            // 多结果只能连同全部目标结束；不能把同一次 CALL 的 owner 拆成独立词法块。
            if literal_start.is_none() && closure_start.is_none() {
                // 一个宽返回组可能在多个 home 上陆续被覆盖；先按原 CALL 排除非首结果，
                // 避免为每个成员的候选重复展开整组目标。
                if let Some(producer) = direct_call_in_stmt(&stmts[start])
                    && let Some(original) = self.facts.native_call_frame(producer)
                    && original.home == home
                    && let Some(targets) = exact_multi_call_home_targets(&stmts[start], self.facts)
                {
                    if !matches!(original.results, Some(crate::transformer::ResultPack::Fixed(pack))
                                if pack.start.index() == home.slot() && pack.len == targets.len())
                        || targets
                            .iter()
                            .enumerate()
                            .any(|(offset, (_, member))| member.slot() != home.slot() + offset)
                        || call_floors.minimum(start + 1, end) < home.slot() + targets.len()
                    {
                        // 候选拒绝[ProofIncomplete]：所有结果必须共同占据原低槽前缀，窗口内调用不能复用其中一员。
                        continue;
                    }
                    let Some(preparation) =
                        self.preparation_start(producer, home, start, &definitions)
                    else {
                        continue;
                    };
                    start = preparation;
                } else if let Some((result, value)) = stmts[start].scalar_temp_assignment() {
                    if self.facts.trusted_temp_home_slot(result) != Some(home) {
                        continue;
                    }
                    match value {
                        HirExpr::Call(producer) => {
                            if self.facts.native_call_frame(producer).is_none_or(|producer|
                            producer.home != home
                                || !matches!(producer.results, Some(crate::transformer::ResultPack::Fixed(pack))
                                    if pack.start.index() == home.slot() && pack.len == 1))
                        {
                            continue;
                        }
                            if self.reads.get(&result) == Some(&1)
                                && call_floors.minimum(start + 1, end) <= home.slot()
                            {
                                // 候选拒绝[LayerBoundary]：单次使用的结果遇到较低/同槽调用时，
                                // 尚不能证明独立声明域；完整外层调用准备应由帧 owner 消费。
                                // 多次使用的源码结果可在最后一次调用时交出根，不由此拒绝。
                                continue;
                            }
                            // callee COPY 与嵌套参数的尚存准备必须一起进入旧域；FASTCALL 的
                            // 参数也可能先于 callee。完整调用仍由帧 owner 重建。
                            let Some(preparation) =
                                self.preparation_start(producer, home, start, &definitions)
                            else {
                                continue;
                            };
                            start = preparation;
                        }
                        HirExpr::TableConstructor(table)
                            if self.facts.allocation_result_home(table) == Some(home) =>
                        {
                            let floor = call_floors.minimum(start, end);
                            if floor == usize::MAX || floor <= home.slot() {
                                // 候选拒绝[LayerBoundary]：没有跨调用的低槽对象身份时，
                                // 分配仍属于高槽字段/参数准备，交完整构造器或调用帧消费。
                                continue;
                            }
                        }
                        HirExpr::Unary(unary)
                            if self.facts.unary_result_home(unary) == Some(home) =>
                        {
                            let input = match unary.expr {
                                HirExpr::TempRef(temp) => self.facts.trusted_temp_home_slot(temp),
                                HirExpr::LocalRef(local) => {
                                    self.facts.trusted_local_home_slot(local)
                                }
                                HirExpr::ParamRef(param) => {
                                    self.facts.trusted_param_home_slot(param)
                                }
                                _ => None,
                            };
                            let floor = call_floors.minimum(start + 1, end);
                            if input.is_none_or(|input| {
                                input.slot() >= home.slot()
                                    || self.facts.unary_operand_home(unary) != Some(input)
                            }) || floor == usize::MAX
                                || floor <= home.slot()
                            {
                                // LayerBoundary：只恢复独立低槽输入之上的原结果声明；
                                // 同槽或高槽准备仍交给完整表达式帧，不能截断其输入寿命。
                                continue;
                            }
                        }
                        HirExpr::TempRef(_) => {
                            let Some(initializer) = self.allocation_copy_start(stmts, start, home)
                            else {
                                continue;
                            };
                            if call_floors.minimum(initializer, end) <= home.slot() {
                                // 候选拒绝[ProofIncomplete]：初始化段内的调用仍须位于低槽接收者之上。
                                continue;
                            }
                            start = initializer;
                        }
                        _ => continue,
                    }
                } else {
                    continue;
                }
            }
            if start < scanned || start >= end {
                continue;
            }
            if (literal_start.is_some() || closure_start.is_some())
                && call_floors.minimum(start, end) <= home.slot()
            {
                // 原声明槽须在窗口中的每次调用下方；闭包同样不能借词法结束改变原覆盖时点。
                // 若中途调用已复用该槽，不能把原准备临时量猜成跨调用声明。
                // 这类参数准备不是可扫描窗口，不能推进 scanned 而屏蔽外围完整结果域。
                continue;
            }
            // 闭合性扫描不重复覆盖旧窗口；调用下界查询独立走区间索引，嵌套的
            // 失败参数候选不会反复遍历大段语句，也不会抢占真正的作用域候选。
            scanned = end;
            if self.closed_window(&stmts[start..end], home) {
                windows.insert(start, end);
                if let Some((temp, HirExpr::Unary(_))) = stmts[start].scalar_temp_assignment() {
                    // 未读的元方法结果仍跨过窗口内调用；先物化这个已证根，
                    // 后层才能保留它的词法结束点，不能把无源码 local 的块展开。
                    self.root_results.insert(temp);
                }
                // 窗口中的原 CALL 结果仍占据对应槽；不能先丢掉未使用结果，
                // 再要求后续源码帧验证一个尚无声明的 Temp。只在这个已闭合窗口保留它。
                for stmt in &stmts[start..end] {
                    if let Some(targets) = exact_multi_call_home_targets(stmt, self.facts) {
                        self.root_results
                            .extend(targets.into_iter().map(|(temp, _)| temp));
                    }
                    if let Some((temp, HirExpr::Call(call))) = stmt.scalar_temp_assignment()
                        && let Some(frame) = self.facts.native_call_frame(call)
                        && self.facts.trusted_temp_home_slot(temp) == Some(frame.home)
                        && matches!(frame.results, Some(crate::transformer::ResultPack::Fixed(pack))
                            if pack.start.index() == frame.home.slot() && pack.len == 1)
                    {
                        self.root_results.insert(temp);
                    }
                }
            }
        }
        windows
    }
}

impl ScopePass<'_> {
    // 原 CLOSURE 与后继同槽新帧直接给出声明入口/末端；不删除创建或缩短物理根。
    // 窗口仍须通过调用下界和所有读写/capture 的闭合性证明。
    fn closure_root_at(&self, stmts: &[HirStmt], index: usize, home: HomeSlotKey) -> bool {
        let Some((temp, HirExpr::Closure(closure))) = stmts[index].scalar_temp_assignment() else {
            return false;
        };
        closure.creation.is_some()
            && self.facts.trusted_temp_home_slot(temp) == Some(home)
            && closure.source_site.is_some_and(|source| {
                self.facts.operation_result_temp(source) == Some(temp)
                    && self.facts.operation_result_home(source) == Some(home)
            })
    }

    /// nil 接收者、高槽分配与低槽 COPY 共同确定原声明入口，不从同槽末次写猜测对象身份。
    fn allocation_copy_start(
        &self,
        stmts: &[HirStmt],
        copy_index: usize,
        base: HomeSlotKey,
    ) -> Option<usize> {
        let start = copy_index.checked_sub(2)?;
        let (initial, HirExpr::Nil) = stmts[start].scalar_temp_assignment()? else {
            return None;
        };
        let (source, HirExpr::TableConstructor(table)) =
            stmts[start + 1].scalar_temp_assignment()?
        else {
            return None;
        };
        let (target, HirExpr::TempRef(read)) = stmts[copy_index].scalar_temp_assignment()? else {
            return None;
        };
        let [copy] = self.facts.trusted_immediate_moves(source)? else {
            return None;
        };
        (source == *read
            && self.facts.nil_write_temps(initial) == Some(&[initial][..])
            && self.facts.copy_overwrite_predecessor(target) == Some(initial)
            && copy.source == Some(source)
            && copy.target == target
            && copy.target_home == base
            && copy.source_home.slot() == base.slot() + 1
            && self.facts.allocation_result_home(table) == Some(copy.source_home)
            && self.facts.allocation_result_reference_unaliased(table))
        .then_some(start)
    }

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
                    // Boolean 预写没有出现在结果表达式的读取集合中，但仍属于同一个
                    // 参数准备事务。不能把它包进旧域，留下跨域的参数结果和 callee。
                    if let Some((initial, _, _, _)) = self.facts.boolean_value_prewrite(temp)
                        && let Some(definition) = definitions.get(&initial)
                    {
                        if let Some(index) = definition.filter(|index| *index < consumer) {
                            start = start.min(index);
                        } else {
                            valid = false;
                        }
                    }
                }
            }),
        );
        valid.then_some(start)
    }

    fn closed_window(&self, stmts: &[HirStmt], base: HomeSlotKey) -> bool {
        let mut definitions = BTreeSet::new();
        let mut entries = stmts.iter().rev().collect::<Vec<_>>();
        while let Some(stmt) = entries.pop() {
            match stmt {
                HirStmt::Assign(assign) => {
                    for target in &assign.targets {
                        if matches!(target, HirLValue::Upvalue(_))
                            && self.facts.upvalue_write_value(assign).is_some()
                        {
                            // 原 SETUPVAL 不声明窗口外的新 local；保持原位写入，RHS 的读取与捕获
                            // 仍参加整个窗口的闭合性验证。引用捕获的 cell 不从这里取得离域许可。
                            continue;
                        }
                        // 表写入不声明或重绑定 local；整个语句保持原顺序进入词法域，
                        // 其 base/key/value 读取仍参加下方闭合性检查。原写入布局必须可追溯，
                        // 不能把未知物理副作用当作仅有表达式读取的语句。
                        if let HirLValue::TableAccess(access) = target {
                            if self.facts.native_table_write_layout(access).is_none() {
                                return false;
                            }
                            if matches!(&access.base, HirExpr::TempRef(temp)
                                if self.facts.is_direct_table_seed_temp(*temp)
                                    && !definitions.contains(temp))
                                || matches!(&access.base, HirExpr::LocalRef(local)
                                    if self.facts.is_direct_table_seed_local(*local))
                            {
                                // 候选拒绝[LayerBoundary]：窗口外分配和窗口内字段写仍可能
                                // 属于同一构造事务；不能只把字段 CALL 包进新域，再迫使
                                // 构造器 owner 跨域移动旧声明。完整初始化先由其 owner 消费。
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
                // 原循环控制和 body 的写域已由 lifetime 索引核对；额外词法块不移动
                // dispatch 或关闭端点。body 中所有 Temp 定义仍参与下面的逃逸检查。
                // scope_loop_body 已核对 Break 只位于被整体包含的循环内；它不结束窗口。
                HirStmt::CallStmt(_) | HirStmt::Break => {}
                HirStmt::GenericFor(for_) => entries.extend(for_.body.stmts.iter().rev()),
                HirStmt::While(while_) => entries.extend(while_.body.stmts.iter().rev()),
                HirStmt::Repeat(repeat) => entries.extend(repeat.body.stmts.iter().rev()),
                // 两臂仍在原条件下执行；逐项验证其定义和表写来源，读取/捕获随后
                // 统一参与整个窗口的逃逸检查，不能只检查条件头或某一个分支。
                HirStmt::If(branch) => {
                    if let Some(body) = &branch.else_block {
                        entries.extend(body.stmts.iter().rev());
                    }
                    entries.extend(branch.then_block.stmts.iter().rev());
                }
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
                        .or_else(|| self.facts.native_fastcall_frame(call))
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
