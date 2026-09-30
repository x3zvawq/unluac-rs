//! 在原槽被下一次调用准备覆盖时，恢复匿名声明的词法末端。
//!
//! 根的保活与覆盖来自共享 lifetime 分析；窗口内身份不得逃逸。先结束旧声明，
//! 避免 promotion 把后继 callee 合入旧 local 后永久占据它自己的调用准备槽。

use super::*;
use crate::hir::common::HirCallExpr;
use crate::hir::simplify::mention::BindingReadCollector;
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
        // 窗口只能结束于本块的直接调用准备。纯分支不自行建窗，避免每层嵌套 if
        // 重复索引同一子树；包含调用的子域会在下面的分支边界检查中截断父级扫描。
        if !block
            .stmts
            .iter()
            .any(|stmt| direct_call_in_stmt(stmt).is_some())
        {
            return false;
        }
        if block.stmts.iter().any(|stmt| {
            !scope_statement(stmt) && !matches!(stmt, HirStmt::ToBeClosed(_) | HirStmt::Close(_))
        }) {
            // MissingFact：SETLIST 和未支持的控制结构可能仍属于跨语句协议。
            // 不能把未知节点当成可切分边界，截断在其两侧继续构造的表达式帧。
            return false;
        }
        let mut windows = BTreeMap::new();
        let mut start = 0;
        for end in 0..=block.stmts.len() {
            if end < block.stmts.len() && scope_statement(&block.stmts[end]) {
                continue;
            }
            if start < end {
                windows.extend(
                    self.scope_windows(&block.stmts[start..end])
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
/// 显式资源激活/关闭分隔候选区，未支持结构保留整个块；每条语句至多在自身及父区各索引一次。
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
        let mut windows = BTreeMap::new();
        let call_floors = CallFloors::new(stmts, self.facts);
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
            if !matches!(stmt, HirStmt::Assign(_) | HirStmt::CallStmt(_)) {
                continue;
            }
            let Some(call) = direct_call_in_stmt(stmt) else {
                continue;
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
            // 多结果只能连同全部目标结束；不能把同一次 CALL 的 owner 拆成独立词法块。
            if literal_start.is_none() {
                // 一个宽返回组可能在多个 home 上陆续被覆盖；先按原 CALL 排除非首结果，
                // 避免为每个成员的候选重复展开整组目标。
                if let Some(producer) = direct_call_in_stmt(&stmts[start])
                    && let Some(original) = self.facts.native_call_frame(producer)
                    && original.home == frame.home
                    && let Some(targets) = exact_multi_call_home_targets(&stmts[start], self.facts)
                {
                    if !matches!(original.results, Some(crate::transformer::ResultPack::Fixed(pack))
                                if pack.start.index() == frame.home.slot() && pack.len == targets.len())
                        || targets
                            .iter()
                            .enumerate()
                            .any(|(offset, (_, home))| home.slot() != frame.home.slot() + offset)
                        || call_floors.minimum(start + 1, end) < frame.home.slot() + targets.len()
                    {
                        // 候选拒绝[ProofIncomplete]：所有结果必须共同占据原低槽前缀，窗口内调用不能复用其中一员。
                        continue;
                    }
                    let Some(preparation) =
                        self.preparation_start(producer, frame.home, start, &definitions)
                    else {
                        continue;
                    };
                    start = preparation;
                } else if let Some((result, value)) = stmts[start].scalar_temp_assignment() {
                    if self.facts.trusted_temp_home_slot(result) != Some(frame.home) {
                        continue;
                    }
                    match value {
                        HirExpr::Call(producer) => {
                            if self.facts.native_call_frame(producer).is_none_or(|producer|
                            producer.home != frame.home
                                || !matches!(producer.results, Some(crate::transformer::ResultPack::Fixed(pack))
                                    if pack.start.index() == frame.home.slot() && pack.len == 1))
                        {
                            continue;
                        }
                            if self.reads.get(&result) == Some(&1)
                                && call_floors.minimum(start + 1, end) <= frame.home.slot()
                            {
                                // 候选拒绝[LayerBoundary]：单次使用的结果遇到较低/同槽调用时，
                                // 尚不能证明独立声明域；完整外层调用准备应由帧 owner 消费。
                                // 多次使用的源码结果可在最后一次调用时交出根，不由此拒绝。
                                continue;
                            }
                            // callee COPY 与嵌套参数的尚存准备必须一起进入旧域；FASTCALL 的
                            // 参数也可能先于 callee。完整调用仍由帧 owner 重建。
                            let Some(preparation) =
                                self.preparation_start(producer, frame.home, start, &definitions)
                            else {
                                continue;
                            };
                            start = preparation;
                        }
                        HirExpr::TableConstructor(table)
                            if self.facts.allocation_result_home(table) == Some(frame.home) =>
                        {
                            let floor = call_floors.minimum(start, end);
                            if floor == usize::MAX || floor <= frame.home.slot() {
                                // 候选拒绝[LayerBoundary]：没有跨调用的低槽对象身份时，
                                // 分配仍属于高槽字段/参数准备，交完整构造器或调用帧消费。
                                continue;
                            }
                        }
                        HirExpr::TempRef(_) => {
                            let Some(initializer) =
                                self.allocation_copy_start(stmts, start, frame.home)
                            else {
                                continue;
                            };
                            if call_floors.minimum(initializer, end) <= frame.home.slot() {
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
            if literal_start.is_some() && call_floors.minimum(start, end) <= frame.home.slot() {
                // 常量不承载独立 GC 身份；其词法槽仍须在窗口中的每次调用下方。
                // 若中途调用已复用该槽，不能把原准备临时量猜成跨调用声明。
                // 这类参数准备不是可扫描窗口，不能推进 scanned 而屏蔽外围完整结果域。
                continue;
            }
            // 闭合性扫描不重复覆盖旧窗口；调用下界查询独立走区间索引，嵌套的
            // 失败参数候选不会反复遍历大段语句，也不会抢占真正的作用域候选。
            scanned = end;
            if self.closed_window(&stmts[start..end], frame.home) {
                windows.insert(start, end);
                // 窗口中的原 CALL 结果仍占据对应槽；不能先丢掉未使用结果，
                // 再要求后续源码帧验证一个尚无声明的 Temp。只在这个已闭合窗口保留它。
                for stmt in &stmts[start..end] {
                    if let Some(targets) = exact_multi_call_home_targets(stmt, self.facts) {
                        self.call_results
                            .extend(targets.into_iter().map(|(temp, _)| temp));
                    }
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
        windows
    }
}

impl ScopePass<'_> {
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
