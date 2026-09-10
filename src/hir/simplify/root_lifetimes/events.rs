//! 在递归入口冻结语句事件，根分析与 locals 的读取、touch、控制头查询共用原始域。
//!
//! 物理 home 来自 Promotion；读写、参数交接和 callee 来自 HIR header，词法域来自
//! HirStmtTree。先序位置只用于集合查询，不代表求值顺序；消费者把后代事件投影回
//! 直属语句，例如 `repeat t = f(t) until p(t)` 的所有 t 读写属于同一观察时点。
//! reads 只需成员关系，writes/参数 token 保留次数：同语句的两个写入也不能证明唯一来源。
//! 不复制后代集合，不进入 child proto，也不跨改写复用快照。改写后的块拥有相同索引，
//! 与未改写的共享子域使用同一套查询。
//! 潜在观察由入口固定的 HirExprSafety 与 HirEvalEffects 发布，显式 GC fence 另按别名解析。
//! local 事件保留原逻辑域：LocalDecl/Local lvalue/release 是写，loop binding 元数据不是写。
//! 例如 `local x=f(); side(); use(x)` 的候选必须读取完整后缀，不能从遇见 f 的位置才建状态。

use std::{collections::BTreeMap, ops::Range};

use super::{
    HomeSlotKey, LocalId, LocalUseCollector, ProtoPromotionFacts, StackWriteCollector,
    StackWriteSummary, TempId, TempWriteCollector,
};
use crate::hir::common::{HirCallExpr, HirExpr, HirStmt};
use crate::hir::expr_safety::{HirEvalEffects, HirExprSafety};
use crate::hir::simplify::lexical_cfg::{HirStmtId, HirStmtTree};
use crate::hir::simplify::temp_touch::TempReadCollector;
use crate::hir::visit::{HirVisitor, visit_stmt_header};

pub(in crate::hir::simplify) struct RootEventIndex {
    tree: HirStmtTree,
    writes: Vec<(usize, HomeSlotKey)>,
    by_home: BTreeMap<HomeSlotKey, Vec<usize>>,
    unknown: Vec<usize>,
    boundaries: Vec<usize>,
    by_temp: BTreeMap<TempId, TempEvents>,
    reads: Vec<(usize, TempId)>,
    temp_writes: Vec<(usize, TempId)>,
    argument_transfers: Vec<(usize, TempId)>,
    local_calls: BTreeMap<LocalId, Vec<usize>>,
    gc_calls: Vec<usize>,
    observations: Vec<usize>,
    by_local: BTreeMap<LocalId, LocalEvents>,
}

#[derive(Default)]
struct LocalEvents {
    reads: Vec<usize>,
    writes: Vec<usize>,
}

#[derive(Default)]
pub(super) struct TempEvents {
    pub(super) reads: Vec<usize>,
    pub(super) writes: Vec<usize>,
    pub(super) argument_transfers: Vec<usize>,
    calls: Vec<usize>,
}

impl RootEventIndex {
    pub(in crate::hir::simplify) fn new(
        stmts: &[HirStmt],
        facts: &ProtoPromotionFacts,
        safety: HirExprSafety,
    ) -> Self {
        let mut writes = Vec::new();
        let mut by_home = BTreeMap::<_, Vec<_>>::new();
        let mut unknown = Vec::new();
        let mut boundaries = Vec::new();
        let mut by_temp = BTreeMap::<TempId, TempEvents>::new();
        let mut read_events = Vec::new();
        let mut temp_writes = Vec::new();
        let mut argument_transfers = Vec::new();
        let mut local_calls = BTreeMap::<_, Vec<_>>::new();
        let mut gc_calls = Vec::new();
        let mut observations = Vec::new();
        let mut by_local = BTreeMap::<LocalId, LocalEvents>::new();
        let tree = HirStmtTree::build(stmts, &mut |id, stmt| {
            let mut summary = StackWriteSummary::default();
            let mut collector = (
                (TempReadCollector::default(), TempWriteCollector::default()),
                (
                    (
                        StackWriteCollector {
                            facts,
                            summary: &mut summary,
                        },
                        CalleeCollector::default(),
                    ),
                    (
                        LocalUseCollector::default(),
                        HirEvalEffects::new(safety, |stmt| matches!(stmt, HirStmt::GenericFor(_))),
                    ),
                ),
            );
            visit_stmt_header(stmt, &mut collector);
            let ((reads, temps), ((_, calls), (locals, effects))) = collector;
            let position = id.index();
            if effects.found() {
                observations.push(position);
            }
            for local in locals.reads {
                by_local.entry(local).or_default().reads.push(position);
            }
            for local in locals.writes {
                by_local.entry(local).or_default().writes.push(position);
            }
            for temp in reads.temps {
                by_temp.entry(temp).or_default().reads.push(position);
                read_events.push((position, temp));
            }
            for temp in temps.temps {
                by_temp.entry(temp).or_default().writes.push(position);
                temp_writes.push((position, temp));
            }
            for temp in temps.argument_transfers {
                by_temp
                    .entry(temp)
                    .or_default()
                    .argument_transfers
                    .push(position);
                argument_transfers.push((position, temp));
            }
            for temp in calls.temps {
                by_temp.entry(temp).or_default().calls.push(position);
            }
            for local in calls.locals {
                local_calls.entry(local).or_default().push(position);
            }
            if calls.gc {
                gc_calls.push(position);
            }
            for home in summary.homes {
                writes.push((position, home));
                by_home.entry(home).or_default().push(position);
            }
            if summary.has_unknown_home {
                unknown.push(position);
            }
            if summary.has_boundary {
                boundaries.push(position);
            }
        });
        Self {
            tree,
            writes,
            by_home,
            unknown,
            boundaries,
            by_temp,
            reads: read_events,
            temp_writes,
            argument_transfers,
            local_calls,
            gc_calls,
            observations,
            by_local,
        }
    }

    pub(in crate::hir::simplify) fn root(&self) -> RootEventBlock<'_> {
        RootEventBlock {
            index: self,
            stmts: self.tree.block(self.tree.root_block()),
            loop_transfer_prefix: self.tree.block_loop_transfer_prefix(self.tree.root_block()),
        }
    }
}

#[derive(Default)]
struct CalleeCollector {
    temps: Vec<TempId>,
    locals: Vec<LocalId>,
    gc: bool,
}

impl HirVisitor for CalleeCollector {
    fn visit_call(&mut self, call: &HirCallExpr) {
        match &call.callee {
            HirExpr::TempRef(temp) => self.temps.push(*temp),
            HirExpr::LocalRef(local) => self.locals.push(*local),
            HirExpr::GlobalRef(global) => self.gc |= global.key.as_bytes() == b"collectgarbage",
            _ => {}
        }
    }
}

#[derive(Clone, Copy)]
pub(in crate::hir::simplify) struct RootEventBlock<'a> {
    index: &'a RootEventIndex,
    stmts: &'a [HirStmtId],
    loop_transfer_prefix: &'a [usize],
}

impl<'a> RootEventBlock<'a> {
    pub(super) fn observation_indices(self) -> super::BTreeSet<usize> {
        (0..self.stmts.len())
            .filter(|&index| self.stmt(index).may_observe_gc_roots())
            .collect()
    }

    pub(super) fn has_local_read_at(self, local: LocalId, ordinal: usize) -> bool {
        self.index
            .by_local
            .get(&local)
            .is_some_and(|events| self.contains(&events.reads, ordinal))
    }

    /// 每个候选 local 独立逆扫完整后缀；嵌套事件仍投影成同一直属观察时点。
    pub(super) fn local_touch_positions_rev(
        self,
        local: LocalId,
    ) -> impl Iterator<Item = usize> + 'a {
        let mut until = self.stmts.len();
        std::iter::from_fn(move || {
            let events = self.index.by_local.get(&local)?;
            let index = self
                .previous(&events.reads, until)
                .into_iter()
                .chain(self.previous(&events.writes, until))
                .max()?;
            until = index;
            Some(index)
        })
    }

    fn previous(self, positions: &[usize], until: usize) -> Option<usize> {
        let end = self
            .index
            .tree
            .stmt(*self.stmts.get(until.checked_sub(1)?)?)
            .range
            .end;
        let last = positions
            .partition_point(|position| *position < end)
            .checked_sub(1)?;
        let position = positions[last];
        (position >= self.range().start).then(|| self.ordinal(position))
    }

    pub(in crate::hir::simplify) fn has_read_at(self, temp: TempId, ordinal: usize) -> bool {
        self.temp(temp)
            .is_some_and(|events| self.contains(&events.reads, ordinal))
    }

    pub(in crate::hir::simplify) fn reads_any(
        self,
        ordinal: usize,
        temps: &super::BTreeSet<TempId>,
    ) -> bool {
        let events = self.reads(ordinal);
        if events.len() < temps.len() {
            events.iter().any(|(_, temp)| temps.contains(temp))
        } else {
            temps.iter().any(|temp| self.has_read_at(*temp, ordinal))
        }
    }

    pub(in crate::hir::simplify) fn has_touch_in(self, temp: TempId, range: Range<usize>) -> bool {
        self.touch_positions_from(temp, range.start)
            .next()
            .is_some_and(|index| index < range.end)
    }

    pub(in crate::hir::simplify) fn has_touch_before(self, temp: TempId, ordinal: usize) -> bool {
        self.has_touch_in(temp, 0..ordinal)
    }

    pub(in crate::hir::simplify) fn has_touch_from(self, temp: TempId, ordinal: usize) -> bool {
        self.touch_positions_from(temp, ordinal).next().is_some()
    }

    /// 每次跳过整条直属语句的全部后代，读写重合仍只发布一个 ordinal。
    pub(in crate::hir::simplify) fn touch_positions_from(
        self,
        temp: TempId,
        mut from: usize,
    ) -> impl Iterator<Item = usize> + 'a {
        std::iter::from_fn(move || {
            let events = self.temp(temp)?;
            let index = self
                .next(&events.reads, from)
                .into_iter()
                .chain(self.next(&events.writes, from))
                .min()?;
            from = index + 1;
            Some(index)
        })
    }

    pub(in crate::hir::simplify) fn stmt(self, ordinal: usize) -> RootEventStmt<'a> {
        RootEventStmt {
            index: self.index,
            stmt: self.stmts[ordinal],
        }
    }

    pub(super) fn prefix(self, len: usize) -> Self {
        self.slice(0..len)
    }

    pub(in crate::hir::simplify) fn slice(self, range: Range<usize>) -> Self {
        Self {
            stmts: &self.stmts[range.clone()],
            loop_transfer_prefix: &self.loop_transfer_prefix[range.start..=range.end],
            ..self
        }
    }

    pub(super) fn has_boundary(self) -> bool {
        self.loop_transfer_prefix.first() != self.loop_transfer_prefix.last()
            || contains_position(&self.index.boundaries, &self.range())
    }

    pub(super) fn has_unknown_home(self) -> bool {
        contains_position(&self.index.unknown, &self.range())
    }

    pub(in crate::hir::simplify) fn preserves_home(self, home: HomeSlotKey) -> bool {
        !self.has_boundary()
            && !self.has_unknown_home()
            && !self
                .index
                .by_home
                .get(&home)
                .is_some_and(|positions| contains_position(positions, &self.range()))
    }

    pub(super) fn home_write_positions_from(
        self,
        home: HomeSlotKey,
        mut from: usize,
    ) -> impl Iterator<Item = usize> + 'a {
        std::iter::from_fn(move || {
            let positions = self.index.by_home.get(&home)?;
            let index = self.next(positions, from)?;
            from = index + 1;
            Some(index)
        })
    }

    fn range(self) -> Range<usize> {
        self.stmts.first().map_or(0..0, |first| {
            first.index()..self.index.tree.stmt(*self.stmts.last().unwrap()).range.end
        })
    }

    pub(super) fn temp(self, temp: TempId) -> Option<&'a TempEvents> {
        self.index.by_temp.get(&temp)
    }

    pub(super) fn positions(self, positions: &'a [usize]) -> &'a [usize] {
        in_range(positions, &self.range())
    }

    pub(super) fn ordinal(self, position: usize) -> usize {
        self.stmts.partition_point(|stmt| stmt.index() <= position) - 1
    }

    pub(super) fn next(self, positions: &[usize], ordinal: usize) -> Option<usize> {
        let start = self.stmts.get(ordinal)?.index();
        positions
            .get(positions.partition_point(|position| *position < start))
            .copied()
            .filter(|position| *position < self.range().end)
            .map(|position| self.ordinal(position))
    }

    pub(super) fn contains(self, positions: &[usize], ordinal: usize) -> bool {
        self.stmts
            .get(ordinal)
            .is_some_and(|stmt| contains_position(positions, &self.index.tree.stmt(*stmt).range))
    }

    pub(super) fn reads(self, ordinal: usize) -> &'a [(usize, TempId)] {
        self.events_at(&self.index.reads, ordinal)
    }

    pub(super) fn argument_transfers(self, ordinal: usize) -> &'a [(usize, TempId)] {
        self.events_at(&self.index.argument_transfers, ordinal)
    }

    fn events_at<T>(self, events: &'a [(usize, T)], ordinal: usize) -> &'a [(usize, T)] {
        let range = &self.index.tree.stmt(self.stmts[ordinal]).range;
        events_in_range(events, range)
    }

    pub(super) fn is_gc_fence(
        self,
        ordinal: usize,
        temps: &super::BTreeSet<TempId>,
        locals: &super::BTreeSet<LocalId>,
    ) -> bool {
        self.contains(&self.index.gc_calls, ordinal)
            || temps.iter().any(|temp| {
                self.temp(*temp)
                    .is_some_and(|events| self.contains(&events.calls, ordinal))
            })
            || locals.iter().any(|local| {
                self.index
                    .local_calls
                    .get(local)
                    .is_some_and(|events| self.contains(events, ordinal))
            })
    }
}

#[derive(Clone, Copy)]
pub(in crate::hir::simplify) struct RootEventStmt<'a> {
    index: &'a RootEventIndex,
    stmt: HirStmtId,
}

impl<'a> RootEventStmt<'a> {
    pub(super) fn may_observe_gc_roots(self) -> bool {
        contains_position(
            &self.index.observations,
            &self.index.tree.stmt(self.stmt).range,
        )
    }

    pub(super) fn writes_local_in_header(self, local: LocalId) -> bool {
        self.index.by_local.get(&local).is_some_and(|events| {
            contains_position(&events.writes, &(self.stmt.index()..self.stmt.index() + 1))
        })
    }

    /// 只证明当前控制头消费，body 的任何逻辑读写都会拒绝；不解释控制可达性。
    pub(in crate::hir::simplify) fn consumes_only_control_head(
        self,
        stmt: &HirStmt,
        temps: &super::BTreeSet<TempId>,
    ) -> bool {
        if !matches!(
            stmt,
            HirStmt::If(_)
                | HirStmt::While(_)
                | HirStmt::Repeat(_)
                | HirStmt::NumericFor(_)
                | HirStmt::GenericFor(_)
        ) {
            return false;
        }
        let range = &self.index.tree.stmt(self.stmt).range;
        let head = events_in_range(&self.index.reads, &(range.start..range.start + 1));
        if !head.iter().any(|(_, temp)| temps.contains(temp)) {
            return false;
        }
        let body = range.start + 1..range.end;
        let reads = events_in_range(&self.index.reads, &body);
        let writes = events_in_range(&self.index.temp_writes, &body);
        if reads.len() + writes.len() < temps.len() {
            !reads
                .iter()
                .chain(writes)
                .any(|(_, temp)| temps.contains(temp))
        } else {
            !temps.iter().any(|temp| {
                self.index.by_temp.get(temp).is_some_and(|events| {
                    contains_position(&events.reads, &body)
                        || contains_position(&events.writes, &body)
                })
            })
        }
    }

    pub(in crate::hir::simplify) fn child(self, ordinal: usize) -> RootEventBlock<'a> {
        let block = self.index.tree.stmt(self.stmt).children[ordinal];
        RootEventBlock {
            index: self.index,
            stmts: self.index.tree.block(block),
            loop_transfer_prefix: self.index.tree.block_loop_transfer_prefix(block),
        }
    }

    pub(super) fn has_boundary(self) -> bool {
        let scope = self.index.tree.stmt(self.stmt);
        scope.has_external_loop_transfer || contains_position(&self.index.boundaries, &scope.range)
    }

    pub(super) fn has_unknown_home(self) -> bool {
        contains_position(&self.index.unknown, &self.index.tree.stmt(self.stmt).range)
    }

    pub(super) fn contains_home(self, home: HomeSlotKey) -> bool {
        self.index.by_home.get(&home).is_some_and(|positions| {
            contains_position(positions, &self.index.tree.stmt(self.stmt).range)
        })
    }

    /// 只枚举较小的写事件或待失效 home 域，纯调用不为查询而扫描全部活动根。
    pub(super) fn intersection<I: Iterator<Item = HomeSlotKey>>(
        self,
        candidate_count: usize,
        candidates: impl FnOnce() -> I,
        contains: impl Fn(HomeSlotKey) -> bool,
    ) -> super::BTreeSet<HomeSlotKey> {
        let range = &self.index.tree.stmt(self.stmt).range;
        let events = events_in_range(&self.index.writes, range);
        if events.len() < candidate_count {
            events
                .iter()
                .map(|(_, home)| *home)
                .filter(|home| contains(*home))
                .collect()
        } else {
            candidates()
                .filter(|home| self.contains_home(*home))
                .collect()
        }
    }
}

fn in_range<'a>(positions: &'a [usize], range: &Range<usize>) -> &'a [usize] {
    let start = positions.partition_point(|position| *position < range.start);
    let end = positions.partition_point(|position| *position < range.end);
    &positions[start..end]
}

fn contains_position(positions: &[usize], range: &Range<usize>) -> bool {
    positions
        .get(positions.partition_point(|position| *position < range.start))
        .is_some_and(|position| *position < range.end)
}

fn events_in_range<'a, T>(events: &'a [(usize, T)], range: &Range<usize>) -> &'a [(usize, T)] {
    let start = events.partition_point(|(position, _)| *position < range.start);
    let end = events.partition_point(|(position, _)| *position < range.end);
    &events[start..end]
}
