//! 这个文件识别普通 HIR 值活跃性看不到的物理槽 root 生命周期。
//!
//! fixed call result（包括已物化 local）、table allocation，以及已跨后续观察点的
//! table/global lookup 与动态运算结果，即使没有 HIR 读取，也会在同一 stack home 被覆盖前继续充当
//! VM GC root。ordinary call 的参数槽由前层标记交接给 callee，只有当前唯一 producer 与
//! call 参数端点仍匹配时才退休 call/lookup/allocation 的对应 home，不能把 callee 可覆盖的槽
//! 物化为额外 caller local。例如 `object = make(); f(object)` 的参数副本结束于 f，原槽
//! 则仍需保活至自己的覆盖点；两者共享值身份，不共享物理根终点。
//! 内嵌 method lookup/call 保留原 SELF 配对时，callee 槽已覆盖旧 receiver，首参另行
//! 交接；`subject.worker:touch()` 不把已结束的低槽根延续到下一次字段读取。显式 local
//! receiver 的异槽根和已经签发的独立保活事务不由这条协议退休。
//! Promotion 另会发布普通 copy root 的单结果 call + 紧邻 MOVE 终点；本层只按 producer / endpoint
//! temp 与 overwritten home 完整匹配，把它接入同一 local-owner handoff，不从 HIR 相邻文本猜 opcode。
//! 参数 COPY 也消费已有精确覆盖证书：`copy=parameter; weak[1]=copy; lookup(); copy=nil`
//! 中 lookup 可改写 parameter，故 copy 必须作为独立根保持到原 nil；先前槽为 nil 不免除这项义务。
//! allocation 的原覆盖配对不依赖当时是否逃逸：`t={child={}}; publish(t.child)` 中
//! 子表可以晚于旧槽覆盖才被外部观察。是否消除独立物化由消费事务的完整证明决定。
//! copy 共享值 identity，
//! 但每个目标 home 都是独立 root transaction；同一 parallel overwrite 可终止多个 home，
//! 消费者只能把 producer 与同 home 的精确覆盖配对。
//! 已物化的槽每次写入后继续到新值自己的覆盖点，call/copy/allocation 共用此链；
//! `call result -> LocalRef -> callee MOVE` 不需要证明三个值相等。
//! 分析只在单个 block 内追踪；只有 nested structure 不写 active home，且没有 opaque transfer
//! 或 cleanup 边界时才允许穿过。循环内的 break/continue 由共享 HIR 词法树判定归属，
//! 不清除循环外 home 的配对。消费者可以保留已配对的两次 materialization，也可以在
//! 更窄的改写仍保持同一覆盖事务时，连同 owner 已证明的 physical home 一起消费该 pair。
//! 同值 frame-end copy 的覆盖证明同时消费前层非资源旧值与两个完整 root transaction，
//! 并复核当前 HIR 未改写 home；删除副本的 owner 必须物化原值根，不能只抹掉负向标记。
//! 潜在求值事件与分支覆盖值的 GC 惰性统一消费入口按目标方言构造的表达式安全上下文。
//! 同一语句快照的读写、参数交接与 GC fence 索引由 RootLifetimeFacts 共享；借用期间
//! 不允许改写语句，例如 locals 可用同一快照分别配对 call 与 lookup 的覆盖端点。
//! 两类端点共用 producer/home 身份，前缀查询只投影已保活且在边界前正向闭合的事务；
//! locals 据此建立一次成员索引，不按每个候选重扫语句前缀。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirAssign, HirBinaryOpKind, HirBinding, HirBlock, HirCallExpr, HirExpr,
    HirGenericForDispatchRelease, HirLValue, HirSourceSite, HirStmt, HirUnaryOpKind, HirValuePack,
    LocalId, ParamId, TempId,
};
use crate::hir::expr_safety::{HirEvalEffects, HirExprSafety};
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

mod allocation_homes;
mod call_values;
mod events;
mod live_read_changes;
mod lookup_values;
mod return_roots;

use allocation_homes::{ActiveAllocationHome, AllocationHomes, AllocationSite};
use call_values::CallValues;
pub(super) use events::{RootEventBlock, RootEventIndex, RootEventStmt};
use lookup_values::ScalarValues;

use crate::hir::visit::{HirVisitor, visit_expr, visit_stmts};

/// 当前语句中必须只有一个仍匹配 producer 的参数交接端点；共享给内联和身份物化。
pub(super) fn stmt_has_argument_root_handoff(stmt: &HirStmt, temp: TempId) -> bool {
    struct Handoffs {
        temp: TempId,
        count: usize,
    }
    impl HirVisitor<'_> for Handoffs {
        fn visit_call(&mut self, call: &HirCallExpr) {
            self.count += usize::from(call.transfers_argument_root(self.temp));
        }
    }
    let mut handoffs = Handoffs { temp, count: 0 };
    visit_stmts(std::slice::from_ref(stmt), &mut handoffs);
    handoffs.count == 1
}

struct ActiveCallRoot {
    value_id: CallValueId,
    root_index: usize,
    eligible: bool,
    observed: bool,
    preserved: bool,
    explicit_fence_only: bool,
    /// 参数已交给 callee，不再选择 caller 根；若 producer 仍被独立物化，需保留原覆写终点。
    transferred: bool,
}

#[derive(Clone, Copy)]
struct PendingCopyRootCallMove {
    root_index: usize,
    producer: TempId,
    endpoint: TempId,
}

#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
struct CallValueId(usize);

#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
struct ScalarValueId(usize);

struct ActiveScalarGcHome {
    value_id: ScalarValueId,
    root_index: usize,
    aliases: BTreeSet<TempId>,
    eligible: bool,
    crossed_observation: bool,
    /// 写入本身清除了 CALL 残值，不能仅按新值是否被 GC 观察判定可删除。
    required_scratch_write: bool,
    /// 该 home 由原始表达式结果写入；跨 home 的机械 copy 不是 return 后缀要保留的独立 owner。
    direct_result_home: bool,
    /// low CFG 已证明该原始 home 在观察事件后仍活到 frame end。
    scope_end_copy_root: bool,
    /// 所有动态路径都到 frame end，不需要同步提交更早的 overwrite endpoint。
    pure_scope_end_copy_root: bool,
    /// low CFG 已证明观察期间保活并以精确 overwrite 结束；只用于同-home 覆盖配对。
    has_overwrite_proof: bool,
}

#[derive(Clone, Copy)]
struct AllocationHomeOwner {
    definition_index: usize,
    eligible: bool,
}

struct ExactNilHomeOverwrite {
    temps: BTreeSet<TempId>,
    home: HomeSlotKey,
    eligible: bool,
}

struct ExactHomeOverwrite {
    temps: BTreeSet<TempId>,
    eligible: bool,
}

/// 覆盖证明与源码身份分开：新 debug 声明只结束已有 owner，不能驱动匿名根物化或同名复用。
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum RootOverwritePolicy {
    Reject,
    ReleaseExisting,
    Reuse,
}

#[derive(Default)]
pub(super) struct CallRootLifetimeIndices {
    roots: BTreeSet<usize>,
    root_homes: BTreeMap<usize, BTreeSet<HomeSlotKey>>,
    roots_by_overwrite: BTreeMap<usize, Vec<PhysicalRootOwner>>,
    retained_overwrites: BTreeSet<usize>,
    continuation_owners: BTreeMap<usize, PhysicalRootOwner>,
    call_dispatch_releases: BTreeMap<usize, Vec<PhysicalRootOwner>>,
    overwrite_releases: BTreeMap<usize, Vec<PhysicalRootOwner>>,
    pre_dispatch_releases: BTreeMap<usize, BTreeSet<(TempId, HomeSlotKey)>>,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct PhysicalRootOwner {
    root_index: usize,
    home: HomeSlotKey,
}

/// HIR 已证明可由另一个 scope-end owner 接管的 method receiver 物理根事务。
///
/// statement 索引只在签发时的同一 block 坐标系内有效；消费者必须原子改写 producer、lookup
/// 与 sink，不能把这份证明提升成 `TempId` 级通用删除许可。
#[derive(Clone, Copy)]
pub(super) struct MethodReceiverRootHandoff {
    producer_index: usize,
    lookup_index: usize,
    sink_index: usize,
    overwrite_index: usize,
    target: TempId,
    source: TempId,
    target_home: HomeSlotKey,
    source_home: HomeSlotKey,
}

#[derive(Default)]
pub(super) struct ScalarGcRootLifetimeIndices {
    roots: BTreeSet<usize>,
    roots_by_overwrite: BTreeMap<usize, Vec<PhysicalRootOwner>>,
    retained_overwrites: BTreeSet<usize>,
    call_dispatch_releases: BTreeMap<usize, Vec<PhysicalRootOwner>>,
    handoff_roots: BTreeSet<TempId>,
}

/// 收集已经物化成 HIR local、但在最后一次显式读取后仍跨过潜在用户代码/GC 事件的
/// fixed call result。
///
/// 当前或后续语句仍有同一 value epoch 的读取时，已有 binding/use owner 会保留该 local；
/// 这里专门补足最后一次读取已经结束、但物理槽仍保活的后缀。这样不会阻断安全的
/// `local x = a:m(); x:n()` 链化，而 `local x = a:m(); x:n(); side()` 会保留词法 root。
pub(super) fn collect_call_result_local_roots(
    stmts: &[HirStmt],
    events: RootEventBlock<'_>,
    trailing_condition: Option<&HirExpr>,
    safety: HirExprSafety,
) -> BTreeSet<LocalId> {
    // 不同 local 的后缀状态互不影响；只请求最终能发布 root 的直属 call-result 候选。
    // 必须逆扫候选的完整后缀，不能从逆序第一次遇见 producer 才开始跟踪读取。
    let candidates = stmts
        .iter()
        .filter_map(direct_call_result_local)
        .collect::<BTreeSet<_>>();
    if candidates.is_empty() {
        return BTreeSet::new();
    }
    let explicit_fences = collect_gc_fences(stmts, events);
    let mut observations = events.observation_indices();
    let mut trailing_uses = LocalUseCollector::default();
    if let Some(condition) = trailing_condition {
        if !safety.is_discard_safe_without_residual(condition) {
            observations.insert(stmts.len());
        }
        visit_expr(condition, &mut trailing_uses);
    }
    let mut roots = BTreeSet::new();
    for local in candidates {
        let has_live_read = trailing_uses.reads.contains(&local);
        let mut state = LocalRootSuffix {
            next_event: stmts.len() + usize::from(!has_live_read),
            has_live_read,
            observed: false,
        };
        for index in events.local_touch_positions_rev(local) {
            let stmt = &stmts[index];
            let gap = index + 1..state.next_event;
            state.observed |= explicit_fences.range(gap.clone()).next().is_some()
                || (!state.has_live_read && observations.range(gap).next().is_some());
            // nested write 改变 future-read，但只有原先允许的直属覆盖才结束 call owner。
            if matches!(
                stmt,
                HirStmt::Assign(_) | HirStmt::LocalDecl(_) | HirStmt::LocalRootRelease(_)
            ) && events.stmt(index).writes_local_in_header(local)
            {
                if direct_call_result_local(stmt) == Some(local) && state.observed {
                    roots.insert(local);
                    break;
                }
                state.observed = false;
            }
            // 当前 RHS 仍可观察旧值；先消费新值后缀，再处理当前语句观察，同句读优先。
            state.has_live_read = events.has_local_read_at(local, index);
            state.observed |= explicit_fences.contains(&index)
                || (!state.has_live_read && observations.contains(&index));
            state.next_event = index;
        }
    }
    roots
}

fn direct_call_result_local(stmt: &HirStmt) -> Option<LocalId> {
    match stmt {
        HirStmt::Assign(assign) => match (
            assign.targets.as_slice(),
            assign.values.fixed.as_slice(),
            &assign.values.tail,
        ) {
            ([HirLValue::Local(local)], [HirExpr::Call(_)], None) => Some(*local),
            _ => None,
        },
        HirStmt::LocalDecl(decl) => match (
            decl.bindings.as_slice(),
            decl.values.fixed.as_slice(),
            &decl.values.tail,
        ) {
            ([local], [HirExpr::Call(_)], None) => Some(*local),
            _ => None,
        },
        _ => None,
    }
}

impl PhysicalRootOwner {
    pub(super) fn root_index(self) -> usize {
        self.root_index
    }

    pub(super) fn home(self) -> HomeSlotKey {
        self.home
    }
}

impl MethodReceiverRootHandoff {
    pub(super) fn producer_index(self) -> usize {
        self.producer_index
    }

    pub(super) fn lookup_index(self) -> usize {
        self.lookup_index
    }

    pub(super) fn sink_index(self) -> usize {
        self.sink_index
    }

    pub(super) fn overwrite_index(self) -> usize {
        self.overwrite_index
    }

    pub(super) fn target(self) -> TempId {
        self.target
    }

    pub(super) fn source(self) -> TempId {
        self.source
    }

    pub(super) fn target_home(self) -> HomeSlotKey {
        self.target_home
    }

    pub(super) fn source_home(self) -> HomeSlotKey {
        self.source_home
    }
}

impl CallRootLifetimeIndices {
    pub(super) fn closed_roots_before(
        &self,
        end: usize,
    ) -> impl Iterator<Item = PhysicalRootOwner> {
        root_owners_before(&self.roots_by_overwrite, end)
            .filter(|owner| self.owner_is_preserved(*owner))
    }

    fn preserve_call_root(&mut self, root: &ActiveCallRoot, home: HomeSlotKey) {
        if root.transferred {
            return;
        }
        self.roots.insert(root.root_index);
        self.root_homes
            .entry(root.root_index)
            .or_default()
            .insert(home);
    }

    pub(super) fn is_root(&self, index: usize) -> bool {
        self.roots.contains(&index)
    }

    pub(super) fn root_homes(&self, index: usize) -> impl Iterator<Item = HomeSlotKey> + '_ {
        self.root_homes.get(&index).into_iter().flatten().copied()
    }

    pub(super) fn overwrite_pair_for_home(
        &self,
        index: usize,
        home: HomeSlotKey,
    ) -> Option<PhysicalRootOwner> {
        self.overwrite_pairs(index).find(|pair| pair.home == home)
    }

    /// 精确 home 终点独立于保活选择；已物化 owner 可消费，不能据此强制物化 producer。
    pub(super) fn owner_overwrites(
        &self,
        index: usize,
    ) -> impl Iterator<Item = PhysicalRootOwner> + '_ {
        self.roots_by_overwrite
            .get(&index)
            .into_iter()
            .flatten()
            .copied()
    }

    pub(super) fn overwrite_pairs(
        &self,
        index: usize,
    ) -> impl Iterator<Item = PhysicalRootOwner> + '_ {
        self.owner_overwrites(index)
            .filter(|owner| self.owner_is_preserved(*owner))
    }

    /// 返回该 statement 唯一的受保护 root overwrite 事务，保留 overwritten home 身份。
    pub(super) fn unambiguous_overwrite_pair(&self, index: usize) -> Option<PhysicalRootOwner> {
        let mut pairs = self.overwrite_pairs(index);
        let pair = pairs.next()?;
        pairs.next().is_none().then_some(pair)
    }

    /// 同 home 的同值写回继承原 owner；身份事实不依赖之后是否签发保活或覆盖许可。
    pub(super) fn continuation_owner(&self, index: usize) -> Option<PhysicalRootOwner> {
        self.continuation_owners.get(&index).copied()
    }

    /// 异值新声明的结束端点；只交给已物化 owner，不能作为匿名根的保活或复用许可。
    pub(super) fn overwrite_releases(
        &self,
        index: usize,
    ) -> impl Iterator<Item = PhysicalRootOwner> + '_ {
        self.overwrite_releases
            .get(&index)
            .into_iter()
            .flatten()
            .copied()
    }

    pub(super) fn call_dispatch_releases(
        &self,
        index: usize,
    ) -> impl Iterator<Item = PhysicalRootOwner> + '_ {
        self.call_dispatch_releases
            .get(&index)
            .into_iter()
            .flatten()
            .copied()
    }

    pub(super) fn owner_is_preserved(&self, owner: PhysicalRootOwner) -> bool {
        self.root_homes
            .get(&owner.root_index)
            .is_some_and(|homes| homes.contains(&owner.home))
    }

    pub(super) fn marked_stmts(&self, stmt_count: usize) -> Vec<bool> {
        let mut marked = vec![false; stmt_count];
        for index in self
            .roots
            .iter()
            .chain(&self.retained_overwrites)
            .chain(
                self.roots_by_overwrite
                    .iter()
                    .filter_map(|(index, owners)| {
                        owners
                            .iter()
                            .any(|owner| self.owner_is_preserved(*owner))
                            .then_some(index)
                    }),
            )
            .chain(
                self.continuation_owners
                    .iter()
                    .filter_map(|(index, owner)| self.owner_is_preserved(*owner).then_some(index)),
            )
        {
            marked[*index] = true;
        }
        marked
    }

    /// 签发由 distinct pure scope-end owner 覆盖的 method receiver root handoff。
    ///
    /// 这里组合 allocation-root producer/overwrite pair、direct SSA copy、trusted homes 与
    /// method-setup 双 use 协议，冻结 HIR/VM 生命周期事实。debug/capture/TBC/disposition 等
    /// “是否允许删除当前 definition”条件仍由具体 rewrite owner 在提交前检查。
    pub(super) fn method_receiver_handoffs(
        &self,
        stmts: &[HirStmt],
        facts: &ProtoPromotionFacts,
        mut preserves_home: impl FnMut(std::ops::Range<usize>, HomeSlotKey) -> bool,
    ) -> Vec<MethodReceiverRootHandoff> {
        // None 表示不同位置都覆盖此 owner；同一位置的重复记录不改变唯一性。
        let mut unique_overwrites = BTreeMap::new();
        for (&index, owners) in &self.roots_by_overwrite {
            for &owner in owners {
                unique_overwrites
                    .entry(owner)
                    .and_modify(|prior| {
                        if *prior != Some(index) {
                            *prior = None;
                        }
                    })
                    .or_insert(Some(index));
            }
        }
        let mut handoffs = Vec::new();
        for producer_index in 0..stmts.len() {
            let Some((target, HirExpr::TempRef(source))) =
                stmts[producer_index].scalar_temp_assignment()
            else {
                continue;
            };
            if !self.is_root(producer_index) || !facts.is_pure_scope_end_copy_root_temp(*source) {
                continue;
            }

            let (Some(target_home), Some(source_home)) = (
                facts.trusted_temp_home_slot(target),
                facts.trusted_temp_home_slot(*source),
            ) else {
                continue;
            };
            if target_home == source_home
                || !self
                    .root_homes(producer_index)
                    .any(|home| home == target_home)
            {
                continue;
            }

            let Some(Some(overwrite_index)) = unique_overwrites.get(&PhysicalRootOwner {
                root_index: producer_index,
                home: target_home,
            }) else {
                continue;
            };
            let Some((lookup_index, sink_index)) =
                method_receiver_protocol_sink(stmts, producer_index + 1, *overwrite_index, target)
            else {
                continue;
            };

            if !preserves_home(producer_index + 1..sink_index + 1, source_home) {
                continue;
            }

            handoffs.push(MethodReceiverRootHandoff {
                producer_index,
                lookup_index,
                sink_index,
                overwrite_index: *overwrite_index,
                target,
                source: *source,
                target_home,
                source_home,
            });
        }
        handoffs
    }
}

impl ScalarGcRootLifetimeIndices {
    pub(super) fn call_dispatch_releases(
        &self,
        index: usize,
    ) -> impl Iterator<Item = PhysicalRootOwner> + '_ {
        self.call_dispatch_releases
            .get(&index)
            .into_iter()
            .flatten()
            .copied()
    }

    pub(super) fn closed_roots_before(
        &self,
        end: usize,
    ) -> impl Iterator<Item = PhysicalRootOwner> {
        root_owners_before(&self.roots_by_overwrite, end)
            .filter(|owner| self.is_root(owner.root_index))
    }

    pub(super) fn handoff_roots(&self) -> impl Iterator<Item = TempId> + '_ {
        self.handoff_roots.iter().copied()
    }

    pub(super) fn is_root(&self, index: usize) -> bool {
        self.roots.contains(&index)
    }

    pub(super) fn overwrite_pair_for_home(
        &self,
        index: usize,
        home: HomeSlotKey,
    ) -> Option<PhysicalRootOwner> {
        self.roots_by_overwrite
            .get(&index)?
            .iter()
            .find(|pair| pair.home == home)
            .copied()
    }

    pub(super) fn overwrite_pairs(
        &self,
        index: usize,
    ) -> impl Iterator<Item = PhysicalRootOwner> + '_ {
        self.owner_overwrites(index)
            .filter(|owner| self.is_root(owner.root_index))
    }

    pub(super) fn owner_overwrites(
        &self,
        index: usize,
    ) -> impl Iterator<Item = PhysicalRootOwner> + '_ {
        self.roots_by_overwrite
            .get(&index)
            .into_iter()
            .flatten()
            .copied()
    }

    pub(super) fn mark_stmts(&self, marked: &mut [bool]) {
        for index in self.roots.iter().chain(&self.retained_overwrites) {
            marked[*index] = true;
        }
    }
}

/// 只投影最终快照中的正向覆盖边；前缀消费者不再逐语句重扫空位置。
fn root_owners_before(
    overwrites: &BTreeMap<usize, Vec<PhysicalRootOwner>>,
    end: usize,
) -> impl Iterator<Item = PhysicalRootOwner> {
    overwrites.range(..end).flat_map(|(index, owners)| {
        owners
            .iter()
            .copied()
            .filter(move |owner| owner.root_index < *index)
    })
}

pub(super) fn collect_call_root_lifetimes(
    snapshot: &RootLifetimeFacts<'_>,
    facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
    observe_potential_events: bool,
    mut producer_temp_is_eligible: impl FnMut(TempId) -> bool,
    mut overwrite_policy: impl FnMut(TempId) -> RootOverwritePolicy,
) -> CallRootLifetimeIndices {
    let stmts = snapshot.stmts;
    let uses = &snapshot.uses;
    let mut active = CallValues::new(uses);
    let mut active_allocations = AllocationHomes::default();
    let mut pending_copy_root_call_moves = BTreeMap::<HomeSlotKey, PendingCopyRootCallMove>::new();
    // Lua 编译器会用 literal nil 的纯 temp copy 清除同 home 的 allocation root；只沿这条
    // 无副作用链传播 nil 事实，其余写入必须先让旧事实失效。
    let mut known_nil_temps = BTreeSet::<TempId>::new();
    let mut lifetimes = CallRootLifetimeIndices::default();

    for (index, stmt) in stmts.iter().enumerate() {
        active.advance(index);
        // caller 的参数槽已交给 callee；同值的低槽 owner 仍独立保活。
        // 必须先消费当前快照的唯一 producer/参数配对，后缀 GC 不能再次选中已交出的 home。
        let transfers = uses.argument_transfers_at(
            index,
            facts,
            active.tracked_temp_count() + active_allocations.temp_count(),
            || active.tracked_temps().chain(active_allocations.temps()),
        );
        for (temp, producer, home) in transfers {
            if active.get(&home).is_some_and(|root| {
                producer >= root.root_index && active.aliases(root.value_id).contains(&temp)
            }) {
                active.transfer(home);
                active.forget_home_aliases(home);
            }
            if active_allocations.get(&home).is_some_and(|root| {
                producer >= root.owner.definition_index && root.aliases.contains(&temp)
            }) {
                active_allocations.transfer(home);
            }
        }
        let scalar_definition = stmt.scalar_temp_assignment();
        let matching_call_move_homes = scalar_definition
            .filter(|(_, value)| matches!(value, HirExpr::Call(_)))
            .and_then(|(temp, _)| {
                facts
                    .trusted_immediate_move_write_homes(temp)
                    .map(|homes| (temp, homes))
            })
            .map(|(temp, homes)| {
                homes
                    .iter()
                    .copied()
                    .filter(|home| {
                        pending_copy_root_call_moves
                            .get(home)
                            .is_some_and(|pending| pending.endpoint == temp)
                    })
                    .collect::<BTreeSet<_>>()
            })
            .unwrap_or_default();
        for home in &matching_call_move_homes {
            let pending = pending_copy_root_call_moves
                .remove(home)
                .expect("matched copy-root call MOVE must retain its pending producer");
            if overwrite_policy(pending.endpoint) == RootOverwritePolicy::Reuse
                && !uses.has_live_read_after(pending.producer, index)
            {
                lifetimes.roots.insert(pending.root_index);
                lifetimes
                    .root_homes
                    .entry(pending.root_index)
                    .or_default()
                    .insert(*home);
                lifetimes
                    .roots_by_overwrite
                    .entry(index)
                    .or_default()
                    .push(PhysicalRootOwner {
                        root_index: pending.root_index,
                        home: *home,
                    });
            }
        }
        if !pending_copy_root_call_moves.is_empty() {
            let writes = snapshot.stack_writes_at(index);
            if writes.has_boundary() || writes.has_unknown_home() {
                pending_copy_root_call_moves.clear();
            } else {
                let homes = writes.intersection(
                    pending_copy_root_call_moves.len(),
                    || pending_copy_root_call_moves.keys().copied(),
                    |home| pending_copy_root_call_moves.contains_key(&home),
                );
                for home in &homes {
                    if !matching_call_move_homes.contains(home) {
                        pending_copy_root_call_moves.remove(home);
                    }
                }
            }
        }

        if let Some(result_homes) = generic_for_dispatch_result_homes(stmt, facts) {
            release_roots_before_generic_dispatch(
                index,
                &result_homes,
                uses,
                facts,
                &mut active,
                &mut active_allocations,
                &mut lifetimes,
            );
        }
        if let Some(call) = call_with_inert_dispatch_prefix(stmt, safety) {
            for producer in &call.frame_root_ends {
                let Some(home) = facts.trusted_temp_home_slot(*producer) else {
                    continue;
                };
                let Some(root) = active.get(&home) else {
                    continue;
                };
                if !root.eligible
                    || !active.aliases(root.value_id).contains(producer)
                    || active.has_live_read_after(root.value_id, home)
                    || active.aliases(root.value_id).iter().any(|temp| {
                        facts.trusted_temp_home_slot(*temp) == Some(home)
                            && uses.has_read_at(*temp, index)
                    })
                {
                    continue;
                }
                let root = active.remove(&home).unwrap();
                lifetimes.preserve_call_root(&root, home);
                lifetimes
                    .call_dispatch_releases
                    .entry(index)
                    .or_default()
                    .push(PhysicalRootOwner {
                        root_index: root.root_index,
                        home,
                    });
            }
        }
        let potential_observation = uses.events.block().stmt(index).may_observe_gc_roots();
        if uses.is_gc_fence(index) {
            preserve_active_call_roots(&mut active, &mut lifetimes);
        } else if observe_potential_events && potential_observation {
            // A potential user-code/GC event matters only if a later same-home overwrite proves
            // the end of this transaction. Unlike an explicit collection fence, this does not
            // by itself justify materializing every still-active call result.
            observe_active_call_values(&mut active, None);
        }
        let read_values = active.read_values_at(index);
        if let HirStmt::Return(ret) = stmt
            && !active.is_empty()
        {
            let value_by_temp = active
                .tracked_temps()
                .filter_map(|temp| active.value_for_temp(temp).map(|value| (temp, value)))
                .collect();
            if let Some(observed) = return_roots::observed_return_roots(
                &ret.values,
                snapshot.scalar_definitions(),
                &value_by_temp,
                safety,
            ) {
                for value in observed {
                    for &home in active.homes(value) {
                        let root = active.get(&home).expect("active call value owns its home");
                        if root.eligible
                            && !root.explicit_fence_only
                            && stmts[root.root_index].scalar_temp_assignment().is_some_and(
                                |(temp, _)| facts.is_pure_scope_end_copy_root_temp(temp),
                            )
                        {
                            // 参数内 callee 已消费后，外层调用仍可能观察原低槽根；
                            // return 自身结束 frame 不能提前到内层调用结束（regress_352）。
                            lifetimes.preserve_call_root(root, home);
                        }
                    }
                }
            }
        }
        let read_observations = read_values
            .into_iter()
            .filter(|value| {
                let aliases = active.aliases(*value);
                let is_loop_control = matches!(
                    stmt,
                    HirStmt::While(_)
                        | HirStmt::Repeat(_)
                        | HirStmt::NumericFor(_)
                        | HirStmt::GenericFor(_)
                );
                let has_later_fence = uses.has_gc_fence_after(index);
                // 控制头和纯 copy 本身只转发值；后续显式 GC 仍需要精确物理根配对。
                if !has_later_fence
                    && (is_loop_control
                        || stmt_is_direct_if_control_read(
                            stmt,
                            aliases,
                            snapshot.uses.events.block().stmt(index),
                        )
                        || stmt_is_transparent_temp_copy(stmt, aliases))
                {
                    return false;
                }
                active.homes(*value).any(|home| {
                    let root = active.get(home).unwrap();
                    // 前层已证明最后值读取后、首个观察前覆盖时，读取不升级根事务。
                    if stmts[root.root_index]
                        .scalar_temp_assignment()
                        .is_some_and(|(temp, _)| facts.call_result_root_ends_after_value_use(temp))
                    {
                        return false;
                    }
                    has_later_fence
                        || potential_observation
                        || definite_grouped_home_overwrite(
                            stmt,
                            snapshot.stack_writes_at(index),
                            *home,
                            facts,
                            &mut |_| true,
                        )
                        .is_none()
                })
            })
            .collect::<BTreeSet<_>>();
        observe_active_call_values(&mut active, Some(&read_observations));
        if let HirStmt::LocalDecl(decl) = stmt
            && let ([local], [HirExpr::TempRef(source)], None) = (
                decl.bindings.as_slice(),
                decl.values.fixed.as_slice(),
                &decl.values.tail,
            )
            && let Some(home) = facts.trusted_local_home_slot(*local)
        {
            // 捕获等入口已物化为 LocalDecl：用现有 RHS 值身份签发交接，不能猜回被丢弃的
            // SSA target。LocalRef 尚无本 collector 的值流事实，不在这里扩展为同 home 即同值。
            let root_index = active
                .get(&home)
                .filter(|root| !root.transferred && active.aliases(root.value_id).contains(source))
                .map(|root| root.root_index)
                .or_else(|| {
                    let root = active_allocations.get(&home)?;
                    (!root.transferred
                        && active_allocations.site_for_temp(*source) == Some(root.allocation_site))
                    .then_some(root.owner.definition_index)
                });
            if let Some(root_index) = root_index {
                lifetimes
                    .continuation_owners
                    .insert(index, PhysicalRootOwner { root_index, home });
            }
            // 此声明已经接管源码 binding；下方写入摘要正常退休旧 Temp home 及其别名。
        }
        let Some((temp, value)) = scalar_definition else {
            known_nil_temps.retain(|temp| !uses.has_write_at(*temp, index));
            if let Some(targets) = exact_multi_call_home_targets(stmt, facts) {
                let target_homes = targets
                    .iter()
                    .map(|(_, home)| *home)
                    .collect::<BTreeSet<_>>();
                for (temp, home) in &targets {
                    if let Some(root) = active.remove(home) {
                        record_call_root_overwrite(
                            root,
                            index,
                            *home,
                            overwrite_policy(*temp) == RootOverwritePolicy::Reuse,
                            uses,
                            &active,
                            &mut lifetimes,
                        );
                    }
                }
                for (temp, _) in &targets {
                    active.forget_temp(*temp);
                }
                active_allocations.remove_homes(&target_homes);
                for (temp, home) in targets {
                    let value_id = active.new_value();
                    active.bind(temp, home, value_id);
                    active.insert(
                        home,
                        ActiveCallRoot {
                            value_id,
                            root_index: index,
                            eligible: producer_temp_is_eligible(temp),
                            observed: false,
                            preserved: false,
                            explicit_fence_only: false,
                            transferred: false,
                        },
                    );
                }
                continue;
            }
            if let Some(overwrites) = exact_multi_nil_home_overwrites(stmt, facts, &mut |temp| {
                overwrite_policy(temp) == RootOverwritePolicy::Reuse
            }) {
                for ExactNilHomeOverwrite {
                    temps,
                    home,
                    eligible,
                } in overwrites
                {
                    known_nil_temps.extend(temps.iter().copied());
                    if let Some(root) = active.remove(&home) {
                        record_call_root_overwrite(
                            root,
                            index,
                            home,
                            eligible,
                            uses,
                            &active,
                            &mut lifetimes,
                        );
                    }
                    if temps.is_empty() {
                        // 已物化 binding 的 nil 写保留原 Local/Param；只退休该 home 的 Temp 跟踪。
                        active_allocations.remove(&home);
                        continue;
                    }
                    let mut allocation_state = AllocationRootState {
                        active: &mut active_allocations,
                        lifetimes: &mut lifetimes,
                        uses,
                    };
                    for temp in temps {
                        update_allocation_roots(
                            &mut allocation_state,
                            index,
                            temp,
                            &HirExpr::Nil,
                            home,
                            eligible,
                        );
                    }
                }
                continue;
            }
            // 摘要只会失效已有 home/alias。空状态不能因嵌套写入产生根，
            // 不应让每层无本地 producer 的循环为此重扫整棵未改写子树。
            if active.is_empty() && active_allocations.is_empty() {
                continue;
            }
            let current_writes = snapshot.stack_writes_at(index);
            let mut current_homes = current_writes.intersection(
                active.tracked_home_count_bound() + active_allocations.len(),
                || active.tracked_homes().chain(active_allocations.keys()),
                |home| active.tracks_home(home) || active_allocations.get(&home).is_some(),
            );
            current_homes.retain(|home| !matching_call_move_homes.contains(home));
            let mut proven_homes = BTreeSet::new();
            let grouped_assignment_is_complete =
                grouped_assignment_targets_are_active(stmt, facts, |home| {
                    active.get(home).is_some() || active_allocations.get(home).is_some()
                });
            // 共享写入摘要已枚举可能覆盖的 home；不为纯调用重扫全部活动对象。
            for home in current_homes.iter().copied() {
                if !grouped_assignment_is_complete {
                    break;
                }
                if active.get(&home).is_none() && active_allocations.get(&home).is_none() {
                    continue;
                }
                let Some(overwrite) = definite_grouped_home_overwrite(
                    stmt,
                    current_writes,
                    home,
                    facts,
                    &mut |temp| overwrite_policy(temp) == RootOverwritePolicy::Reuse,
                ) else {
                    continue;
                };
                proven_homes.insert(home);
                let active_root_is_read = active.get(&home).is_some_and(|root| {
                    active
                        .aliases(root.value_id)
                        .iter()
                        .any(|alias| uses.has_read_at(*alias, index))
                });
                for temp in &overwrite.temps {
                    active.forget_temp(*temp);
                }
                if let Some(root) = active.remove(&home)
                    && !active_root_is_read
                {
                    record_call_root_overwrite(
                        root,
                        index,
                        home,
                        overwrite.eligible,
                        uses,
                        &active,
                        &mut lifetimes,
                    );
                }
                terminate_allocation_home(
                    &mut active_allocations,
                    &mut lifetimes,
                    uses,
                    index,
                    home,
                    overwrite.eligible,
                );
            }
            if current_writes.has_boundary() || current_writes.has_unknown_home() {
                active.clear();
                active_allocations.clear();
            } else {
                for home in current_homes
                    .iter()
                    .filter(|home| !proven_homes.contains(home))
                {
                    active.remove(home);
                    active.forget_home_aliases(*home);
                }
                for home in current_homes
                    .iter()
                    .filter(|home| !proven_homes.contains(home))
                {
                    active_allocations.remove(home);
                }
            }
            continue;
        };
        let value_is_known_nil = matches!(value, HirExpr::Nil)
            || matches!(value, HirExpr::TempRef(source) if known_nil_temps.contains(source));
        known_nil_temps.remove(&temp);
        if value_is_known_nil {
            known_nil_temps.insert(temp);
        }
        let Some(slot) = facts.trusted_temp_home_slot(temp) else {
            active.clear();
            active_allocations.clear();
            continue;
        };

        let producer_eligible = producer_temp_is_eligible(temp);
        let overwrite_policy = overwrite_policy(temp);
        let overwrite_eligible = overwrite_policy == RootOverwritePolicy::Reuse;
        let needs_copy_root_bridge = !matches!(
            value,
            HirExpr::Call(_)
                | HirExpr::TempRef(_)
                | HirExpr::GlobalRef(_)
                | HirExpr::TableAccess(_)
                | HirExpr::TableConstructor(_)
                | HirExpr::Unresolved(_)
        ) && !safety.result_is_gc_inert(value);
        if producer_eligible
            && needs_copy_root_bridge
            && let Some(endpoint) = facts.copy_root_call_result_move_overwrite(temp)
        {
            pending_copy_root_call_moves.insert(
                slot,
                PendingCopyRootCallMove {
                    root_index: index,
                    producer: temp,
                    endpoint,
                },
            );
        }
        let mut allocation_state = AllocationRootState {
            active: &mut active_allocations,
            lifetimes: &mut lifetimes,
            uses,
        };
        update_allocation_roots(
            &mut allocation_state,
            index,
            temp,
            value,
            slot,
            producer_eligible,
        );
        let same_value_in_target_home = matches!(value, HirExpr::TempRef(source)
            if active
                .get(&slot)
                .is_some_and(|root| !root.transferred && active.aliases(root.value_id).contains(source)));
        active.forget_temp(temp);

        if matches!(value, HirExpr::Call(_))
            && let Some(write_homes) = facts.trusted_immediate_move_write_homes(temp)
        {
            let extra_write_homes = write_homes
                .iter()
                .copied()
                .filter(|home| *home != slot)
                .collect::<BTreeSet<_>>();
            for write_home in &extra_write_homes {
                if let Some(root) = active.remove(write_home) {
                    record_call_root_overwrite(
                        root,
                        index,
                        *write_home,
                        overwrite_eligible,
                        uses,
                        &active,
                        &mut lifetimes,
                    );
                }
                // CALL 后的透明 MOVE 也会结束 allocation 的旧 home；不能只移除索引，
                // 否则 locals 会新建返回值 binding，留下跨后续 GC 的旧分配根。
                terminate_allocation_home(
                    &mut active_allocations,
                    &mut lifetimes,
                    uses,
                    index,
                    *write_home,
                    overwrite_eligible,
                );
            }
        }

        // Copying the active value back into its own home leaves the same GC root in place.
        // Record the new SSA name as another alias so a later logical read can prove that the
        // physical home was not the value's only surviving root.
        if same_value_in_target_home {
            let value_id = active
                .get(&slot)
                .expect("same-home active call root must exist")
                .value_id;
            active.bind(temp, slot, value_id);
            let root = active.get(&slot).unwrap();
            lifetimes.continuation_owners.insert(
                index,
                PhysicalRootOwner {
                    root_index: root.root_index,
                    home: slot,
                },
            );
            continue;
        }

        if let Some(root) = active.remove(&slot) {
            if overwrite_policy == RootOverwritePolicy::ReleaseExisting
                && root.eligible
                && !active.has_live_read_after(root.value_id, slot)
            {
                lifetimes
                    .overwrite_releases
                    .entry(index)
                    .or_default()
                    .push(PhysicalRootOwner {
                        root_index: root.root_index,
                        home: slot,
                    });
            }
            record_call_root_overwrite(
                root,
                index,
                slot,
                overwrite_eligible,
                uses,
                &active,
                &mut lifetimes,
            );
        }

        if let HirExpr::TempRef(source) = value {
            if let Some(value_id) = active.value_for_temp(*source) {
                active.bind(temp, slot, value_id);
                // A cross-home copy starts an independent physical root transaction. The
                // source home can be overwritten before a later GC fence while this target
                // home still retains the call result, so alias propagation alone is not enough.
                active.insert(
                    slot,
                    ActiveCallRoot {
                        value_id,
                        root_index: index,
                        eligible: producer_eligible,
                        observed: false,
                        preserved: false,
                        // Transparent compiler forwarding can normally be reconstructed inside
                        // its consuming expression. Only an explicit collection fence proves
                        // that the otherwise unread target home needs a standalone source owner.
                        explicit_fence_only: true,
                        transferred: false,
                    },
                );
            }
            continue;
        }

        if matches!(value, HirExpr::Call(_)) {
            let value_id = active.new_value();
            active.bind(temp, slot, value_id);
            active.insert(
                slot,
                ActiveCallRoot {
                    value_id,
                    root_index: index,
                    eligible: producer_eligible,
                    observed: false,
                    preserved: false,
                    explicit_fence_only: false,
                    transferred: false,
                },
            );
        }
    }

    // 覆盖当时尚未逃逸不授权丢弃终点：对象可以在之后经父表发布，而独立 HIR
    // binding 仍可能被物化。完整构造器事务可消费自己的私有证明，原 home 终点始终保留。
    extend_physical_owner_overwrites(
        snapshot,
        facts,
        safety,
        &mut producer_temp_is_eligible,
        &mut |temp| overwrite_policy(temp) == RootOverwritePolicy::Reuse,
        &mut lifetimes,
    );
    lifetimes
}

/// 复用已保活的物理 owner 后，新写入值也必须在其精确覆盖点释放。
/// 例如 call result -> captured local 读回 -> callee MOVE，或 allocation -> lookup：
/// 每次写入都有自己的值身份，但共享同一源码 root 的完整覆盖链。
/// 这里只延续已证明的同 home 物化事务，不推断新旧值相等。
fn extend_physical_owner_overwrites(
    snapshot: &RootLifetimeFacts<'_>,
    facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
    producer_is_eligible: &mut impl FnMut(TempId) -> bool,
    overwrite_is_eligible: &mut impl FnMut(TempId) -> bool,
    lifetimes: &mut CallRootLifetimeIndices,
) {
    if lifetimes.root_homes.is_empty() {
        return;
    }
    let stmts = snapshot.stmts;
    let uses = &snapshot.uses;
    let mut owners = BTreeMap::<HomeSlotKey, (usize, TempId)>::new();
    for (index, stmt) in stmts.iter().enumerate() {
        let definition = stmt.scalar_temp_assignment();
        let target = definition.and_then(|(temp, value)| {
            facts
                .trusted_temp_home_slot(temp)
                .map(|home| (temp, value, home))
        });
        if let Some((temp, _, home)) = target
            && let Some((root_index, producer)) = owners.get(&home).copied()
            && overwrite_is_eligible(temp)
            && !uses.has_live_read_after(producer, index)
            && !uses.has_argument_transfer(producer, root_index, index)
            && lifetimes.overwrite_pair_for_home(index, home).is_none()
        {
            lifetimes.roots.insert(root_index);
            lifetimes
                .root_homes
                .entry(root_index)
                .or_default()
                .insert(home);
            if !lifetimes
                .owner_overwrites(index)
                .any(|owner| owner.root_index == root_index && owner.home == home)
            {
                lifetimes
                    .roots_by_overwrite
                    .entry(index)
                    .or_default()
                    .push(PhysicalRootOwner { root_index, home });
            }
        }
        let continues_physical_owner = target.is_some_and(|(_, _, home)| {
            lifetimes
                .overwrite_pairs(index)
                .any(|pair| pair.home() == home)
        });
        if !owners.is_empty() {
            let writes = snapshot.stack_writes_at(index);
            if writes.has_boundary() || writes.has_unknown_home() {
                owners.clear();
            } else {
                let homes = writes.intersection(
                    owners.len(),
                    || owners.keys().copied(),
                    |home| owners.contains_key(&home),
                );
                for home in &homes {
                    owners.remove(home);
                }
            }
        }
        if let Some((temp, value, home)) = target
            && continues_physical_owner
            && producer_is_eligible(temp)
            && !safety.result_is_gc_inert(value)
            // copy 带有独立目标 home 和参数交接生命周期；把它沿用为 caller owner
            // 会在 callee 已释放参数后继续保活。不能从值相同推断根的生命周期相同。
            && !matches!(value, HirExpr::TempRef(_))
        {
            owners.insert(home, (index, temp));
        }
    }
}

fn generic_for_dispatch_result_homes(
    stmt: &HirStmt,
    facts: &ProtoPromotionFacts,
) -> Option<BTreeSet<HomeSlotKey>> {
    let HirStmt::GenericFor(for_stmt) = stmt else {
        return None;
    };
    if for_stmt.dispatch_results.is_empty() {
        return None;
    }
    assert_eq!(
        for_stmt.dispatch_results.len(),
        for_stmt.bindings.len(),
        "generic-for dispatch certificate must cover every source binding"
    );
    assert!(
        for_stmt
            .dispatch_results
            .iter()
            .zip(&for_stmt.bindings)
            .all(|(result, binding)| result.success_binding == *binding),
        "generic-for dispatch certificate must preserve result/binding positions"
    );
    Some(
        for_stmt
            .dispatch_results
            .iter()
            .map(|result| {
                facts
                    .home_slot(result.result_def)
                    .expect("generic-for dispatch result must retain its raw physical home")
            })
            .collect(),
    )
}

fn release_roots_before_generic_dispatch(
    index: usize,
    result_homes: &BTreeSet<HomeSlotKey>,
    uses: &TempUseEvents<'_>,
    facts: &ProtoPromotionFacts,
    active_calls: &mut CallValues<'_>,
    active_allocations: &mut AllocationHomes,
    lifetimes: &mut CallRootLifetimeIndices,
) {
    for home in result_homes {
        if let Some(root) = active_calls.remove(home)
            && root.eligible
            && let Some(temp) = root_release_temp(
                active_calls.aliases(root.value_id),
                *home,
                index,
                uses,
                facts,
            )
        {
            lifetimes
                .pre_dispatch_releases
                .entry(index)
                .or_default()
                .insert((temp, *home));
        }
    }

    for home in result_homes {
        if let Some(root) = active_allocations.remove(home)
            && root.owner.eligible
            && let Some(temp) = root
                .aliases
                .iter()
                .copied()
                .find(|temp| !uses.has_live_read_from(*temp, index))
        {
            lifetimes
                .pre_dispatch_releases
                .entry(index)
                .or_default()
                .insert((temp, *home));
        }
    }
}

fn root_release_temp(
    aliases: &BTreeSet<TempId>,
    home: HomeSlotKey,
    index: usize,
    uses: &TempUseEvents<'_>,
    facts: &ProtoPromotionFacts,
) -> Option<TempId> {
    aliases.iter().copied().find(|temp| {
        facts.trusted_temp_home_slot(*temp) == Some(home) && !uses.has_live_read_from(*temp, index)
    })
}

/// 将 VM 在 generic-for iterator callback 前结束的旧 result-home root 显式化为 HIR nil
/// release。这个赋值不模拟 iterator result；它只给后续 locals/AST 一个可表达的词法作用域
/// endpoint，避免把旧对象强引用错误延长进 callback 或函数尾。
pub(super) fn materialize_generic_for_dispatch_root_releases(
    block: &mut HirBlock,
    facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
    temp_is_eligible: &mut impl FnMut(TempId) -> bool,
) -> bool {
    // 释放端点只可能是当前 block 的显式 dispatch；子块由下面的递归独立处理。
    let releases = if block.stmts.iter().any(|stmt| {
        matches!(stmt, HirStmt::GenericFor(for_stmt) if !for_stmt.dispatch_results.is_empty())
    }) {
        collect_call_root_lifetimes(
            &RootLifetimeFacts::new(&block.stmts, facts, safety),
            facts,
            safety,
            true,
            &mut *temp_is_eligible,
            |_| RootOverwritePolicy::Reuse,
        ).pre_dispatch_releases
    } else {
        BTreeMap::new()
    };
    let mut changed = !releases.is_empty();
    let old_stmts = std::mem::take(&mut block.stmts);
    let mut new_stmts = Vec::with_capacity(old_stmts.len() + releases.len());
    for (index, mut stmt) in old_stmts.into_iter().enumerate() {
        if let Some(pairs) = releases.get(&index) {
            let dispatch_results = dispatch_release_results(&stmt, facts);
            let mut release_homes = BTreeMap::<TempId, Option<HomeSlotKey>>::new();
            for &(temp, home) in pairs {
                // 同一 allocation alias 可承担多个结果槽的旧根；仍只清零一次，但不
                // 把一个 binding 的多个端点任意签成其中一个 result identity。
                release_homes
                    .entry(temp)
                    .and_modify(|home| *home = None)
                    .or_insert(Some(home));
            }
            for (temp, home) in release_homes {
                let generic_for_dispatch_release = home.and_then(|home| {
                    let (dispatch, results) = dispatch_results.as_ref()?;
                    Some(HirGenericForDispatchRelease {
                        dispatch: *dispatch,
                        result_def: *results.get(&home)?,
                        released: temp,
                    })
                });
                new_stmts.push(HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(temp)],
                    values: HirValuePack::fixed(vec![HirExpr::Nil]),
                    initializer_merge_transaction: None,
                    generic_for_initializer_producer: None,
                    generic_for_dispatch_release,
                    method_rewrite_transaction: None,
                })));
            }
        }
        changed |= materialize_generic_for_dispatch_root_releases_in_stmt(
            &mut stmt,
            facts,
            safety,
            temp_is_eligible,
        );
        new_stmts.push(stmt);
    }
    block.stmts = new_stmts;
    changed
}

/// dispatch source 与 raw result home 由同一 loop owner 验证；缺少来源时保留原 nil 写，
/// 不从相邻 iterator 文本或被释放 binding 的 possible home 反推协议身份。
fn dispatch_release_results(
    stmt: &HirStmt,
    facts: &ProtoPromotionFacts,
) -> Option<(HirSourceSite, BTreeMap<HomeSlotKey, TempId>)> {
    let HirStmt::GenericFor(for_) = stmt else {
        return None;
    };
    facts.generic_for_body_frame(for_)?;
    let dispatch = for_.body_frame_source?;
    let results = for_
        .dispatch_results
        .iter()
        .map(|result| Some((facts.home_slot(result.result_def)?, result.result_def)))
        .collect::<Option<BTreeMap<_, _>>>()?;
    Some((dispatch, results))
}

fn materialize_generic_for_dispatch_root_releases_in_stmt(
    stmt: &mut HirStmt,
    facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
    temp_is_eligible: &mut impl FnMut(TempId) -> bool,
) -> bool {
    match stmt {
        HirStmt::LocalRootRelease(_) => false,
        HirStmt::If(if_stmt) => {
            let then_changed = materialize_generic_for_dispatch_root_releases(
                &mut if_stmt.then_block,
                facts,
                safety,
                temp_is_eligible,
            );
            let else_changed = if_stmt.else_block.as_mut().is_some_and(|block| {
                materialize_generic_for_dispatch_root_releases(
                    block,
                    facts,
                    safety,
                    temp_is_eligible,
                )
            });
            then_changed || else_changed
        }
        HirStmt::While(while_stmt) => materialize_generic_for_dispatch_root_releases(
            &mut while_stmt.body,
            facts,
            safety,
            temp_is_eligible,
        ),
        HirStmt::Repeat(repeat_stmt) => materialize_generic_for_dispatch_root_releases(
            &mut repeat_stmt.body,
            facts,
            safety,
            temp_is_eligible,
        ),
        HirStmt::NumericFor(for_stmt) => materialize_generic_for_dispatch_root_releases(
            &mut for_stmt.body,
            facts,
            safety,
            temp_is_eligible,
        ),
        HirStmt::GenericFor(for_stmt) => materialize_generic_for_dispatch_root_releases(
            &mut for_stmt.body,
            facts,
            safety,
            temp_is_eligible,
        ),
        HirStmt::Block(block) => {
            materialize_generic_for_dispatch_root_releases(block, facts, safety, temp_is_eligible)
        }
        HirStmt::LocalDecl(_)
        | HirStmt::GlobalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => false,
    }
}

/// 识别跨后续用户代码/GC 事件，或 return 表达式内部后续事件的标量结果物理 root。
/// 动态一元/二元运算可经元方法返回对象，与 lookup 共用 home、别名与观察窗口。
/// 例如 `a = x * 2; b = a + 1; if b > 10 then ... end` 的比较元方法仍可观察 a。
///
/// Call 的观察、allocation owner 与相邻 overwrite 合同保持在既有 collector 中；这里不把
/// 普通 lookup 一概提升为 source local。GlobalRef 只在 low CFG 已经证明所有路径都活到 scope
/// end，且 HIR 的最后一次 identity 读取后仍有观察点时，才需要独立物化；TableAccess 的标量
/// 与无求值 multi-nil 仍沿既有同-home 精确配对。没有可见 overwrite 时，跨过显式 GC/普通
/// 用户事件，或在 return 子表达式中先被消费、随后又跨过用户事件的 lookup，由当前 HIR
/// block 的词法 local 保活到 block end。block 外的 successor 不属于该 local 的可见区间，
/// 因此无需猜测跨块 home 复用。
pub(super) fn collect_scalar_gc_root_lifetimes(
    snapshot: &RootLifetimeFacts<'_>,
    facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
    mut temp_is_eligible: impl FnMut(TempId) -> bool,
) -> ScalarGcRootLifetimeIndices {
    let stmts = snapshot.stmts;
    let uses = &snapshot.uses;
    if uses.gc_fence_indices.is_empty()
        && uses.events.block().observation_indices().is_empty()
        && !stmts.iter().any(|stmt| matches!(stmt, HirStmt::Return(_)))
    {
        return ScalarGcRootLifetimeIndices::default();
    }
    let reference_captured_temps = super::mention::stmts_reference_captured_bindings(stmts).temps;
    let mut active = BTreeMap::<HomeSlotKey, ActiveScalarGcHome>::new();
    let mut values = ScalarValues::new(uses);
    let mut lifetimes = ScalarGcRootLifetimeIndices::default();

    for (index, stmt) in stmts.iter().enumerate() {
        values.advance(index);
        // 参数 home 在 dispatch 时交给 callee；不能再把它物化为跨调用存活的 caller local。
        // 同值的其它 home 仍独立保活，只有当前快照中的唯一 producer/端点证明可以结束事务。
        let transfers = uses.argument_transfers_at(index, facts, values.by_temp.len(), || {
            values.by_temp.keys().copied()
        });
        for (temp, producer, home) in transfers {
            let Some(root) = active.get(&home) else {
                continue;
            };
            if root.aliases.contains(&temp) && producer >= root.root_index {
                let root = active
                    .remove(&home)
                    .expect("matched argument home must remain active");
                for alias in root.aliases {
                    values.remove(&alias, index);
                }
            }
        }

        if let HirStmt::CallStmt(call_stmt) = stmt
            && let call = &call_stmt.call
            && let HirExpr::TableAccess(access) = &call.callee
            && let Some(protocol) =
                super::method_protocol::match_method_setup_pair(access, &call.callee, call)
                    .and_then(|id| facts.method_setup_protocol(id))
            && let Some(prior) = protocol.prior_callee_root_temp
            && let Some(home) = facts.trusted_temp_home_slot(protocol.callee_temp)
            && facts.trusted_temp_home_slot(prior) == Some(home)
            && let Some(root) = active.get(&home)
            && root.eligible
            && root.aliases.contains(&prior)
            && !lifetimes.is_root(root.root_index)
            && !root
                .aliases
                .iter()
                .any(|temp| uses.has_live_read_after(*temp, index))
        {
            // 完整 SELF lookup 已在原 callee home 覆盖 receiver；独立首参 home 由
            // argument handoff 管理。内嵌 lookup 仍须保持协议双端匹配，不能把已结束
            // 的低槽根延续到下一次 receiver 读取（regress_316）。这里不删 producer
            // 或插入提前释放，已有独立保活事务仍交给其原 endpoint owner。
            let root = active.remove(&home).unwrap();
            for alias in root.aliases {
                values.remove(&alias, index);
            }
        }

        if let Some(call) = call_with_inert_dispatch_prefix(stmt, safety) {
            for producer in &call.frame_root_ends {
                let Some(home) = facts.trusted_temp_home_slot(*producer) else {
                    continue;
                };
                let Some(root) = active.get(&home) else {
                    continue;
                };
                if !root.eligible
                    || !root.aliases.contains(producer)
                    || root
                        .aliases
                        .iter()
                        .any(|temp| uses.has_live_read_from(*temp, index))
                {
                    continue;
                }
                let root = active.remove(&home).unwrap();
                for alias in root.aliases {
                    values.remove(&alias, index);
                }
                // 原 frame 在 dispatch 排除该 home。保留 producer 与终点为同一事务，
                // 不能将读取结果提升为越过 callee 的独立 local（包括 LuaJIT frame gap）。
                lifetimes.roots.insert(root.root_index);
                lifetimes
                    .call_dispatch_releases
                    .entry(index)
                    .or_default()
                    .push(PhysicalRootOwner {
                        root_index: root.root_index,
                        home,
                    });
            }
        }

        let Some((temp, value)) = stmt.scalar_temp_assignment() else {
            if let HirStmt::Return(return_stmt) = stmt {
                observe_lookup_return_post_use_roots(
                    &return_stmt.values,
                    snapshot.scalar_definitions(),
                    &values.by_temp,
                    &mut active,
                    safety,
                );
                preserve_lookup_roots_to_scope_end(&active, &values, index + 1, &mut lifetimes);
                active.clear();
                values.clear();
                continue;
            }
            if let HirStmt::ErrNil(err_nil) = stmt
                && let HirExpr::TempRef(temp) = &err_nil.value
                && let Some(value_id) = values.by_temp.get(temp).copied()
            {
                // ERRNNIL 的正常后继已经证明该 lookup 结果为 nil；它不再可能承担 GC root。
                // 只终止同一 value identity，不能把同时活跃的其它 home 一并清空。
                values.retire_value(value_id, index, &mut active, facts);
                continue;
            }
            if let Some((value_id, handoff_root)) = nil_guarded_global_lookup_handoff(
                index,
                stmt,
                &active,
                &values,
                &reference_captured_temps,
                uses,
                facts,
            ) {
                // `source ~= nil` 的分支已经先把同一 identity 交给另一个 reference-captured
                // physical home；另一路 source 为 nil，本来就没有待保活对象。原 lookup
                // home 因而不再是后续观察点所需的独立 root。这个证明必须留在 HIR：AST
                // 只会看到两个 local，无法恢复分支对应的 VM home 事务（regress_36）。
                values.retire_value(value_id, index, &mut active, facts);
                lifetimes.handoff_roots.insert(handoff_root);
            }
            if let Some(overwrites) =
                exact_multi_nil_home_overwrites(stmt, facts, &mut temp_is_eligible)
            {
                for overwrite in &overwrites {
                    for temp in &overwrite.temps {
                        values.remove(temp, index);
                        if let Some(root) = active.get_mut(&overwrite.home) {
                            root.aliases.remove(temp);
                        }
                    }
                }
                for overwrite in overwrites {
                    if let Some(root) = active.remove(&overwrite.home) {
                        for alias in &root.aliases {
                            values.remove(alias, index);
                        }
                        record_lookup_root_overwrite(
                            root,
                            index,
                            overwrite.home,
                            overwrite.eligible,
                            uses,
                            &values,
                            &mut lifetimes,
                        );
                    }
                }
                continue;
            }
            if active.is_empty() && values.by_temp.is_empty() {
                continue;
            }
            let mut proven_homes = BTreeSet::new();
            let writes = snapshot.stack_writes_at(index);
            let grouped_assignment_is_complete =
                grouped_assignment_targets_are_active(stmt, facts, |home| {
                    active.contains_key(home)
                });
            let written_active_homes = writes.intersection(
                active.len(),
                || active.keys().copied(),
                |home| active.contains_key(&home),
            );
            for home in written_active_homes.iter().copied() {
                if !grouped_assignment_is_complete {
                    break;
                }
                let Some(overwrite) = definite_grouped_home_overwrite(
                    stmt,
                    writes,
                    home,
                    facts,
                    &mut temp_is_eligible,
                ) else {
                    continue;
                };
                proven_homes.insert(home);
                for temp in &overwrite.temps {
                    values.remove(temp, index);
                    if let Some(root) = active.get_mut(&home) {
                        root.aliases.remove(temp);
                    }
                }
                let Some(mut root) = active.remove(&home) else {
                    continue;
                };
                for alias in &root.aliases {
                    values.remove(alias, index);
                }
                // Grouped assignment evaluates every RHS and branch/block prefix while the old
                // physical home is still owned by this local. Each proven path then commits a
                // target for the same home, so the old lookup can terminate at this statement.
                root.crossed_observation |= uses.has_gc_fence_after(index);
                record_lookup_root_overwrite(
                    root,
                    index,
                    home,
                    overwrite.eligible,
                    uses,
                    &values,
                    &mut lifetimes,
                );
            }
            if writes.has_boundary() || writes.has_unknown_home() {
                // 清空嵌套控制流的 home 状态前消费观察；只接受 low CFG 的全路径保活证明。
                // 仅在失效时访问这些 home，不在每个普通 call 上重扫全部活动根。
                for root in active.values() {
                    preserve_observed_scope_end_root(root, &values, index + 1, &mut lifetimes);
                }
                active.clear();
                values.clear();
            } else {
                for home in written_active_homes
                    .iter()
                    .filter(|home| !proven_homes.contains(home))
                {
                    if let Some(root) = active.remove(home) {
                        preserve_observed_scope_end_root(&root, &values, index + 1, &mut lifetimes);
                        for alias in root.aliases {
                            values.remove(&alias, index);
                        }
                    }
                }
            }
            continue;
        };
        let Some(home) = facts.trusted_temp_home_slot(temp) else {
            active.clear();
            values.clear();
            continue;
        };
        let eligible = temp_is_eligible(temp);
        let incoming_value = match value {
            HirExpr::ParamRef(_)
                if facts.overwrites_unknown_scratch(temp)
                    || facts.copy_root_overwrites(temp).is_some() =>
            {
                // 参数在回调中可被 debug.setlocal 改写；独立 COPY 的精确纯覆盖终点
                // 已由原 owner 证明，不能因目标原先为 nil 就丢弃这个快照根。
                Some(values.new_value(index, None))
            }
            HirExpr::TempRef(source) if facts.overwrites_unknown_scratch(temp) => Some(
                values
                    .by_temp
                    .get(source)
                    .copied()
                    .unwrap_or_else(|| values.new_value(index, None)),
            ),
            HirExpr::TableAccess(_) => Some(values.new_value(index, None)),
            HirExpr::Unary(_) | HirExpr::Binary(_) if !safety.result_is_gc_inert(value) => {
                // 元方法可返回任意对象；独立结果槽在最后一次读取后仍可能是 GC root。
                // 与 lookup 共用 identity/home 生命周期，不能把算术外形当作数值证明。
                Some(values.new_value(index, None))
            }
            HirExpr::GlobalRef(_) if facts.is_pure_scope_end_copy_root_temp(temp) => {
                Some(values.new_value(index, Some(home)))
            }
            HirExpr::TempRef(source) => values.by_temp.get(source).copied(),
            _ => None,
        };
        let continues_same_home = incoming_value.is_some_and(|value_id| {
            active
                .get(&home)
                .is_some_and(|root| root.value_id == value_id)
        });
        // alias 只在其 trusted home 中建立，覆盖也只影响该 home 的旧事务。
        if let Some(root) = active.get_mut(&home) {
            root.aliases.remove(&temp);
        }
        values.remove(&temp, index);

        if continues_same_home {
            let root = active
                .get_mut(&home)
                .expect("same-home active lookup root must exist");
            root.aliases.insert(temp);
            root.eligible &= eligible;
            values.insert(temp, root.value_id, index);
            continue;
        }

        if let Some(root) = active.remove(&home) {
            for alias in &root.aliases {
                values.remove(alias, index);
            }
            record_lookup_root_overwrite(
                root,
                index,
                home,
                eligible,
                uses,
                &values,
                &mut lifetimes,
            );
        }

        if let Some(value_id) = incoming_value {
            values.insert(temp, value_id, index);
            active.insert(
                home,
                ActiveScalarGcHome {
                    value_id,
                    root_index: index,
                    aliases: BTreeSet::from([temp]),
                    // 已有前置读写的 temp 由现存状态/循环 owner 管理，不能在此新建词法根。
                    eligible: eligible
                        && !uses.events.block().has_touch_before(temp, index)
                        && !uses.has_read_at(temp, index),
                    crossed_observation: false,
                    required_scratch_write: facts.overwrites_unknown_scratch(temp),
                    direct_result_home: matches!(
                        value,
                        HirExpr::TableAccess(_)
                            | HirExpr::GlobalRef(_)
                            | HirExpr::Unary(_)
                            | HirExpr::Binary(_)
                    ),
                    scope_end_copy_root: facts.is_scope_end_copy_root_temp(temp),
                    pure_scope_end_copy_root: facts.is_pure_scope_end_copy_root_temp(temp),
                    has_overwrite_proof: facts.copy_root_overwrites(temp).is_some(),
                },
            );
        }
    }

    preserve_lookup_roots_to_scope_end(&active, &values, stmts.len(), &mut lifetimes);
    lifetimes
}

/// 识别 nil fallback 前缀里的条件 root handoff。
///
/// 只接受 `lookup ~= nil` 一侧在任何潜在观察前，以纯 copy 把同一 identity 写入另一个
/// physical home；该 target 必须在 join 后仍以同一 trusted home 被 reference capture，因而
/// 不能作为 dead temp 消失。nil 一侧不需要 root；non-nil 一侧把 PhysicalRoot provenance
/// 转交给这个 join owner。普通 callee copy 没有 capture owner，因此不会把
/// `global; copy; call; gc` 错认成 handoff（regress_419）。
fn nil_guarded_global_lookup_handoff(
    index: usize,
    stmt: &HirStmt,
    active: &BTreeMap<HomeSlotKey, ActiveScalarGcHome>,
    values: &ScalarValues<'_>,
    reference_captured_temps: &BTreeSet<TempId>,
    uses: &TempUseEvents<'_>,
    facts: &ProtoPromotionFacts,
) -> Option<(ScalarValueId, TempId)> {
    let HirStmt::If(if_stmt) = stmt else {
        return None;
    };
    let (checked_temp, non_nil_block) = match &if_stmt.cond {
        HirExpr::Binary(binary) if binary.op == HirBinaryOpKind::Eq => {
            let temp = nil_compared_temp(&binary.lhs, &binary.rhs)?;
            (temp, if_stmt.else_block.as_ref()?)
        }
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
            let HirExpr::Binary(binary) = &unary.expr else {
                return None;
            };
            if binary.op != HirBinaryOpKind::Eq {
                return None;
            }
            let temp = nil_compared_temp(&binary.lhs, &binary.rhs)?;
            (temp, &if_stmt.then_block)
        }
        _ => return None,
    };
    let value_id = values.by_temp.get(&checked_temp).copied()?;
    let root_home = values.global_home(value_id)?;
    let root = active.get(&root_home)?;
    // copy 沿用 identity，却不能重新建立已覆盖的直接 lookup 事务。
    if root.value_id != value_id || !root.direct_result_home || !root.pure_scope_end_copy_root {
        return None;
    }

    let mut branch_aliases = BTreeSet::new();
    let mut handoff_owner = None;
    for branch_stmt in &non_nil_block.stmts {
        let (target, value) = branch_stmt.scalar_temp_assignment()?;
        let HirExpr::TempRef(source) = value else {
            return None;
        };
        if values.by_temp.get(source) != Some(&value_id) && !branch_aliases.contains(source) {
            return None;
        }
        branch_aliases.insert(target);
        let target_home = facts.trusted_temp_home_slot(target)?;
        if reference_captured_temps.contains(&target)
            && uses.has_live_read_after(target, index)
            && target_home != root_home
        {
            handoff_owner = Some(target);
        }
    }
    handoff_owner.map(|owner| (value_id, owner))
}

fn nil_compared_temp(lhs: &HirExpr, rhs: &HirExpr) -> Option<TempId> {
    match (lhs, rhs) {
        (HirExpr::TempRef(temp), HirExpr::Nil) | (HirExpr::Nil, HirExpr::TempRef(temp)) => {
            Some(*temp)
        }
        _ => None,
    }
}

fn record_lookup_root_overwrite(
    root: ActiveScalarGcHome,
    index: usize,
    home: HomeSlotKey,
    overwrite_is_eligible: bool,
    uses: &TempUseEvents<'_>,
    values: &ScalarValues<'_>,
    lifetimes: &mut ScalarGcRootLifetimeIndices,
) {
    if (root.required_scratch_write || values.global_home(root.value_id).is_none())
        && root.eligible
        && overwrite_is_eligible
        && !root
            .aliases
            .iter()
            .any(|alias| uses.has_live_read_after(*alias, index))
    {
        // 是否必须新增 root 与原 home 何时结束是两份事实。即使没有识别到显式 GC，
        // 后续任意 callback 都能观察多保留的 lookup 值；已物化 owner 必须消费原端点。
        if root.required_scratch_write
            || root.crossed_observation
            || values.observed(&root, index + 1, root.has_overwrite_proof)
            || (uses.has_gc_fence_after(index)
                && values.crossed_observer_before(root.root_index, index))
        {
            lifetimes.roots.insert(root.root_index);
            lifetimes.retained_overwrites.insert(index);
        }
        if values.exposed(root.value_id) {
            lifetimes.retained_overwrites.insert(index);
        }
        lifetimes
            .roots_by_overwrite
            .entry(index)
            .or_default()
            .push(PhysicalRootOwner {
                root_index: root.root_index,
                home,
            });
    }
}

fn preserve_observed_scope_end_root(
    root: &ActiveScalarGcHome,
    values: &ScalarValues<'_>,
    end: usize,
    lifetimes: &mut ScalarGcRootLifetimeIndices,
) {
    if root.eligible && root.pure_scope_end_copy_root && values.observed(root, end, false) {
        lifetimes.roots.insert(root.root_index);
    }
}

fn preserve_lookup_roots_to_scope_end(
    active: &BTreeMap<HomeSlotKey, ActiveScalarGcHome>,
    values: &ScalarValues<'_>,
    end: usize,
    lifetimes: &mut ScalarGcRootLifetimeIndices,
) {
    // collector 按 HirBlock 独立运行，locals pass 也把 producer 提升为同一 block 内的词法
    // local。active 说明本 block 内没有已证明的同-home overwrite；一旦离开 block，源码
    // local 的作用域自然终止，所以无需也不能把 parent successor 的 home 复用算进这里。
    // regress_396 覆盖 child-if 后立即复用该 home 的边界。
    lifetimes.roots.extend(
        active
            .values()
            .filter(|root| {
                root.eligible
                    && (root.required_scratch_write
                        || root.crossed_observation
                        || values.observed(root, end, false))
                    && (root.required_scratch_write
                        || values.global_home(root.value_id).is_none()
                        || root.pure_scope_end_copy_root)
            })
            .map(|root| root.root_index),
    );
}

/// 将 return 表达式里“值已经被子表达式消费、随后仍跨过潜在用户代码/GC 事件”的
/// lookup transaction 转成显式 root 观察事实。
///
/// 普通二元/一元/call 的当前 operands 在 operator/call 执行期间仍由表达式临时槽持有；
/// 因此当前节点自身的事件只要求保留更早已经消费的 lookup identity。逻辑短路、
/// constructor、closure 与 Decision 另有条件执行或强引用 handoff，当前证明不跨层猜测。
fn observe_lookup_return_post_use_roots(
    values: &crate::hir::common::HirValuePack,
    definitions: &BTreeMap<TempId, &HirExpr>,
    value_by_temp: &BTreeMap<TempId, ScalarValueId>,
    active: &mut BTreeMap<HomeSlotKey, ActiveScalarGcHome>,
    safety: HirExprSafety,
) {
    if active.is_empty() {
        return;
    }
    let Some(needs_independent_root) =
        return_roots::observed_return_roots(values, definitions, value_by_temp, safety)
    else {
        return;
    };

    for root in active.values_mut() {
        if root.direct_result_home
            && root.scope_end_copy_root
            && needs_independent_root.contains(&root.value_id)
        {
            root.crossed_observation = true;
        }
    }
}

fn exact_multi_nil_home_overwrites(
    stmt: &HirStmt,
    facts: &ProtoPromotionFacts,
    temp_is_eligible: &mut impl FnMut(TempId) -> bool,
) -> Option<Vec<ExactNilHomeOverwrite>> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    if assign.targets.len() < 2
        || assign.targets.len() != assign.values.fixed.len()
        || assign.values.tail.is_some()
        || !assign
            .values
            .fixed
            .iter()
            .all(|value| matches!(value, HirExpr::Nil))
    {
        return None;
    }
    let mut overwrites = BTreeMap::<HomeSlotKey, ExactNilHomeOverwrite>::new();
    for target in &assign.targets {
        let (temp, possible_homes, home) = match target {
            HirLValue::Temp(temp) => (
                Some(*temp),
                facts.possible_temp_home_slots(*temp)?,
                facts.trusted_temp_home_slot(*temp),
            ),
            HirLValue::Local(local) => (
                None,
                facts.possible_local_home_slots(*local)?,
                facts.trusted_local_home_slot(*local),
            ),
            HirLValue::Param(param) => (
                None,
                facts.possible_param_home_slots(*param)?,
                facts.trusted_param_home_slot(*param),
            ),
            HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_) => {
                return None;
            }
        };
        if possible_homes.is_empty() {
            // Synthetic home-free targets participate in the HIR parallel assignment but do not
            // write a physical VM cell. They therefore cannot prevent the exact physical members
            // of the same nil transaction from closing their preceding root epochs.
            continue;
        }
        let home = home?;
        let eligible = temp.is_some_and(&mut *temp_is_eligible);
        let overwrite = overwrites
            .entry(home)
            .or_insert_with(|| ExactNilHomeOverwrite {
                temps: BTreeSet::new(),
                home,
                eligible: true,
            });
        overwrite.temps.extend(temp);
        overwrite.eligible &= eligible;
    }
    // Literal nil 没有求值事件；同 home 的全部 target 是同一次物理覆盖事务，并共同
    // 承接相同的 nil 后态。资格按组取交集，避免只提升其中一部分 identity-sensitive temp。
    (!overwrites.is_empty()).then(|| overwrites.into_values().collect())
}

/// fixed call 的完整结果目标与互异 trusted home；物化与生命周期分析共享该 HIR 证明。
pub(super) fn exact_multi_call_home_targets(
    stmt: &HirStmt,
    facts: &ProtoPromotionFacts,
) -> Option<Vec<(TempId, HomeSlotKey)>> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let tail = assign.values.tail.as_ref()?;
    if assign.targets.len() < 2
        || !assign.values.fixed.is_empty()
        || tail.exact_width() != Some(assign.targets.len())
        || !matches!(tail.as_expr(), HirExpr::Call(_))
    {
        return None;
    }

    let mut temp_homes = Vec::with_capacity(assign.targets.len());
    let mut distinct_homes = BTreeSet::new();
    for target in &assign.targets {
        let HirLValue::Temp(temp) = target else {
            return None;
        };
        let home = facts.trusted_temp_home_slot(*temp)?;
        if !distinct_homes.insert(home) {
            return None;
        }
        temp_homes.push((*temp, home));
    }

    Some(temp_homes)
}

fn definite_grouped_home_overwrite(
    stmt: &HirStmt,
    writes: RootEventStmt<'_>,
    home: HomeSlotKey,
    facts: &ProtoPromotionFacts,
    temp_is_eligible: &mut impl FnMut(TempId) -> bool,
) -> Option<ExactHomeOverwrite> {
    let temps = match stmt {
        HirStmt::Assign(assign) if assign.targets.len() > 1 => {
            if writes.has_boundary()
                || writes.has_unknown_home()
                || !writes.contains_home(home)
                || !assign.targets.iter().all(|target| {
                    matches!(target, HirLValue::Temp(temp) if facts.trusted_temp_home_slot(*temp).is_some())
                })
            {
                return None;
            }
            assign
                .targets
                .iter()
                .filter_map(|target| {
                    let HirLValue::Temp(temp) = target else {
                        return None;
                    };
                    (facts.trusted_temp_home_slot(*temp) == Some(home)).then_some(*temp)
                })
                .collect::<BTreeSet<_>>()
        }
        HirStmt::If(if_stmt) => {
            let else_block = if_stmt.else_block.as_ref()?;
            let then_temps =
                definite_block_home_overwrite(&if_stmt.then_block, writes.child(0), home, facts)?;
            let else_temps =
                definite_block_home_overwrite(else_block, writes.child(1), home, facts)?;
            then_temps.union(&else_temps).copied().collect()
        }
        HirStmt::Block(block) => {
            definite_block_home_overwrite(block, writes.child(0), home, facts)?
        }
        _ => return None,
    };
    if temps.is_empty() {
        return None;
    }
    let eligible = temps.iter().copied().all(temp_is_eligible);
    Some(ExactHomeOverwrite { temps, eligible })
}

fn grouped_assignment_targets_are_active(
    stmt: &HirStmt,
    facts: &ProtoPromotionFacts,
    home_is_active: impl FnMut(&HomeSlotKey) -> bool,
) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return true;
    };
    if assign.targets.len() <= 1 {
        return true;
    }
    let Some(target_homes) = assign
        .targets
        .iter()
        .map(|target| {
            let HirLValue::Temp(temp) = target else {
                return None;
            };
            facts.trusted_temp_home_slot(*temp)
        })
        .collect::<Option<BTreeSet<_>>>()
    else {
        return false;
    };
    target_homes.len() == assign.targets.len() && target_homes.iter().all(home_is_active)
}

fn definite_block_home_overwrite(
    block: &HirBlock,
    events: RootEventBlock<'_>,
    home: HomeSlotKey,
    facts: &ProtoPromotionFacts,
) -> Option<BTreeSet<TempId>> {
    let (first_index, first_temp) =
        events
            .home_write_positions_from(home, 0)
            .find_map(|index| {
                let (temp, _) = block.stmts[index].scalar_temp_assignment()?;
                (facts.trusted_temp_home_slot(temp) == Some(home)).then_some((index, temp))
            })?;
    let suffix = events.slice(first_index + 1..block.stmts.len());
    if !events.prefix(first_index).preserves_home(home)
        || suffix.has_boundary()
        || suffix.has_unknown_home()
        || !events
            .home_write_positions_from(home, first_index + 1)
            .all(|index| {
                block.stmts[index]
                    .scalar_temp_assignment()
                    .is_some_and(|(temp, _)| facts.trusted_temp_home_slot(temp) == Some(home))
            })
    {
        return None;
    }
    Some(BTreeSet::from([first_temp]))
}

fn stmt_is_transparent_temp_copy(stmt: &HirStmt, aliases: &BTreeSet<TempId>) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    matches!(
        (assign.targets.as_slice(), assign.values.fixed.as_slice(), &assign.values.tail),
        ([HirLValue::Temp(_)], [HirExpr::TempRef(source)], None)
            if aliases.contains(source)
    )
}

fn stmt_is_direct_if_control_read(
    stmt: &HirStmt,
    aliases: &BTreeSet<TempId>,
    scope: RootEventStmt<'_>,
) -> bool {
    let HirStmt::If(if_stmt) = stmt else {
        return false;
    };
    let reads_alias = match &if_stmt.cond {
        HirExpr::TempRef(temp) => aliases.contains(temp),
        HirExpr::Unary(unary) => {
            matches!(&unary.expr, HirExpr::TempRef(temp) if aliases.contains(temp))
        }
        _ => false,
    };
    reads_alias && scope.consumes_only_control_head(stmt, aliases)
}

/// 两个原始 home 都保活到 frame end，且当前 HIR 仍保留相同值的覆盖关系。
/// 消费者删除 target copy 后必须把 source 作为 PhysicalRoot 物化，不能据此继续内联 source。
pub(super) struct ScopeEndCopyRootHandoff {
    pub(super) target: TempId,
    pub(super) source: TempId,
    pub(super) copy_index: usize,
    pub(super) target_home: HomeSlotKey,
    pub(super) source_home: HomeSlotKey,
}

pub(super) fn scope_end_copy_root_handoffs(
    stmts: &[HirStmt],
    facts: &ProtoPromotionFacts,
    mut preserves_home: impl FnMut(std::ops::Range<usize>, HomeSlotKey) -> bool,
) -> Vec<ScopeEndCopyRootHandoff> {
    let Some((HirStmt::Return(_), prefix)) = stmts.split_last() else {
        return Vec::new();
    };
    let mut first_definitions = BTreeMap::new();
    let mut handoffs = Vec::new();
    for (copy_index, stmt) in prefix.iter().enumerate() {
        let Some((target, value)) = stmt.scalar_temp_assignment() else {
            continue;
        };
        first_definitions.entry(target).or_insert(copy_index);
        let HirExpr::TempRef(source) = value else {
            continue;
        };
        // 前层非资源旧值证明删除 copy 不会丢失另一个旧对象的释放点；两个纯 scope-end
        // transaction 则证明共享值不需要在不同的动态 endpoint 分别释放。
        if !facts.overwrites_gc_inert(target)
            || !facts.is_pure_scope_end_copy_root_temp(target)
            || !facts.is_pure_scope_end_copy_root_temp(*source)
        {
            continue;
        }
        let (Some(target_home), Some(source_home)) = (
            facts.trusted_temp_home_slot(target),
            facts.trusted_temp_home_slot(*source),
        ) else {
            continue;
        };
        if target_home == source_home {
            continue;
        }
        let Some(&source_index) = first_definitions.get(source) else {
            continue;
        };
        if source_index >= copy_index {
            continue;
        }
        // 当前 HIR 必须继续满足原始 home 的无覆盖合同；opaque control/cleanup
        // 边界不能用原始负向 root 标记推导出正向覆盖证明。
        if !preserves_home(source_index + 1..prefix.len(), source_home)
            || !preserves_home(copy_index + 1..prefix.len(), target_home)
        {
            continue;
        }
        handoffs.push(ScopeEndCopyRootHandoff {
            target,
            source: *source,
            copy_index,
            target_home,
            source_home,
        });
    }
    handoffs
}

pub(super) fn scope_end_copy_roots_needing_materialization(
    stmts: &[HirStmt],
    facts: &ProtoPromotionFacts,
) -> BTreeSet<TempId> {
    let mut collector = ScopeEndRootCollector {
        roots: BTreeSet::new(),
        facts,
    };
    visit_stmts(stmts, &mut collector);
    collector.roots
}

struct ScopeEndRootCollector<'a> {
    roots: BTreeSet<TempId>,
    facts: &'a ProtoPromotionFacts,
}

impl ScopeEndRootCollector<'_> {
    fn control_test(&mut self, expr: &HirExpr) {
        let temp = match expr {
            HirExpr::TempRef(temp) => Some(*temp),
            HirExpr::Unary(unary) => match &unary.expr {
                HirExpr::TempRef(temp) => Some(*temp),
                _ => None,
            },
            _ => None,
        };
        if let Some(temp) = temp
            && self.facts.is_scope_end_copy_root_temp(temp)
        {
            self.roots.insert(temp);
        }
    }
}

impl HirVisitor<'_> for ScopeEndRootCollector<'_> {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        if let HirStmt::GenericFor(for_stmt) = stmt {
            self.roots.extend(
                for_stmt
                    .initializer_roots
                    .iter()
                    .copied()
                    .filter(|temp| self.facts.is_scope_end_copy_root_temp(*temp)),
            );
        }
        let HirStmt::If(if_stmt) = stmt else {
            return;
        };
        self.control_test(&if_stmt.cond);
    }

    fn visit_expr(&mut self, expr: &HirExpr) {
        match expr {
            // 同一原始 test 不因 If 变成短路表达式就失去低槽 root；例如 regress_562
            // 的 saved 在下一次高槽调用期间仍存活，源 TEST 自身没有结束这个 home。
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                self.control_test(&logical.lhs);
            }
            HirExpr::Decision(decision) => {
                for node in &decision.nodes {
                    self.control_test(&node.test);
                }
            }
            _ => {}
        }
    }
}

fn record_call_root_overwrite(
    root: ActiveCallRoot,
    index: usize,
    home: HomeSlotKey,
    eligible: bool,
    uses: &TempUseEvents<'_>,
    active: &CallValues<'_>,
    lifetimes: &mut CallRootLifetimeIndices,
) {
    // 普通表达式 forwarding 可由仍活读的同值副本接管；显式 GC 物化则必须同时保留
    // 原 home 的结束位置，不能因另一个 home 继续读该值而留下永不释放的源码 local。
    if !eligible || !root.eligible || active.has_live_read_after(root.value_id, home) {
        return;
    }
    if root.transferred || root.explicit_fence_only && uses.has_gc_fence_after(index) {
        // 参数交接停止选择新增根，但不允许提前内联掉已有 owner 的最后覆写。
        // COPY 也可因多次逻辑读取而在 locals 中物化，即使其原存活窗口没有显式 GC。
        // 后续 GC 能观察延长的旧根，因此先保留精确结束写；物化选择仍留给 binding
        // owner，不能为了保住端点而把每个透明 COPY 升级成必须新增的 root。
        lifetimes.retained_overwrites.insert(index);
    }
    if !root.transferred
        && root.observed
        && (root.preserved
            || uses.has_gc_fence_after(index)
            || !active.value_has_live_read_after(root.value_id))
    {
        lifetimes.preserve_call_root(&root, home);
    }
    lifetimes
        .roots_by_overwrite
        .entry(index)
        .or_default()
        .push(PhysicalRootOwner {
            root_index: root.root_index,
            home,
        });
}

fn preserve_active_call_roots(
    active: &mut CallValues<'_>,
    lifetimes: &mut CallRootLifetimeIndices,
) {
    for home in active.pending(true) {
        active.observe(home, true);
        let root = active.get(&home).unwrap();
        lifetimes.preserve_call_root(root, home);
    }
}

fn observe_active_call_values(active: &mut CallValues<'_>, values: Option<&BTreeSet<CallValueId>>) {
    let homes = values.map_or_else(
        || active.pending(false),
        |values| {
            values
                .iter()
                .filter_map(|value| active.representative(*value, false))
                .collect()
        },
    );
    for home in homes {
        active.observe(home, false);
    }
}

pub(super) fn stmt_may_observe_gc_roots(stmt: &HirStmt, safety: HirExprSafety) -> bool {
    let mut collector = HirEvalEffects::new(safety, |stmt| matches!(stmt, HirStmt::GenericFor(_)));
    visit_stmts(std::slice::from_ref(stmt), &mut collector);
    collector.found()
}

/// 逆序扫描中该 local 到下一次直属覆盖的观察事实；只在自身读写事件上更新。
struct LocalRootSuffix {
    next_event: usize,
    has_live_read: bool,
    observed: bool,
}

#[derive(Default)]
struct LocalUseCollector {
    reads: BTreeSet<LocalId>,
    writes: BTreeSet<LocalId>,
}

impl HirVisitor<'_> for LocalUseCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        if let HirStmt::LocalDecl(decl) = stmt {
            self.writes.extend(decl.bindings.iter().copied());
        }
    }

    fn visit_expr(&mut self, expr: &HirExpr) {
        if let HirExpr::LocalRef(local) = expr {
            self.reads.insert(*local);
        }
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        if let HirLValue::Local(local) = lvalue {
            self.writes.insert(*local);
        }
    }
}

pub(super) struct RootLifetimeFacts<'a> {
    stmts: &'a [HirStmt],
    uses: TempUseEvents<'a>,
    scalar_definitions: std::cell::OnceCell<BTreeMap<TempId, &'a HirExpr>>,
}

impl<'a> RootLifetimeFacts<'a> {
    pub(super) fn new(
        stmts: &'a [HirStmt],
        facts: &ProtoPromotionFacts,
        safety: HirExprSafety,
    ) -> Self {
        Self::with_events(stmts, facts, safety, None)
    }

    pub(super) fn with_events(
        stmts: &'a [HirStmt],
        facts: &ProtoPromotionFacts,
        safety: HirExprSafety,
        block: Option<RootEventBlock<'a>>,
    ) -> Self {
        let events = match block {
            Some(block) => RootEvents::Shared(block.prefix(stmts.len())),
            None => RootEvents::Owned(Box::new(RootEventIndex::new(stmts, facts, safety))),
        };
        let scope = events.block();
        let gc_fence_indices = collect_gc_fences(stmts, scope);
        Self {
            stmts,
            scalar_definitions: std::cell::OnceCell::new(),
            uses: TempUseEvents {
                events,
                gc_fence_indices,
            },
        }
    }

    fn stack_writes_at(&self, index: usize) -> RootEventStmt<'_> {
        self.uses.events.block().stmt(index)
    }

    fn scalar_definitions(&self) -> &BTreeMap<TempId, &'a HirExpr> {
        self.scalar_definitions.get_or_init(|| {
            self.stmts
                .iter()
                .filter_map(HirStmt::scalar_temp_assignment)
                .collect()
        })
    }
}

enum RootEvents<'a> {
    Shared(RootEventBlock<'a>),
    Owned(Box<RootEventIndex>),
}

impl RootEvents<'_> {
    fn block(&self) -> RootEventBlock<'_> {
        match self {
            Self::Shared(block) => *block,
            Self::Owned(index) => index.root(),
        }
    }
}

struct TempUseEvents<'a> {
    events: RootEvents<'a>,
    gc_fence_indices: BTreeSet<usize>,
}

impl TempUseEvents<'_> {
    fn argument_transfers_at<I: Iterator<Item = TempId>>(
        &self,
        index: usize,
        facts: &ProtoPromotionFacts,
        candidate_count: usize,
        candidates: impl FnOnce() -> I,
    ) -> BTreeSet<(TempId, usize, HomeSlotKey)> {
        let events = self.events.block().argument_transfers(index);
        let transfer = |temp| self.argument_transfer_at(temp, index, facts);
        if events.len() < candidate_count {
            events
                .iter()
                .filter_map(|(_, temp)| transfer(*temp))
                .collect()
        } else {
            candidates().filter_map(transfer).collect()
        }
    }

    /// 只查询已绑定的候选 alias，唯一 producer 和端点仍须在整个 block 域内成立。
    fn argument_transfer_at(
        &self,
        temp: TempId,
        index: usize,
        facts: &ProtoPromotionFacts,
    ) -> Option<(TempId, usize, HomeSlotKey)> {
        let (producer, site) = self.argument_transfer(temp)?;
        if site != index {
            return None;
        }
        Some((temp, producer, facts.trusted_temp_home_slot(temp)?))
    }

    fn argument_transfer(&self, temp: TempId) -> Option<(usize, usize)> {
        let scope = self.events.block();
        let events = scope.temp(temp)?;
        let [producer] = scope.positions(&events.writes) else {
            return None;
        };
        let [site] = scope.positions(&events.argument_transfers) else {
            return None;
        };
        let (producer, site) = (scope.ordinal(*producer), scope.ordinal(*site));
        (producer < site).then_some((producer, site))
    }

    fn has_argument_transfer(&self, temp: TempId, producer: usize, overwrite: usize) -> bool {
        self.argument_transfer(temp)
            .is_some_and(|(origin, site)| origin == producer && site <= overwrite)
    }

    fn has_live_read_after(&self, temp: TempId, index: usize) -> bool {
        self.has_live_read_from(temp, index + 1)
    }

    fn has_live_read_from(&self, temp: TempId, index: usize) -> bool {
        let scope = self.events.block();
        let Some(events) = scope.temp(temp) else {
            return false;
        };
        let read = scope.next(&events.reads, index);
        let write = scope.next(&events.writes, index);
        read.is_some_and(|read| write.is_none_or(|write| read <= write))
    }

    /// boundary 是直属语句之后的位置。一次跳过该语句的全部后代重复事件，
    /// 只在已绑定 alias 到达该点时计算活性，不预展开未消费的后缀或 temp 域。
    fn next_read_write_boundary(&self, temp: TempId, after: usize) -> Option<usize> {
        let scope = self.events.block();
        let events = scope.temp(temp)?;
        scope
            .next(&events.reads, after)
            .into_iter()
            .chain(scope.next(&events.writes, after))
            .min()
            .map(|index| index + 1)
    }

    fn has_read_at(&self, temp: TempId, index: usize) -> bool {
        self.events.block().has_read_at(temp, index)
    }

    fn has_write_at(&self, temp: TempId, index: usize) -> bool {
        let scope = self.events.block();
        scope
            .temp(temp)
            .is_some_and(|events| scope.contains(&events.writes, index))
    }

    fn has_gc_fence_after(&self, index: usize) -> bool {
        self.gc_fence_indices.range((index + 1)..).next().is_some()
    }

    fn is_gc_fence(&self, index: usize) -> bool {
        self.gc_fence_indices.contains(&index)
    }
}

fn collect_gc_fences(stmts: &[HirStmt], events: RootEventBlock<'_>) -> BTreeSet<usize> {
    let mut aliases = BTreeSet::new();
    let mut fences = BTreeSet::new();
    let mut writes = Vec::new();
    for (index, stmt) in stmts.iter().enumerate() {
        if events.is_gc_fence(index, &aliases) {
            fences.insert(index);
        }
        let is_alias = |value: Option<&HirExpr>| {
            value.is_some_and(|value| {
                matches!(value, HirExpr::GlobalRef(global) if global.key.as_bytes() == b"collectgarbage")
                    || HirBinding::from_expr(value).is_some_and(|binding| aliases.contains(&binding))
            })
        };
        // 所有 RHS 读取同一个旧快照；即使 f,g=g,f 或 f=f，也先求值再更新目标。
        // MOVE 只转交 callable 身份，不能丢掉之后 GC 对旧物理根覆盖端点的观察。
        match stmt {
            HirStmt::Assign(assign) => {
                writes.extend(assign.targets.iter().enumerate().filter_map(|(i, target)| {
                    HirBinding::from_lvalue(target)
                        .filter(|binding| {
                            matches!(binding, HirBinding::Temp(_) | HirBinding::Local(_))
                        })
                        .map(|binding| (binding, is_alias(assign.values.result_source(i))))
                }))
            }
            HirStmt::LocalDecl(decl) => {
                writes.extend(decl.bindings.iter().enumerate().map(|(i, local)| {
                    (
                        HirBinding::Local(*local),
                        is_alias(decl.values.result_source(i)),
                    )
                }))
            }
            HirStmt::LocalRootRelease(local) => writes.push((HirBinding::Local(*local), false)),
            HirStmt::If(_)
            | HirStmt::While(_)
            | HirStmt::Repeat(_)
            | HirStmt::NumericFor(_)
            | HirStmt::GenericFor(_)
            | HirStmt::Block(_) => {
                // 本投影不求解分支后态；嵌套调用已按入口别名纳入当前语句。
                events.invalidate_written_aliases(index, &mut aliases);
                continue;
            }
            HirStmt::Label(_) | HirStmt::Goto(_) => {
                aliases.clear();
                continue;
            }
            _ => continue,
        };
        for (binding, known) in writes.drain(..) {
            if known {
                aliases.insert(binding);
            } else {
                aliases.remove(&binding);
            }
        }
    }
    fences
}

#[derive(Default)]
struct TempWriteCollector {
    temps: Vec<TempId>,
    argument_transfers: Vec<TempId>,
}

impl HirVisitor<'_> for TempWriteCollector {
    fn visit_call(&mut self, call: &HirCallExpr) {
        for root in &call.argument_roots {
            if call.transfers_argument_root(root.producer) {
                self.argument_transfers.push(root.producer);
            }
        }
    }
    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        if let HirLValue::Temp(temp) = lvalue {
            self.temps.push(*temp);
        }
    }
}

fn method_receiver_protocol_sink(
    stmts: &[HirStmt],
    begin: usize,
    end: usize,
    receiver: TempId,
) -> Option<(usize, usize)> {
    let mut matches = Vec::new();
    for (lookup_index, lookup_stmt) in stmts.iter().enumerate().take(end).skip(begin) {
        let Some((callee, HirExpr::TableAccess(access))) = lookup_stmt.scalar_temp_assignment()
        else {
            continue;
        };
        let HirExpr::TempRef(base) = &access.base else {
            continue;
        };
        if *base != receiver {
            continue;
        }

        for (sink_index, sink_stmt) in stmts.iter().enumerate().take(end).skip(lookup_index + 1) {
            let Some(call) = direct_call_in_stmt(sink_stmt) else {
                continue;
            };
            if super::method_protocol::match_method_setup_pair(
                access,
                &HirExpr::TempRef(callee),
                call,
            )
            .is_some()
            {
                matches.push((lookup_index, sink_index));
            }
        }
    }
    let [candidate] = matches.as_slice() else {
        return None;
    };
    Some(*candidate)
}

fn call_with_inert_dispatch_prefix(stmt: &HirStmt, safety: HirExprSafety) -> Option<&HirCallExpr> {
    let call = direct_call_in_stmt(stmt)?;
    // 只能在当前 callee/参数求值无观察时，于 statement 前释放精确 dispatch 终止的根。
    // 表/global 目标在调用前也可能求值，不允许把释放前移越过这些事件。
    (!matches!(stmt, HirStmt::Assign(assign)
        if assign.targets.iter().any(|target| matches!(target,
            HirLValue::TableAccess(_) | HirLValue::Global(_))))
        && safety.is_discard_safe_without_residual(&call.callee)
        && call.args.tail.is_none()
        && call
            .args
            .fixed
            .iter()
            .all(|arg| safety.is_discard_safe_without_residual(arg)))
    .then_some(call)
}

fn direct_call_in_stmt(stmt: &HirStmt) -> Option<&HirCallExpr> {
    let values = match stmt {
        HirStmt::CallStmt(call_stmt) => return Some(&call_stmt.call),
        HirStmt::LocalDecl(local_decl) => &local_decl.values,
        HirStmt::Assign(assign) => &assign.values,
        HirStmt::Return(ret) => &ret.values,
        _ => return None,
    };
    let mut expressions = values.iter();
    let HirExpr::Call(call) = expressions.next()? else {
        return None;
    };
    expressions.next().is_none().then_some(call)
}

struct AllocationRootState<'a> {
    active: &'a mut AllocationHomes,
    lifetimes: &'a mut CallRootLifetimeIndices,
    uses: &'a TempUseEvents<'a>,
}

fn update_allocation_roots(
    state: &mut AllocationRootState<'_>,
    index: usize,
    temp: TempId,
    value: &HirExpr,
    slot: HomeSlotKey,
    eligible: bool,
) {
    // 必须在移除 target 别名前解析 source，保留 t=t 与同值写回已有 home 的原事务。
    let source_site = match value {
        HirExpr::TempRef(source) => state.active.site_for_temp(*source),
        _ => None,
    };
    let continues_home = source_site.is_some_and(|site| {
        state
            .active
            .get(&slot)
            .is_some_and(|root| !root.transferred && root.allocation_site == site)
    });
    if continues_home {
        state.lifetimes.continuation_owners.insert(
            index,
            PhysicalRootOwner {
                root_index: state.active.get(&slot).unwrap().owner.definition_index,
                home: slot,
            },
        );
    }
    state.active.forget_temp(temp);
    if !continues_home {
        terminate_allocation_home(
            state.active,
            state.lifetimes,
            state.uses,
            index,
            slot,
            eligible,
        );
    }
    let allocation_site = source_site.or(match value {
        HirExpr::TableConstructor(_) => Some(AllocationSite(index)),
        _ => None,
    });
    if let Some(allocation_site) = allocation_site {
        state.active.bind(
            slot,
            temp,
            allocation_site,
            AllocationHomeOwner {
                definition_index: index,
                eligible,
            },
        );
    }
}

fn terminate_allocation_home(
    active: &mut AllocationHomes,
    lifetimes: &mut CallRootLifetimeIndices,
    uses: &TempUseEvents<'_>,
    index: usize,
    home: HomeSlotKey,
    eligible: bool,
) {
    if let Some(root) = active.remove(&home) {
        record_allocation_root_overwrite(&root, index, home, eligible, uses, lifetimes);
    }
}

fn record_allocation_root_overwrite(
    root: &ActiveAllocationHome,
    index: usize,
    home: HomeSlotKey,
    eligible: bool,
    uses: &TempUseEvents<'_>,
    lifetimes: &mut CallRootLifetimeIndices,
) {
    let owner = root.owner;
    if owner.eligible
        && eligible
        && !root
            .aliases
            .iter()
            .any(|alias| uses.has_live_read_after(*alias, index))
    {
        let root_index = owner.definition_index;
        // 交接后的端点仅供已物化 owner 消费。单独固定 endpoint 会阻断完整调用事务，
        // 反而迫使原本可消费的参数副本成为跨调用的源码强引用。
        if !root.transferred {
            lifetimes.roots.insert(root_index);
            lifetimes
                .root_homes
                .entry(root_index)
                .or_default()
                .insert(home);
        }
        lifetimes
            .roots_by_overwrite
            .entry(index)
            .or_default()
            .push(PhysicalRootOwner { root_index, home });
    }
}

#[derive(Default)]
struct StackWriteSummary {
    homes: BTreeSet<HomeSlotKey>,
    has_unknown_home: bool,
    has_boundary: bool,
}

impl StackWriteSummary {
    fn note_home(&mut self, home: Option<HomeSlotKey>) {
        match home {
            Some(home) => {
                self.homes.insert(home);
            }
            None => self.has_unknown_home = true,
        }
    }
}

struct StackWriteCollector<'a> {
    facts: &'a ProtoPromotionFacts,
    summary: &'a mut StackWriteSummary,
}

impl HirVisitor<'_> for StackWriteCollector<'_> {
    fn visit_local_root_release(&mut self, _local: LocalId) {}

    fn visit_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            // TBC 正常激活只登记 cleanup 链，不写 TValue；失败路径不会继续到后续覆盖。
            // 资源 identity 与声明配对仍由各自 owner 保护，真正执行用户 cleanup 的 Close 保持边界。
            HirStmt::ToBeClosed(_) => {}
            HirStmt::LocalDecl(local_decl) => {
                for local in &local_decl.bindings {
                    self.note_local(*local);
                }
            }
            HirStmt::GenericFor(for_stmt) => {
                for result in &for_stmt.dispatch_results {
                    self.summary
                        .note_home(self.facts.home_slot(result.result_def));
                }
            }
            HirStmt::NumericFor(for_stmt) => {
                for home in for_stmt.control_homes {
                    self.summary.note_home(Some(home));
                }
            }
            HirStmt::GlobalDecl(_)
            | HirStmt::Close(_)
            | HirStmt::Return(_)
            | HirStmt::Goto(_)
            | HirStmt::Label(_) => self.summary.has_boundary = true,
            _ => {}
        }
    }

    fn visit_expr(&mut self, expr: &HirExpr) {
        if matches!(expr, HirExpr::Decision(_) | HirExpr::Unresolved(_)) {
            self.summary.has_boundary = true;
        }
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        match lvalue {
            HirLValue::Param(param) => self.note_param(*param),
            HirLValue::Temp(temp) => self.summary.note_home(self.facts.home_slot(*temp)),
            HirLValue::Local(local) => self.note_local(*local),
            HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_) => {}
        }
    }
}

impl StackWriteCollector<'_> {
    fn note_param(&mut self, param: ParamId) {
        self.summary
            .note_home(self.facts.trusted_param_home_slot(param));
    }

    fn note_local(&mut self, local: LocalId) {
        self.summary
            .note_home(self.facts.trusted_local_home_slot(local));
    }
}
