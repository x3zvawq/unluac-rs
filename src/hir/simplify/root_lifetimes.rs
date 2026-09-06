//! 这个文件识别普通 HIR 值活跃性看不到的物理槽 root 生命周期。
//!
//! fixed call result（包括已物化 local）、已逃逸 table allocation，以及已跨后续观察点的
//! table/global lookup result，即使没有 HIR 读取，也会在同一 stack home 被覆盖前继续充当
//! VM GC root。ordinary call 的参数槽由前层标记交接给 callee，只有当前唯一 producer 与
//! call 参数端点仍匹配时才排除跨调用的 allocation-root 配对，不能把 callee 可覆盖的槽
//! 物化为额外 caller local。例如 `f({})` 在 f 内丢弃参数后允许对象回收。
//! Promotion 另会发布普通 copy root 的单结果 call + 紧邻 MOVE 终点；本层只按 producer / endpoint
//! temp 与 overwritten home 完整匹配，把它接入同一 local-owner handoff，不从 HIR 相邻文本猜 opcode。
//! allocation 的内部 aggregate 存储由共享 object_flow 证明是否真正逃逸，不能仅凭
//! store 外形把不同 value epoch 合成一个 local。缺失正向证明时仍保留原配对。
//! copy 共享值 identity，
//! 但每个目标 home 都是独立 root transaction；同一 parallel overwrite 可终止多个 home，
//! 消费者只能把 producer 与同 home 的精确覆盖配对。
//! 分析只在单个 block 内追踪；只有 nested structure 不写 active home，且没有 opaque transfer
//! 或 cleanup 边界时才允许穿过。消费者可以保留已配对的两次 materialization，也可以在
//! 更窄的改写仍保持同一覆盖事务时，连同 owner 已证明的 physical home 一起消费该 pair。
//! 同值 frame-end copy 的覆盖证明同时消费前层非资源旧值与两个完整 root transaction，
//! 并复核当前 HIR 未改写 home；删除副本的 owner 必须物化原值根，不能只抹掉负向标记。
//! 潜在求值事件与分支覆盖值的 GC 惰性统一消费入口按目标方言构造的表达式安全上下文。
//! 同一语句快照的读写、参数交接与 GC fence 索引由 RootLifetimeFacts 共享；借用期间
//! 不允许改写语句，例如 locals 可用同一快照分别配对 call 与 lookup 的覆盖端点。
//! 两类端点共用 producer/home 身份，前缀查询只投影已保活且在边界前正向闭合的事务；
//! locals 据此建立一次成员索引，不按每个候选重扫语句前缀。

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::hir::common::{
    HirAssign, HirBinaryOpKind, HirBlock, HirCallExpr, HirExpr, HirLValue, HirStmt, HirUnaryOpKind,
    HirValuePack, LocalId, ParamId, TempId,
};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

mod allocation_homes;
mod call_values;
mod lookup_values;
mod return_lookup;

use allocation_homes::{ActiveAllocationHome, AllocationHomes};
use call_values::CallValues;
use lookup_values::LookupValues;

use super::object_flow::RootAnalysisContext;
use super::temp_touch::{collect_temp_reads_by_stmt, stmt_consumes_temps_only_in_control_head};
use crate::hir::visit::{HirVisitor, visit_expr, visit_stmts};

/// 当前语句中必须只有一个仍匹配 producer 的参数交接端点；共享给内联和身份物化。
pub(super) fn stmt_has_argument_root_handoff(stmt: &HirStmt, temp: TempId) -> bool {
    struct Handoffs {
        temp: TempId,
        count: usize,
    }
    impl HirVisitor for Handoffs {
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
struct LookupValueId(usize);

struct ActiveLookupGcHome {
    value_id: LookupValueId,
    root_index: usize,
    aliases: BTreeSet<TempId>,
    eligible: bool,
    crossed_observation: bool,
    /// 该 home 由原始 lookup 写入；跨 home 的机械 copy 不是 return 后缀要保留的独立 owner。
    direct_lookup_home: bool,
    /// low CFG 已证明该原始 home 在观察事件后仍活到 frame end。
    scope_end_copy_root: bool,
    /// 所有动态路径都到 frame end，不需要同步提交更早的 overwrite endpoint。
    pure_scope_end_copy_root: bool,
}

#[derive(Clone, Copy)]
struct AllocationHomeOwner {
    producer: TempId,
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

#[derive(Default)]
pub(super) struct CallRootLifetimeIndices {
    roots: BTreeSet<usize>,
    root_homes: BTreeMap<usize, BTreeSet<HomeSlotKey>>,
    roots_by_overwrite: BTreeMap<usize, Vec<PhysicalRootOwner>>,
    continuation_owners: BTreeMap<usize, PhysicalRootOwner>,
    call_dispatch_releases: BTreeMap<usize, Vec<PhysicalRootOwner>>,
    pre_dispatch_releases: BTreeMap<usize, BTreeSet<TempId>>,
    allocation_sites: BTreeMap<usize, usize>,
    allocation_release_sites: BTreeMap<(usize, TempId), usize>,
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
pub(super) struct LookupGcRootLifetimeIndices {
    roots: BTreeSet<usize>,
    roots_by_overwrite: BTreeMap<usize, Vec<PhysicalRootOwner>>,
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
    trailing_condition: Option<&HirExpr>,
    safety: HirExprSafety,
) -> BTreeSet<LocalId> {
    let explicit_fences = collect_gc_fence_indices(stmts);
    let mut observations = stmts
        .iter()
        .enumerate()
        .filter_map(|(index, stmt)| stmt_may_observe_gc_roots(stmt, safety).then_some(index))
        .collect::<BTreeSet<_>>();
    let mut states = BTreeMap::<LocalId, LocalRootSuffix>::new();
    if let Some(condition) = trailing_condition {
        if expr_may_observe_gc_roots(condition, safety) {
            observations.insert(stmts.len());
        }
        let mut uses = LocalUseCollector::default();
        visit_expr(condition, &mut uses);
        for local in uses.reads {
            states.insert(
                local,
                LocalRootSuffix {
                    next_event: stmts.len(),
                    has_live_read: true,
                    observed: false,
                },
            );
        }
    }
    let mut roots = BTreeSet::new();
    for (index, stmt) in stmts.iter().enumerate().rev() {
        let mut uses = LocalUseCollector::default();
        visit_stmts(std::slice::from_ref(stmt), &mut uses);
        let mut direct_writes = BTreeSet::new();
        let mut call_result = None;
        match stmt {
            HirStmt::LocalRootRelease(local) => {
                direct_writes.insert(*local);
            }
            HirStmt::Assign(assign) => {
                direct_writes.extend(assign.targets.iter().filter_map(|target| match target {
                    HirLValue::Local(local) => Some(*local),
                    _ => None,
                }));
                if let ([HirLValue::Local(local)], [HirExpr::Call(_)], None) = (
                    assign.targets.as_slice(),
                    assign.values.fixed.as_slice(),
                    &assign.values.tail,
                ) {
                    call_result = Some(*local);
                }
            }
            HirStmt::LocalDecl(decl) => {
                direct_writes.extend(decl.bindings.iter().copied());
                if let ([local], [HirExpr::Call(_)], None) = (
                    decl.bindings.as_slice(),
                    decl.values.fixed.as_slice(),
                    &decl.values.tail,
                ) {
                    call_result = Some(*local);
                }
            }
            _ => {}
        }
        // 相邻读写事件之间的 future-read 状态不变，只查询该窗口是否存在观察点。
        // 同一语句中的读先于覆盖；nested write 改变 future-read，但不终止直属 call owner。
        for &local in uses.reads.union(&uses.writes) {
            let state = states.entry(local).or_insert(LocalRootSuffix {
                next_event: stmts.len() + 1,
                has_live_read: false,
                observed: false,
            });
            let gap = index + 1..state.next_event;
            state.observed |= explicit_fences.range(gap.clone()).next().is_some()
                || (!state.has_live_read && observations.range(gap).next().is_some());
            if direct_writes.contains(&local) {
                if call_result == Some(local) && state.observed {
                    roots.insert(local);
                }
                // 当前覆盖语句的求值仍可观察旧值，所以先消费新值的后缀，再处理当前观察。
                state.observed = false;
            }
            state.has_live_read = uses.reads.contains(&local);
            state.observed |= explicit_fences.contains(&index)
                || (!state.has_live_read && observations.contains(&index));
            state.next_event = index;
        }
    }
    roots
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

            let writes =
                StackWriteSummary::for_stmts(&stmts[(producer_index + 1)..=sink_index], facts);
            if writes.has_unknown_home || writes.has_boundary || writes.homes.contains(&source_home)
            {
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

impl LookupGcRootLifetimeIndices {
    pub(super) fn closed_roots_before(
        &self,
        end: usize,
    ) -> impl Iterator<Item = PhysicalRootOwner> {
        root_owners_before(&self.roots_by_overwrite, end)
    }

    pub(super) fn into_handoff_roots(self) -> BTreeSet<TempId> {
        self.handoff_roots
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
        self.roots_by_overwrite
            .get(&index)
            .into_iter()
            .flatten()
            .copied()
    }

    pub(super) fn mark_stmts(&self, marked: &mut [bool]) {
        for index in self.roots.iter().chain(self.roots_by_overwrite.keys()) {
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
    context: RootAnalysisContext<'_>,
    observe_potential_events: bool,
    mut producer_temp_is_eligible: impl FnMut(TempId) -> bool,
    mut overwrite_temp_is_eligible: impl FnMut(TempId) -> bool,
) -> CallRootLifetimeIndices {
    let stmts = snapshot.stmts;
    let uses = &snapshot.uses;
    let safety = context.safety;
    let opaque_allocations = stmts
        .iter()
        .filter_map(HirStmt::scalar_temp_assignment)
        .filter_map(|(temp, value)| {
            (matches!(value, HirExpr::TableConstructor(_)) && !producer_temp_is_eligible(temp))
                .then_some(temp)
        })
        .collect::<BTreeSet<_>>();
    let mut active = CallValues::new(uses);
    let mut active_allocations = AllocationHomes::default();
    let mut pending_copy_root_call_moves = BTreeMap::<HomeSlotKey, PendingCopyRootCallMove>::new();
    // Lua 编译器会用 literal nil 的纯 temp copy 清除同 home 的 allocation root；只沿这条
    // 无副作用链传播 nil 事实，其余写入必须先让旧事实失效。
    let mut known_nil_temps = BTreeSet::<TempId>::new();
    let mut lifetimes = CallRootLifetimeIndices::default();

    for (index, stmt) in stmts.iter().enumerate() {
        active.advance(index);
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
            if overwrite_temp_is_eligible(pending.endpoint)
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
        let mut current_writes = StackWriteSummary::for_stmt(stmt, facts);
        current_writes
            .homes
            .retain(|home| !matching_call_move_homes.contains(home));
        if current_writes.has_boundary || current_writes.has_unknown_home {
            pending_copy_root_call_moves.clear();
        } else {
            for home in &current_writes.homes {
                pending_copy_root_call_moves.remove(home);
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
        if let HirStmt::CallStmt(call_stmt) = stmt {
            let call = &call_stmt.call;
            // 只在当前 callee/参数求值不含观察事件时，才可在 statement 前释放。
            // 原始 dispatch 事实不允许把释放前移到已内联的 lookup、分配或嵌套调用之前。
            if !expr_may_observe_gc_roots(&call.callee, safety)
                && call.args.tail.is_none()
                && call
                    .args
                    .fixed
                    .iter()
                    .all(|arg| !expr_may_observe_gc_roots(arg, safety))
            {
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
                        || uses.reads_at(index).is_some_and(|reads| {
                            reads.iter().any(|temp| {
                                facts.trusted_temp_home_slot(*temp) == Some(home)
                                    && active.aliases(root.value_id).contains(temp)
                            })
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
        }
        let potential_observation = stmt_may_observe_gc_roots(stmt, safety);
        if uses.is_gc_fence(index) {
            preserve_active_call_roots(&mut active, &mut lifetimes);
        } else if observe_potential_events && potential_observation {
            // A potential user-code/GC event matters only if a later same-home overwrite proves
            // the end of this transaction. Unlike an explicit collection fence, this does not
            // by itself justify materializing every still-active call result.
            observe_active_call_values(&mut active, None);
        }
        let reads = uses.reads_at(index);
        let read_values = reads
            .into_iter()
            .flatten()
            .filter_map(|temp| active.value_for_temp(*temp))
            .collect::<BTreeSet<_>>();
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
                        || stmt_is_direct_if_control_read(stmt, aliases)
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
                        || definite_grouped_home_overwrite(stmt, *home, facts, &mut |_| true)
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
                .filter(|root| active.aliases(root.value_id).contains(source))
                .map(|root| root.root_index)
                .or_else(|| {
                    let root = active_allocations.get(&home)?;
                    (active_allocations.site_for_temp(*source) == Some(root.allocation_site))
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
            forget_written_known_nil_temps(stmt, &mut known_nil_temps);
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
                            overwrite_temp_is_eligible(*temp),
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
                        },
                    );
                }
                continue;
            }
            if let Some(overwrites) =
                exact_multi_nil_home_overwrites(stmt, facts, &mut overwrite_temp_is_eligible)
            {
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
            let mut proven_homes = BTreeSet::new();
            let grouped_assignment_is_complete =
                grouped_assignment_targets_are_active(stmt, facts, |home| {
                    active.get(home).is_some() || active_allocations.get(home).is_some()
                });
            // 共享写入摘要已枚举可能覆盖的 home；不为纯调用重扫全部活动对象。
            for home in current_writes.homes.iter().copied() {
                if !grouped_assignment_is_complete {
                    break;
                }
                if active.get(&home).is_none() && active_allocations.get(&home).is_none() {
                    continue;
                }
                let Some(overwrite) = definite_grouped_home_overwrite(
                    stmt,
                    home,
                    facts,
                    &mut overwrite_temp_is_eligible,
                ) else {
                    continue;
                };
                proven_homes.insert(home);
                let active_root_is_read = active.get(&home).is_some_and(|root| {
                    reads.is_some_and(|reads| {
                        active
                            .aliases(root.value_id)
                            .iter()
                            .any(|alias| reads.contains(alias))
                    })
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
            let mut writes = current_writes;
            writes.homes.retain(|home| !proven_homes.contains(home));
            if writes.has_boundary || writes.has_unknown_home {
                active.clear();
                active_allocations.clear();
            } else {
                for home in &writes.homes {
                    active.remove(home);
                    active.forget_home_aliases(*home);
                }
                active_allocations.remove_homes(&writes.homes);
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
        let overwrite_eligible = overwrite_temp_is_eligible(temp);
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
                .is_some_and(|root| active.aliases(root.value_id).contains(source)));
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
            }
            active_allocations.remove_homes(&extra_write_homes);
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
                },
            );
        }
    }

    // 物理槽复用不代表对象已被外部观察。共享对象流证明原始 allocation 在
    // 覆盖点仍未逃逸时，不把内部 aggregate 存储固化成同一 local 的释放事务。
    let allocation_roots = std::mem::take(&mut lifetimes.allocation_sites);
    let allocation_releases = std::mem::take(&mut lifetimes.allocation_release_sites);
    if !allocation_roots.is_empty() || !allocation_releases.is_empty() {
        let objects =
            super::object_flow::AllocationEscapeFacts::analyze(stmts, context, &opaque_allocations);
        for ((index, temp), site) in allocation_releases {
            if objects.proves_unescaped(site, &stmts[index])
                && let Some(releases) = lifetimes.pre_dispatch_releases.get_mut(&index)
            {
                releases.remove(&temp);
            }
        }
        lifetimes
            .pre_dispatch_releases
            .retain(|_, releases| !releases.is_empty());
        for (index, pairs) in &mut lifetimes.roots_by_overwrite {
            pairs.retain(|pair| {
                allocation_roots
                    .get(&pair.root_index)
                    .is_none_or(|site| !objects.proves_unescaped(*site, &stmts[*index]))
            });
        }
        lifetimes
            .roots_by_overwrite
            .retain(|_, pairs| !pairs.is_empty());
        let retained = lifetimes
            .roots_by_overwrite
            .values()
            .flatten()
            .map(|pair| pair.root_index)
            .collect::<BTreeSet<_>>();
        for root in allocation_roots
            .keys()
            .filter(|root| !retained.contains(root))
        {
            lifetimes.roots.remove(root);
            lifetimes.root_homes.remove(root);
        }
    }
    extend_allocation_owner_overwrites(
        stmts,
        facts,
        safety,
        uses,
        &allocation_roots,
        &mut producer_temp_is_eligible,
        &mut overwrite_temp_is_eligible,
        &mut lifetimes,
    );
    lifetimes
}

/// 复用 allocation owner 时，新写入值也必须在它自己的精确覆盖点释放。
/// 例如 allocation -> global lookup -> table lookup，不能只保留第一条边，否则
/// 第二次 lookup 被内联后，global lookup 的接收者会额外存活到源码 local 的作用域末尾。
/// 只延续已经证明需要物化的 allocation 事务；call/copy 的独立根仍由各自 value owner 管理。
#[allow(clippy::too_many_arguments)]
fn extend_allocation_owner_overwrites(
    stmts: &[HirStmt],
    facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
    uses: &TempUseEvents,
    allocation_roots: &BTreeMap<usize, usize>,
    producer_is_eligible: &mut impl FnMut(TempId) -> bool,
    overwrite_is_eligible: &mut impl FnMut(TempId) -> bool,
    lifetimes: &mut CallRootLifetimeIndices,
) {
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
        let continues_allocation_owner = target.is_some_and(|(_, _, home)| {
            lifetimes.overwrite_pairs(index).any(|pair| {
                pair.home() == home
                    && (allocation_roots.contains_key(&pair.root_index())
                        || owners
                            .get(&home)
                            .is_some_and(|(owner, _)| *owner == pair.root_index()))
            })
        });
        let writes = StackWriteSummary::for_stmt(stmt, facts);
        if writes.has_boundary || writes.has_unknown_home {
            owners.clear();
        } else {
            for home in writes.homes {
                owners.remove(&home);
            }
        }
        if let Some((temp, value, home)) = target
            && continues_allocation_owner
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
    uses: &TempUseEvents,
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
                .insert(temp);
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
                .allocation_release_sites
                .insert((index, temp), root.allocation_site);
            lifetimes
                .pre_dispatch_releases
                .entry(index)
                .or_default()
                .insert(temp);
        }
    }
}

fn root_release_temp(
    aliases: &BTreeSet<TempId>,
    home: HomeSlotKey,
    index: usize,
    uses: &TempUseEvents,
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
    context: RootAnalysisContext<'_>,
    temp_is_eligible: &mut impl FnMut(TempId) -> bool,
) -> bool {
    // 释放端点只可能是当前 block 的显式 dispatch；子块由下面的递归独立处理。
    let releases = if block.stmts.iter().any(|stmt| {
        matches!(stmt, HirStmt::GenericFor(for_stmt) if !for_stmt.dispatch_results.is_empty())
    }) {
        collect_call_root_lifetimes(
            &RootLifetimeFacts::new(&block.stmts),
            facts,
            context,
            true,
            &mut *temp_is_eligible,
            |_| true,
        ).pre_dispatch_releases
    } else {
        BTreeMap::new()
    };
    let mut changed = !releases.is_empty();
    let old_stmts = std::mem::take(&mut block.stmts);
    let mut new_stmts = Vec::with_capacity(old_stmts.len() + releases.len());
    for (index, mut stmt) in old_stmts.into_iter().enumerate() {
        if let Some(temps) = releases.get(&index) {
            for temp in temps {
                new_stmts.push(HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(*temp)],
                    values: HirValuePack::fixed(vec![HirExpr::Nil]),
                    initializer_merge_transaction: None,
                    generic_for_initializer_producer: None,
                    method_rewrite_transaction: None,
                })));
            }
        }
        changed |= materialize_generic_for_dispatch_root_releases_in_stmt(
            &mut stmt,
            facts,
            context,
            temp_is_eligible,
        );
        new_stmts.push(stmt);
    }
    block.stmts = new_stmts;
    changed
}

fn materialize_generic_for_dispatch_root_releases_in_stmt(
    stmt: &mut HirStmt,
    facts: &ProtoPromotionFacts,
    context: RootAnalysisContext<'_>,
    temp_is_eligible: &mut impl FnMut(TempId) -> bool,
) -> bool {
    match stmt {
        HirStmt::LocalRootRelease(_) => false,
        HirStmt::If(if_stmt) => {
            let then_changed = materialize_generic_for_dispatch_root_releases(
                &mut if_stmt.then_block,
                facts,
                context,
                temp_is_eligible,
            );
            let else_changed = if_stmt.else_block.as_mut().is_some_and(|block| {
                materialize_generic_for_dispatch_root_releases(
                    block,
                    facts,
                    context,
                    temp_is_eligible,
                )
            });
            then_changed || else_changed
        }
        HirStmt::While(while_stmt) => materialize_generic_for_dispatch_root_releases(
            &mut while_stmt.body,
            facts,
            context,
            temp_is_eligible,
        ),
        HirStmt::Repeat(repeat_stmt) => materialize_generic_for_dispatch_root_releases(
            &mut repeat_stmt.body,
            facts,
            context,
            temp_is_eligible,
        ),
        HirStmt::NumericFor(for_stmt) => materialize_generic_for_dispatch_root_releases(
            &mut for_stmt.body,
            facts,
            context,
            temp_is_eligible,
        ),
        HirStmt::GenericFor(for_stmt) => materialize_generic_for_dispatch_root_releases(
            &mut for_stmt.body,
            facts,
            context,
            temp_is_eligible,
        ),
        HirStmt::Block(block) => {
            materialize_generic_for_dispatch_root_releases(block, facts, context, temp_is_eligible)
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

/// 识别跨后续用户代码/GC 事件，或 return 表达式内部后续事件的 lookup 物理 root。
///
/// Call 的观察、allocation owner 与相邻 overwrite 合同保持在既有 collector 中；这里不把
/// 普通 lookup 一概提升为 source local。GlobalRef 只在 low CFG 已经证明所有路径都活到 scope
/// end，且 HIR 的最后一次 identity 读取后仍有观察点时，才需要独立物化；TableAccess 的标量
/// 与无求值 multi-nil 仍沿既有同-home 精确配对。没有可见 overwrite 时，跨过显式 GC/普通
/// 用户事件，或在 return 子表达式中先被消费、随后又跨过用户事件的 lookup，由当前 HIR
/// block 的词法 local 保活到 block end。block 外的 successor 不属于该 local 的可见区间，
/// 因此无需猜测跨块 home 复用。
pub(super) fn collect_lookup_gc_root_lifetimes(
    snapshot: &RootLifetimeFacts<'_>,
    facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
    mut temp_is_eligible: impl FnMut(TempId) -> bool,
) -> LookupGcRootLifetimeIndices {
    let stmts = snapshot.stmts;
    let uses = &snapshot.uses;
    if uses.gc_fence_indices.is_empty()
        && !stmts.iter().any(|stmt| matches!(stmt, HirStmt::Return(_)))
    {
        return LookupGcRootLifetimeIndices::default();
    }
    let definitions = stmts
        .iter()
        .filter_map(HirStmt::scalar_temp_assignment)
        .collect::<BTreeMap<_, _>>();
    let reference_captured_temps = super::mention::stmts_reference_captured_bindings(stmts).temps;
    let mut active = BTreeMap::<HomeSlotKey, ActiveLookupGcHome>::new();
    let mut values = LookupValues::new(uses, stmts, safety);
    let mut lifetimes = LookupGcRootLifetimeIndices::default();

    for (index, stmt) in stmts.iter().enumerate() {
        values.advance(index);
        // 参数 home 在 dispatch 时交给 callee；不能再把它物化为跨调用存活的 caller local。
        // 同值的其它 home 仍独立保活，只有当前快照中的唯一 producer/端点证明可以结束事务。
        for temp in &uses.argument_transfers_by_stmt[index] {
            let Some(home) = facts.trusted_temp_home_slot(*temp) else {
                continue;
            };
            let Some(root) = active.get(&home) else {
                continue;
            };
            let [producer] = uses.by_temp[temp].writes.as_slice() else {
                continue;
            };
            if root.aliases.contains(temp)
                && *producer >= root.root_index
                && uses.has_argument_transfer(*temp, *producer, index)
            {
                let root = active
                    .remove(&home)
                    .expect("matched argument home must remain active");
                for alias in root.aliases {
                    values.remove(&alias, index);
                }
            }
        }

        let Some((temp, value)) = stmt.scalar_temp_assignment() else {
            if let HirStmt::Return(return_stmt) = stmt {
                observe_lookup_return_post_use_roots(
                    &return_stmt.values,
                    &definitions,
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
            let mut proven_homes = BTreeSet::new();
            let mut writes = StackWriteSummary::for_stmt(stmt, facts);
            let grouped_assignment_is_complete =
                grouped_assignment_targets_are_active(stmt, facts, |home| {
                    active.contains_key(home)
                });
            let written_active_homes = writes
                .homes
                .iter()
                .copied()
                .filter(|home| active.contains_key(home))
                .collect::<Vec<_>>();
            for home in written_active_homes {
                if !grouped_assignment_is_complete {
                    break;
                }
                let Some(overwrite) =
                    definite_grouped_home_overwrite(stmt, home, facts, &mut temp_is_eligible)
                else {
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
            writes.homes.retain(|home| !proven_homes.contains(home));
            if writes.has_boundary || writes.has_unknown_home {
                active.clear();
                values.clear();
            } else {
                for home in writes.homes {
                    if let Some(root) = active.remove(&home) {
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
            HirExpr::TableAccess(_) => Some(values.new_value(index, None)),
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
                ActiveLookupGcHome {
                    value_id,
                    root_index: index,
                    aliases: BTreeSet::from([temp]),
                    eligible,
                    crossed_observation: false,
                    direct_lookup_home: matches!(
                        value,
                        HirExpr::TableAccess(_) | HirExpr::GlobalRef(_)
                    ),
                    scope_end_copy_root: facts.is_scope_end_copy_root_temp(temp),
                    pure_scope_end_copy_root: facts.is_pure_scope_end_copy_root_temp(temp),
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
    active: &BTreeMap<HomeSlotKey, ActiveLookupGcHome>,
    values: &LookupValues<'_>,
    reference_captured_temps: &BTreeSet<TempId>,
    uses: &TempUseEvents,
    facts: &ProtoPromotionFacts,
) -> Option<(LookupValueId, TempId)> {
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
    if root.value_id != value_id || !root.direct_lookup_home || !root.pure_scope_end_copy_root {
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
    root: ActiveLookupGcHome,
    index: usize,
    home: HomeSlotKey,
    overwrite_is_eligible: bool,
    uses: &TempUseEvents,
    values: &LookupValues<'_>,
    lifetimes: &mut LookupGcRootLifetimeIndices,
) {
    if values.global_home(root.value_id).is_none()
        // 已跨语句观察的 lookup 即使仍有活读，物化后也必须在后续 GC 前精确释放。
        // overwrite 自身的求值不属于此前区间；相邻 lookup/copy 可由同一表达式临时槽接管。
        && (root.crossed_observation
            || values.observed(&root, index + 1)
            || (uses.has_gc_fence_after(index)
                && values.crossed_observer_before(root.root_index, index)))
        && root.eligible
        && overwrite_is_eligible
        && !root
            .aliases
            .iter()
            .any(|alias| uses.has_live_read_after(*alias, index))
    {
        lifetimes.roots.insert(root.root_index);
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

fn preserve_lookup_roots_to_scope_end(
    active: &BTreeMap<HomeSlotKey, ActiveLookupGcHome>,
    values: &LookupValues<'_>,
    end: usize,
    lifetimes: &mut LookupGcRootLifetimeIndices,
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
                    && (root.crossed_observation || values.observed(root, end))
                    && (values.global_home(root.value_id).is_none()
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
    value_by_temp: &BTreeMap<TempId, LookupValueId>,
    active: &mut BTreeMap<HomeSlotKey, ActiveLookupGcHome>,
    safety: HirExprSafety,
) {
    if active.is_empty() {
        return;
    }
    let Some(needs_independent_root) =
        return_lookup::observed_return_lookup_roots(values, definitions, value_by_temp, safety)
    else {
        return;
    };

    for root in active.values_mut() {
        if root.direct_lookup_home
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
    home: HomeSlotKey,
    facts: &ProtoPromotionFacts,
    temp_is_eligible: &mut impl FnMut(TempId) -> bool,
) -> Option<ExactHomeOverwrite> {
    let temps = match stmt {
        HirStmt::Assign(assign) if assign.targets.len() > 1 => {
            let writes = StackWriteSummary::for_stmt(stmt, facts);
            if writes.has_boundary
                || writes.has_unknown_home
                || !writes.homes.contains(&home)
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
            let then_temps = definite_block_home_overwrite(&if_stmt.then_block, home, facts)?;
            let else_temps = definite_block_home_overwrite(else_block, home, facts)?;
            then_temps.union(&else_temps).copied().collect()
        }
        HirStmt::Block(block) => definite_block_home_overwrite(block, home, facts)?,
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
    home: HomeSlotKey,
    facts: &ProtoPromotionFacts,
) -> Option<BTreeSet<TempId>> {
    let (first_index, first_temp) = block.stmts.iter().enumerate().find_map(|(index, stmt)| {
        let (temp, _) = stmt.scalar_temp_assignment()?;
        (facts.trusted_temp_home_slot(temp) == Some(home)).then_some((index, temp))
    })?;
    if !stmts_preserve_home(&block.stmts[..first_index], home, facts)
        || !stmts_rewrite_home_only_through_scalar_temps(
            &block.stmts[(first_index + 1)..],
            home,
            facts,
        )
    {
        return None;
    }
    Some(BTreeSet::from([first_temp]))
}

fn stmts_preserve_home(stmts: &[HirStmt], home: HomeSlotKey, facts: &ProtoPromotionFacts) -> bool {
    let writes = StackWriteSummary::for_stmts(stmts, facts);
    !writes.has_boundary && !writes.has_unknown_home && !writes.homes.contains(&home)
}

fn stmts_rewrite_home_only_through_scalar_temps(
    stmts: &[HirStmt],
    home: HomeSlotKey,
    facts: &ProtoPromotionFacts,
) -> bool {
    stmts.iter().all(|stmt| {
        let writes = StackWriteSummary::for_stmt(stmt, facts);
        if writes.has_boundary || writes.has_unknown_home {
            return false;
        }
        !writes.homes.contains(&home)
            || stmt
                .scalar_temp_assignment()
                .is_some_and(|(temp, _)| facts.trusted_temp_home_slot(temp) == Some(home))
    })
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

fn stmt_is_direct_if_control_read(stmt: &HirStmt, aliases: &BTreeSet<TempId>) -> bool {
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
    reads_alias && stmt_consumes_temps_only_in_control_head(stmt, aliases)
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
) -> Vec<ScopeEndCopyRootHandoff> {
    let Some((HirStmt::Return(_), prefix)) = stmts.split_last() else {
        return Vec::new();
    };
    let mut first_definitions = BTreeMap::new();
    let mut suffix_writes = None;
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
        // 只在存在候选时汇总一次：无 copy 的嵌套 block 不应因此反复遍历整棵子树。
        // 所有查询都到同一 prefix 末尾；nested 写入仍归属原顶层 stmt。
        let (last_home_writes, last_boundary) = suffix_writes.get_or_insert_with(|| {
            let mut last_home_writes = BTreeMap::new();
            let mut last_boundary = None;
            for (index, stmt) in prefix.iter().enumerate() {
                let writes = StackWriteSummary::for_stmt(stmt, facts);
                if writes.has_boundary || writes.has_unknown_home {
                    last_boundary = Some(index);
                }
                for home in writes.homes {
                    last_home_writes.insert(home, index);
                }
            }
            (last_home_writes, last_boundary)
        });
        // 当前 HIR 必须继续满足原始 home 的无覆盖合同；opaque control/cleanup
        // 边界不能用原始负向 root 标记推导出正向覆盖证明。
        if last_boundary.is_some_and(|last| last > source_index)
            || last_home_writes
                .get(&source_home)
                .is_some_and(|last| *last > source_index)
            || last_home_writes
                .get(&target_home)
                .is_some_and(|last| *last > copy_index)
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

impl HirVisitor for ScopeEndRootCollector<'_> {
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
        let temp = match &if_stmt.cond {
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

fn record_call_root_overwrite(
    root: ActiveCallRoot,
    index: usize,
    home: HomeSlotKey,
    eligible: bool,
    uses: &TempUseEvents,
    active: &CallValues<'_>,
    lifetimes: &mut CallRootLifetimeIndices,
) {
    // 普通表达式 forwarding 可由仍活读的同值副本接管；显式 GC 物化则必须同时保留
    // 原 home 的结束位置，不能因另一个 home 继续读该值而留下永不释放的源码 local。
    if !eligible || !root.eligible || active.has_live_read_after(root.value_id, home) {
        return;
    }
    if root.observed
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
    let mut collector = GcRootObservationCollector {
        found: false,
        safety,
    };
    visit_stmts(std::slice::from_ref(stmt), &mut collector);
    collector.found
}

fn expr_may_observe_gc_roots(expr: &HirExpr, safety: HirExprSafety) -> bool {
    let mut collector = GcRootObservationCollector {
        found: false,
        safety,
    };
    visit_expr(expr, &mut collector);
    collector.found
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

impl HirVisitor for LocalUseCollector {
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

struct GcRootObservationCollector {
    found: bool,
    safety: HirExprSafety,
}

impl HirVisitor for GcRootObservationCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        self.found |= matches!(
            stmt,
            HirStmt::GlobalDecl(_) | HirStmt::Close(_) | HirStmt::GenericFor(_)
        );
    }

    fn visit_expr(&mut self, expr: &HirExpr) {
        // The shared discard-safety boundary already classifies dynamic environment/table
        // access, metamethod-capable operators, calls, and allocating expressions as eventful;
        // residual diagnostics stay conservative instead of being treated as executable no-ops.
        self.found |= !self.safety.node_is_discard_safe_without_residual(expr);
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.found |= matches!(lvalue, HirLValue::Global(_) | HirLValue::TableAccess(_));
    }

    fn visit_call(&mut self, _call: &HirCallExpr) {
        // CallStmt exposes a HirCallExpr directly instead of wrapping it in HirExpr::Call.
        self.found = true;
    }
}

pub(super) struct RootLifetimeFacts<'a> {
    stmts: &'a [HirStmt],
    uses: TempUseEvents,
}

impl<'a> RootLifetimeFacts<'a> {
    pub(super) fn new(stmts: &'a [HirStmt]) -> Self {
        Self {
            stmts,
            uses: TempUseEvents::new(stmts),
        }
    }
}

struct TempUseEvents {
    argument_transfers_by_stmt: Vec<Vec<TempId>>,
    // 只按 identity 查询，不枚举 hash 顺序；事件顺序由语句扫描固定。
    by_temp: HashMap<TempId, TempEvents>,
    reads_by_stmt: Vec<BTreeSet<TempId>>,
    gc_fence_indices: BTreeSet<usize>,
}

#[derive(Default)]
struct TempEvents {
    reads: Vec<usize>,
    writes: Vec<usize>,
    argument_transfers: Vec<usize>,
}

impl TempUseEvents {
    fn new(stmts: &[HirStmt]) -> Self {
        let reads_by_stmt = collect_temp_reads_by_stmt(stmts);
        let mut by_temp = HashMap::<TempId, TempEvents>::new();
        for (index, temps) in reads_by_stmt.iter().enumerate() {
            for temp in temps {
                by_temp.entry(*temp).or_default().reads.push(index);
            }
        }

        let mut argument_transfers_by_stmt = Vec::with_capacity(stmts.len());
        for (index, stmt) in stmts.iter().enumerate() {
            let mut collector = TempWriteCollector::default();
            visit_stmts(std::slice::from_ref(stmt), &mut collector);
            for temp in collector.temps {
                by_temp.entry(temp).or_default().writes.push(index);
            }
            for temp in &collector.argument_transfers {
                by_temp
                    .entry(*temp)
                    .or_default()
                    .argument_transfers
                    .push(index);
            }
            argument_transfers_by_stmt.push(collector.argument_transfers);
        }
        Self {
            argument_transfers_by_stmt,
            by_temp,
            reads_by_stmt,
            gc_fence_indices: collect_gc_fence_indices(stmts),
        }
    }

    /// 精确配对本快照内唯一的 producer 与 call 参数端点。多写或重复 call token 必须拒绝。
    fn has_argument_transfer(&self, temp: TempId, producer: usize, overwrite: usize) -> bool {
        let Some(events) = self.by_temp.get(&temp) else {
            return false;
        };
        let [site] = events.argument_transfers.as_slice() else {
            return false;
        };
        events.writes.as_slice() == [producer] && producer < *site && *site <= overwrite
    }

    fn has_live_read_after(&self, temp: TempId, index: usize) -> bool {
        self.has_live_read_from(temp, index + 1)
    }

    fn live_read_changes(&self) -> Vec<(usize, TempId, bool)> {
        let mut changes = Vec::new();
        for (temp, events) in &self.by_temp {
            for index in events.reads.iter().chain(&events.writes).copied() {
                let live = self.has_live_read_after(*temp, index);
                if live != self.has_live_read_from(*temp, index) {
                    changes.push((index + 1, *temp, live));
                }
            }
        }
        changes.sort_unstable();
        changes.dedup();
        changes
    }

    fn has_live_read_from(&self, temp: TempId, index: usize) -> bool {
        let Some(events) = self.by_temp.get(&temp) else {
            return false;
        };
        let next_read = next_event_at_or_after(Some(&events.reads), index);
        let next_write = next_event_at_or_after(Some(&events.writes), index);
        next_read.is_some_and(|read| next_write.is_none_or(|write| read <= write))
    }

    fn reads_at(&self, index: usize) -> Option<&BTreeSet<TempId>> {
        self.reads_by_stmt.get(index)
    }

    fn has_gc_fence_after(&self, index: usize) -> bool {
        self.gc_fence_indices.range((index + 1)..).next().is_some()
    }

    fn is_gc_fence(&self, index: usize) -> bool {
        self.gc_fence_indices.contains(&index)
    }
}

pub(super) fn collect_gc_fence_indices(stmts: &[HirStmt]) -> BTreeSet<usize> {
    let mut temp_aliases = BTreeSet::new();
    let mut local_aliases = BTreeSet::new();
    let mut fences = BTreeSet::new();

    for (index, stmt) in stmts.iter().enumerate() {
        let mut visitor = GcFenceCollector {
            temp_aliases: &temp_aliases,
            local_aliases: &local_aliases,
            found: false,
        };
        visit_stmts(std::slice::from_ref(stmt), &mut visitor);
        if visitor.found {
            fences.insert(index);
        }

        match stmt {
            HirStmt::Assign(assign) => {
                if let [target] = assign.targets.as_slice() {
                    match target {
                        HirLValue::Temp(temp) => {
                            temp_aliases.remove(temp);
                            if value_is_collectgarbage(&assign.values) {
                                temp_aliases.insert(*temp);
                            }
                        }
                        HirLValue::Local(local) => {
                            local_aliases.remove(local);
                            if value_is_collectgarbage(&assign.values) {
                                local_aliases.insert(*local);
                            }
                        }
                        _ => {}
                    }
                }
            }
            HirStmt::LocalDecl(decl) => {
                if let ([binding], [value], None) = (
                    decl.bindings.as_slice(),
                    decl.values.fixed.as_slice(),
                    &decl.values.tail,
                ) {
                    local_aliases.remove(binding);
                    if matches!(value, HirExpr::GlobalRef(global) if global.key.as_bytes() == b"collectgarbage")
                    {
                        local_aliases.insert(*binding);
                    }
                }
            }
            _ => {}
        }
    }
    fences
}

fn value_is_collectgarbage(values: &crate::hir::common::HirValuePack) -> bool {
    matches!(
        (values.fixed.as_slice(), &values.tail),
        ([HirExpr::GlobalRef(global)], None) if global.key.as_bytes() == b"collectgarbage"
    )
}

struct GcFenceCollector<'a> {
    temp_aliases: &'a BTreeSet<TempId>,
    local_aliases: &'a BTreeSet<LocalId>,
    found: bool,
}

impl HirVisitor for GcFenceCollector<'_> {
    fn visit_call(&mut self, call: &HirCallExpr) {
        self.found |= matches!(
            &call.callee,
            HirExpr::GlobalRef(global) if global.key.as_bytes() == b"collectgarbage"
        ) || matches!(&call.callee, HirExpr::TempRef(temp) if self.temp_aliases.contains(temp))
            || matches!(&call.callee, HirExpr::LocalRef(local) if self.local_aliases.contains(local));
    }
}

fn next_event_at_or_after(events: Option<&Vec<usize>>, index: usize) -> Option<usize> {
    let events = events?;
    events
        .get(events.partition_point(|event| *event < index))
        .copied()
}

#[derive(Default)]
struct TempWriteCollector {
    temps: Vec<TempId>,
    argument_transfers: Vec<TempId>,
}

impl HirVisitor for TempWriteCollector {
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

fn forget_written_known_nil_temps(stmt: &HirStmt, known_nil_temps: &mut BTreeSet<TempId>) {
    let mut collector = TempWriteCollector::default();
    visit_stmts(std::slice::from_ref(stmt), &mut collector);
    for temp in collector.temps {
        known_nil_temps.remove(&temp);
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

fn direct_call_in_stmt(stmt: &HirStmt) -> Option<&HirCallExpr> {
    let values = match stmt {
        HirStmt::CallStmt(call_stmt) => return Some(&call_stmt.call),
        HirStmt::LocalDecl(local_decl) => &local_decl.values,
        HirStmt::Assign(assign) => &assign.values,
        HirStmt::Return(ret) => &ret.values,
        _ => return None,
    };
    let ([HirExpr::Call(call)], None) = (values.fixed.as_slice(), &values.tail) else {
        return None;
    };
    Some(call)
}

struct AllocationRootState<'a> {
    active: &'a mut AllocationHomes,
    lifetimes: &'a mut CallRootLifetimeIndices,
    uses: &'a TempUseEvents,
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
            .is_some_and(|root| root.allocation_site == site)
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
    let allocation_site = source_site.or_else(|| match value {
        HirExpr::TableConstructor(table) => Some(std::ptr::from_ref(table.as_ref()).addr()),
        _ => None,
    });
    if let Some(allocation_site) = allocation_site {
        state.active.bind(
            slot,
            temp,
            allocation_site,
            AllocationHomeOwner {
                producer: temp,
                definition_index: index,
                eligible,
            },
        );
    }
}

fn terminate_allocation_home(
    active: &mut AllocationHomes,
    lifetimes: &mut CallRootLifetimeIndices,
    uses: &TempUseEvents,
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
    uses: &TempUseEvents,
    lifetimes: &mut CallRootLifetimeIndices,
) {
    let owner = root.owner;
    if !uses.has_argument_transfer(owner.producer, owner.definition_index, index)
        && owner.eligible
        && eligible
        && !root
            .aliases
            .iter()
            .any(|alias| uses.has_live_read_after(*alias, index))
    {
        let root_index = owner.definition_index;
        lifetimes
            .allocation_sites
            .insert(root_index, root.allocation_site);
        lifetimes.roots.insert(root_index);
        lifetimes
            .root_homes
            .entry(root_index)
            .or_default()
            .insert(home);
        lifetimes
            .roots_by_overwrite
            .entry(index)
            .or_default()
            .push(PhysicalRootOwner { root_index, home });
    }
}

struct StackWriteSummary {
    homes: BTreeSet<HomeSlotKey>,
    has_unknown_home: bool,
    has_boundary: bool,
}

impl StackWriteSummary {
    fn for_stmt(stmt: &HirStmt, facts: &ProtoPromotionFacts) -> Self {
        Self::for_stmts(std::slice::from_ref(stmt), facts)
    }

    fn for_stmts(stmts: &[HirStmt], facts: &ProtoPromotionFacts) -> Self {
        let mut summary = Self {
            homes: BTreeSet::new(),
            has_unknown_home: false,
            has_boundary: false,
        };
        let mut collector = StackWriteCollector {
            facts,
            summary: &mut summary,
        };
        visit_stmts(stmts, &mut collector);
        summary
    }

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

impl HirVisitor for StackWriteCollector<'_> {
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
            HirStmt::GlobalDecl(_)
            | HirStmt::Close(_)
            | HirStmt::Return(_)
            | HirStmt::Break
            | HirStmt::Continue
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decompile::DecompileDialect;
    use crate::hir::common::{
        HirCallStmt, HirGenericFor, HirGenericForDispatchResult, HirTableConstructor, UpvalueId,
    };

    fn assign(target: HirLValue, value: HirExpr) -> HirStmt {
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![target],
            values: HirValuePack::fixed(vec![value]),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        }))
    }

    fn generic_for(result_def: TempId, binding: LocalId) -> HirStmt {
        HirStmt::GenericFor(Box::new(HirGenericFor {
            bindings: vec![binding],
            iterator: HirValuePack::fixed(vec![HirExpr::GlobalRef(
                crate::hir::common::HirGlobalRef {
                    key: "iterator".into(),
                },
            )]),
            body: HirBlock::default(),
            initializer_transaction: None,
            initializer_roots: Vec::new(),
            dispatch_results: vec![HirGenericForDispatchResult {
                result_def,
                success_binding: binding,
            }],
        }))
    }

    fn call(name: &str) -> HirExpr {
        HirExpr::Call(Box::new(HirCallExpr {
            argument_roots: Vec::new(),
            frame_root_ends: Vec::new(),
            callee: HirExpr::GlobalRef(crate::hir::common::HirGlobalRef { key: name.into() }),
            args: HirValuePack::default(),
            method: false,
            fastcall: None,
            method_key: None,
            callee_root_handoff: None,
            method_rewrite_transaction: None,
        }))
    }

    fn call_stmt(name: &str) -> HirStmt {
        let HirExpr::Call(call) = call(name) else {
            unreachable!("test call helper must return a call expression")
        };
        HirStmt::CallStmt(Box::new(HirCallStmt { call: *call }))
    }

    #[test]
    fn certified_copy_root_call_move_reuses_the_overwritten_home_owner() {
        let producer = TempId(0);
        let endpoint = TempId(1);
        let producer_home = HomeSlotKey::new(0, 0);
        let endpoint_home = HomeSlotKey::new(1, 0);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(producer, producer_home);
        facts.record_temp_home_slot_for_test(endpoint, endpoint_home);
        facts.record_copy_root_call_result_move_for_test(producer, endpoint);
        let stmts = vec![
            assign(HirLValue::Temp(producer), HirExpr::UpvalueRef(UpvalueId(0))),
            call_stmt("observe"),
            assign(HirLValue::Temp(endpoint), call("replacement")),
        ];

        let lifetimes = collect_call_root_lifetimes(
            &RootLifetimeFacts::new(&stmts),
            &facts,
            RootAnalysisContext {
                safety: HirExprSafety::for_dialect(DecompileDialect::Luau),
                effects: &[],
            },
            true,
            |_| true,
            |_| true,
        );

        assert!(lifetimes.is_root(0));
        let pair = lifetimes
            .unambiguous_overwrite_pair(2)
            .expect("certified call MOVE must publish one overwrite pair");
        assert_eq!(pair.root_index(), 0);
        assert_eq!(pair.home(), producer_home);
    }

    #[test]
    fn certified_copy_root_call_move_rejects_hir_write_before_endpoint() {
        let producer = TempId(0);
        let endpoint = TempId(1);
        let intervening = TempId(2);
        let producer_home = HomeSlotKey::new(0, 0);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(producer, producer_home);
        facts.record_temp_home_slot_for_test(endpoint, HomeSlotKey::new(1, 0));
        facts.record_temp_home_slot_for_test(intervening, producer_home);
        facts.record_copy_root_call_result_move_for_test(producer, endpoint);
        let stmts = vec![
            assign(HirLValue::Temp(producer), HirExpr::UpvalueRef(UpvalueId(0))),
            assign(HirLValue::Temp(intervening), HirExpr::Nil),
            assign(HirLValue::Temp(endpoint), call("replacement")),
        ];

        let lifetimes = collect_call_root_lifetimes(
            &RootLifetimeFacts::new(&stmts),
            &facts,
            RootAnalysisContext {
                safety: HirExprSafety::for_dialect(DecompileDialect::Luau),
                effects: &[],
            },
            true,
            |_| true,
            |_| true,
        );

        assert!(!lifetimes.is_root(0));
        assert!(lifetimes.unambiguous_overwrite_pair(2).is_none());
    }

    #[test]
    fn generic_for_result_home_releases_escaped_allocation_before_dispatch() {
        let old = TempId(0);
        let result_def = TempId(1);
        let binding = LocalId(0);
        let home = HomeSlotKey::new(4, 0);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(old, home);
        facts.record_temp_home_slot_for_test(result_def, home);
        let mut block = HirBlock {
            stmts: vec![
                assign(
                    HirLValue::Temp(old),
                    HirExpr::TableConstructor(Box::<HirTableConstructor>::default()),
                ),
                assign(HirLValue::Upvalue(UpvalueId(0)), HirExpr::TempRef(old)),
                generic_for(result_def, binding),
            ],
        };

        assert!(materialize_generic_for_dispatch_root_releases(
            &mut block,
            &facts,
            RootAnalysisContext {
                safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
                effects: &[]
            },
            &mut |_| true,
        ));
        assert!(matches!(
            block.stmts.as_slice(),
            [
                _,
                _,
                HirStmt::Assign(release),
                HirStmt::GenericFor(_)
            ] if matches!(
                (release.targets.as_slice(), release.values.fixed.as_slice(), &release.values.tail),
                ([HirLValue::Temp(temp)], [HirExpr::Nil], None) if *temp == old
            )
        ));
        assert!(!materialize_generic_for_dispatch_root_releases(
            &mut block,
            &facts,
            RootAnalysisContext {
                safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
                effects: &[]
            },
            &mut |_| true,
        ));
    }

    #[test]
    fn generic_for_dispatch_itself_observes_and_releases_an_opaque_call_result() {
        let old = TempId(0);
        let result_def = TempId(1);
        let binding = LocalId(0);
        let home = HomeSlotKey::new(4, 0);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(old, home);
        facts.record_temp_home_slot_for_test(result_def, home);
        let mut block = HirBlock {
            stmts: vec![
                assign(
                    HirLValue::Temp(old),
                    HirExpr::Call(Box::new(HirCallExpr {
                        argument_roots: Vec::new(),
                        frame_root_ends: Vec::new(),
                        callee: HirExpr::GlobalRef(crate::hir::common::HirGlobalRef {
                            key: "make_collectable".into(),
                        }),
                        args: HirValuePack::default(),
                        method: false,
                        fastcall: None,
                        method_key: None,
                        callee_root_handoff: None,
                        method_rewrite_transaction: None,
                    })),
                ),
                generic_for(result_def, binding),
            ],
        };

        assert!(materialize_generic_for_dispatch_root_releases(
            &mut block,
            &facts,
            RootAnalysisContext {
                safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
                effects: &[]
            },
            &mut |_| true,
        ));
        assert!(matches!(
            block.stmts.as_slice(),
            [_, HirStmt::Assign(release), HirStmt::GenericFor(_)] if matches!(
                (release.targets.as_slice(), release.values.fixed.as_slice(), &release.values.tail),
                ([HirLValue::Temp(temp)], [HirExpr::Nil], None) if *temp == old
            )
        ));
    }

    #[test]
    fn generic_for_result_home_does_not_release_a_disjoint_root() {
        let old = TempId(0);
        let result_def = TempId(1);
        let binding = LocalId(0);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(old, HomeSlotKey::new(4, 0));
        facts.record_temp_home_slot_for_test(result_def, HomeSlotKey::new(5, 0));
        let mut block = HirBlock {
            stmts: vec![
                assign(
                    HirLValue::Temp(old),
                    HirExpr::TableConstructor(Box::<HirTableConstructor>::default()),
                ),
                assign(HirLValue::Upvalue(UpvalueId(0)), HirExpr::TempRef(old)),
                generic_for(result_def, binding),
            ],
        };

        assert!(!materialize_generic_for_dispatch_root_releases(
            &mut block,
            &facts,
            RootAnalysisContext {
                safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
                effects: &[]
            },
            &mut |_| true,
        ));
        assert_eq!(block.stmts.len(), 3);
    }

    #[test]
    fn generic_for_result_home_does_not_materialize_an_ineligible_release() {
        let old = TempId(0);
        let result_def = TempId(1);
        let binding = LocalId(0);
        let home = HomeSlotKey::new(4, 0);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(old, home);
        facts.record_temp_home_slot_for_test(result_def, home);
        let mut block = HirBlock {
            stmts: vec![
                assign(
                    HirLValue::Temp(old),
                    HirExpr::TableConstructor(Box::<HirTableConstructor>::default()),
                ),
                assign(HirLValue::Upvalue(UpvalueId(0)), HirExpr::TempRef(old)),
                generic_for(result_def, binding),
            ],
        };

        assert!(!materialize_generic_for_dispatch_root_releases(
            &mut block,
            &facts,
            RootAnalysisContext {
                safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
                effects: &[]
            },
            &mut |_| false,
        ));
        assert_eq!(block.stmts.len(), 3);
    }
}
