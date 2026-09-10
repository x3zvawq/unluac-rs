//! 这个文件负责清理 simplify 出口上已经没有任何读取者的无副作用 temp 赋值。
//!
//! 结构层在 block 入口会先把一批 phi/temp 物化出来，后续 branch/loop/readability pass
//! 再把真正活着的那部分折进源码结构。对大函数来说，最后常会留下"只赋值一次、后面从未
//! 再读"的机械 temp 壳；它们继续留在 HIR 里不仅会制造残余 unresolved warning，
//! 还会直接挡住 AST lowering。
//!
//! 清理范围：目标 temp 全局无读者，且 RHS 不含潜在副作用（调用、metamethod 触发、
//! table 构造等）的赋值语句。它依赖 promotion 保存的物理 home 与 entry-nil provenance：
//! 无物理 home 的纯死写可直接删除；参数同槽写改回参数赋值；不经过循环或可达反向边的
//! 结构化前缀中，`entry nil -> GC-inert value` 的写入也可删除；只被前向 goto 引用的
//! label 不会停用整段证明。复制无 capture-home
//! 别名、无后写且后缀仍读取的可见 binding 同样不需要建立第二个 root。其余有 home 的
//! 写入不在这里猜 reaching value，因为它仍可能决定旧对象或新对象的 GC root 生命周期。
//! debug identity 与 `HirInlineDisposition::Preserve` 统一进入 protected-temp 集；普通死写、
//! copy-root retarget 和相邻 overwrite 事务都必须显式避开它，而不能依赖某个 retention
//! reason 恰好也会命中 capture/home guard。
//! RHS 的可删除性与 GC 惰性统一消费入口按目标方言构造的表达式安全上下文。
//!
//! 例子：根前缀里的机械 `t = false` 若 `t` 是非参数槽首个 fixed def，可删成空；
//! `t = stable_local` 若目标覆盖 entry nil 可删；`t = p; p = false` 则必须把后写精确
//! 接回同一个 PhysicalRoot，不能把 `t` 的 root 无条件延长到函数结束。
//! copy-root 候选只读借用当前 HIR 的 RHS；各块一次计算直线 GC-inert return 后缀，
//! 位置查询复用该边界。提交计划只保存身份，不把借用或后缀位置带过树改写。
//! 候选位置使用当前树的语句先序编号与块结束位置；每个 scalar 写只保存固定大小的坐标，
//! 不保存祖先路径，也不从这个词法索引推导动态支配或可达性。
//! 可见 binding 的稳定性消费入口的一份 home 写入摘要；未知 home 写影响所有查询，
//! LocalRootRelease 只影响被释放的 Local 身份，不扩散到同 home 的其它 binding。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirBlock, HirExpr, HirLValue, HirProto, HirStmt, LocalId, ParamId, TempId,
};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::{CopyRootOverwrite, HomeSlotKey, ProtoPromotionFacts};

use super::lexical_cfg::{
    LexicalBlockKind, LexicalBlockPath, LexicalCfgFailure, OwnerReentryFacts,
};
use super::mention::{stmts_protected_locals, stmts_reference_captured_bindings};
use super::root_lifetimes::stmt_may_observe_gc_roots;
use super::temp_touch::collect_temp_reads_in_proto;
use super::walk::{HirRewritePass, rewrite_proto};
use crate::hir::visit::{self, HirVisitor};

pub(super) fn remove_dead_temp_materializations_in_proto(
    proto: &mut HirProto,
    promotion_facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
) -> bool {
    let live_reads = collect_temp_reads_in_proto(proto);
    let parameters_by_home = proto
        .params
        .iter()
        .filter_map(|param| {
            promotion_facts
                .trusted_param_home_slot(*param)
                .map(|home| (home, *param))
        })
        .collect::<BTreeMap<_, _>>();
    let parameter_by_temp = (0..proto.temp_count)
        .map(TempId)
        .filter_map(|temp| {
            promotion_facts
                .trusted_temp_home_slot(temp)
                .and_then(|home| parameters_by_home.get(&home).copied())
                .map(|param| (temp, param))
        })
        .collect();
    let physical_home_temps = (0..proto.temp_count)
        .map(TempId)
        .filter(|temp| promotion_facts.home_slot(*temp).is_some())
        .collect();
    let mut protected_temps = (0..proto.temp_count)
        .map(TempId)
        .zip(&proto.temp_debug_locals)
        .filter_map(|(temp, hint)| hint.as_ref().map(|_| temp))
        .collect::<BTreeSet<_>>();
    protected_temps.extend(
        (0..proto.temp_count)
            .map(TempId)
            .filter(|temp| proto.inline_dispositions.temp(*temp).must_preserve()),
    );
    let reference_captured = stmts_reference_captured_bindings(&proto.body.stmts);
    let reference_captured_homes = reference_captured.complete_home_slots(promotion_facts);
    let protected_locals = stmts_protected_locals(&proto.body.stmts);
    let home_writes = VisibleHomeWrites::collect(proto, promotion_facts);
    // 参数覆盖在本 pass 入口可能仍是写同 home 的 Local/Temp，不能只扫描已经语法化成
    // HirLValue::Param 的目标；缺可信 home 的直接 binding 写也不能用于稳定性正证明。
    let overwritten_visible_params = proto
        .params
        .iter()
        .filter(|param| {
            promotion_facts.trusted_param_home_slot(**param).is_some()
                && !reference_captured.params.contains(param)
                && home_writes.may_write(VisibleBinding::Param(**param))
        })
        .copied()
        .collect::<BTreeSet<_>>();
    let params = proto
        .params
        .iter()
        .filter(|param| {
            promotion_facts
                .trusted_param_home_slot(**param)
                .is_some_and(|home| !reference_captured_homes.contains(&home))
                && !overwritten_visible_params.contains(param)
        })
        .copied()
        .collect();
    let locals = (0..proto.local_count)
        .map(LocalId)
        .filter(|local| {
            promotion_facts
                .trusted_local_home_slot(*local)
                .is_some_and(|home| !reference_captured_homes.contains(&home))
                // TBC/loop binding 有独立资源或迭代生命周期，不能只按普通 root 证明。
                && !protected_locals.contains(local)
                && !home_writes.may_write(VisibleBinding::Local(*local))
        })
        .collect();
    let stable_visible_bindings = StableVisibleBindings {
        params,
        locals,
        reference_captured_homes,
    };
    let mut pass = DeadTempPass {
        live_reads: &live_reads,
        parameter_by_temp,
        physical_home_temps,
        protected_temps,
        facts: promotion_facts,
        stable_visible_bindings,
        overwritten_visible_params,
        physical_root_temps: BTreeSet::new(),
        safety,
    };
    let mut changed = rewrite_proto(proto, &mut pass);
    // rewrite_proto 可能删除或重写同一 owner 内的语句；后续 CFG 必须消费改写后的
    // goto/label 关系，否则会把已经消失的重入边误判为仍然存在。
    let owner_reentry =
        OwnerReentryFacts::collect(&proto.body, safety).unwrap_or_else(|failure| match failure {
            LexicalCfgFailure::AmbiguousLabel => {
                panic!("HIR label identity must have one lexical owner per proto")
            }
            LexicalCfgFailure::ExternalEntry => {
                unreachable!("owner-wide CFG cannot have a parent entry")
            }
        });
    let dead_entry_context = DeadEntryNilContext {
        owner_reentry: &owner_reentry,
        live_reads: &live_reads,
        protected_temps: &pass.protected_temps,
        physical_root_temps: &proto.physical_root_temps,
        stable_visible_bindings: &pass.stable_visible_bindings,
        facts: promotion_facts,
        safety,
    };
    changed |= remove_dead_entry_nil_writes_from_acyclic_prefixes(
        &mut proto.body,
        &mut LexicalBlockPath::root(),
        &dead_entry_context,
    );
    changed |= preserve_copy_roots_in_proto(
        proto,
        &live_reads,
        &pass.protected_temps,
        &pass.stable_visible_bindings.reference_captured_homes,
        promotion_facts,
        safety,
        &mut pass.physical_root_temps,
    );
    changed |= preserve_adjacent_dead_physical_overwrites(
        &mut proto.body,
        &live_reads,
        &pass.protected_temps,
        &pass.stable_visible_bindings.reference_captured_homes,
        promotion_facts,
        safety,
        &mut pass.physical_root_temps,
    );
    let original_physical_root_count = proto.physical_root_temps.len();
    proto
        .physical_root_temps
        .extend(pass.physical_root_temps.iter().copied());
    changed |= proto.physical_root_temps.len() != original_physical_root_count;
    changed
}

struct DeadEntryNilContext<'a> {
    owner_reentry: &'a OwnerReentryFacts,
    live_reads: &'a BTreeSet<TempId>,
    protected_temps: &'a BTreeSet<TempId>,
    physical_root_temps: &'a BTreeSet<TempId>,
    stable_visible_bindings: &'a StableVisibleBindings,
    facts: &'a ProtoPromotionFacts,
    safety: HirExprSafety,
}

fn remove_dead_entry_nil_writes_from_acyclic_prefixes(
    block: &mut HirBlock,
    path: &mut LexicalBlockPath,
    context: &DeadEntryNilContext<'_>,
) -> bool {
    let reentry_start = context
        .owner_reentry
        .first_reentry_target(path)
        .unwrap_or(block.stmts.len());
    let mut changed = false;
    for (index, stmt) in block.stmts.iter_mut().enumerate() {
        // 若当前语句位于 owner 的可达回边区域，它的嵌套 block 也可能重复执行；即使
        // 嵌套 block 自身没有 label，也不能把它当成单次入口继续递归证明。
        if index >= reentry_start {
            break;
        }
        match stmt {
            HirStmt::LocalRootRelease(_) => {}
            HirStmt::If(if_stmt) => {
                changed |= path.with_child(index, LexicalBlockKind::Then, |path| {
                    remove_dead_entry_nil_writes_from_acyclic_prefixes(
                        &mut if_stmt.then_block,
                        path,
                        context,
                    )
                });
                if let Some(else_block) = &mut if_stmt.else_block {
                    changed |= path.with_child(index, LexicalBlockKind::Else, |path| {
                        remove_dead_entry_nil_writes_from_acyclic_prefixes(
                            else_block, path, context,
                        )
                    });
                }
            }
            HirStmt::Block(nested) => {
                changed |= path.with_child(index, LexicalBlockKind::Body, |path| {
                    remove_dead_entry_nil_writes_from_acyclic_prefixes(nested, path, context)
                });
            }
            HirStmt::LocalDecl(_)
            | HirStmt::GlobalDecl(_)
            | HirStmt::Assign(_)
            | HirStmt::TableSetList(_)
            | HirStmt::While(_)
            | HirStmt::Repeat(_)
            | HirStmt::NumericFor(_)
            | HirStmt::GenericFor(_)
            | HirStmt::Return(_)
            | HirStmt::Break
            | HirStmt::Continue
            | HirStmt::Goto(_)
            | HirStmt::Label(_)
            | HirStmt::ErrNil(_)
            | HirStmt::ToBeClosed(_)
            | HirStmt::Close(_)
            | HirStmt::CallStmt(_) => {}
        }
    }
    changed |= remove_dead_entry_nil_writes_from_root_prefix(block, reentry_start, context);
    changed
}

fn preserve_copy_roots_in_proto(
    proto: &mut HirProto,
    live_reads: &BTreeSet<TempId>,
    protected_temps: &BTreeSet<TempId>,
    reference_captured_homes: &BTreeSet<HomeSlotKey>,
    facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
    physical_root_temps: &mut BTreeSet<TempId>,
) -> bool {
    let mut sites = CopyRootAssignmentSites::default();
    sites.collect_block(&proto.body, live_reads, safety);

    let mut rewrite_targets = BTreeMap::<TempId, TempId>::new();
    let mut roots = BTreeSet::new();
    for (&producer, producer_site) in &sites.temps {
        if protected_temps.contains(&producer) {
            // 候选拒绝[LayerBoundary]：copy-root retarget 会把 endpoint 写改绑到 producer
            // 并交给 PhysicalRoot owner；它不能顺带消解上游 HIR 的 binding Preserve。
            continue;
        }
        let Some(producer_value) = producer_site.unique_dead_value() else {
            continue;
        };
        if safety.result_is_gc_inert(producer_value) {
            continue;
        }
        let scope_end = facts.is_scope_end_copy_root_temp(producer);
        let overwrites = facts.copy_root_overwrites(producer);
        if !scope_end && overwrites.is_none() {
            continue;
        }
        let Some(home) = facts.trusted_temp_home_slot(producer) else {
            continue;
        };
        if reference_captured_homes.contains(&home) {
            // 候选拒绝[SemanticBarrier:Capture]：同槽 capture 会观察 overwrite 是否仍写回
            // 原 cell；regress_431 的 captured root 证明不能把 transaction 改绑到别的 identity。
            continue;
        }

        let mut candidate_rewrites = BTreeMap::new();
        let match_context = CopyRootMatchContext {
            sites: &sites,
            protected_temps,
            facts,
            existing_rewrites: &rewrite_targets,
        };
        let all_overwrites_match = overwrites.into_iter().flatten().all(|overwrite| {
            copy_root_overwrite_matches_hir(
                *overwrite,
                producer,
                producer_site,
                &match_context,
                &mut candidate_rewrites,
            )
        });
        if !all_overwrites_match {
            continue;
        }
        roots.insert(producer);
        rewrite_targets.extend(candidate_rewrites);
    }

    let rewritten = if rewrite_targets.is_empty() {
        0
    } else {
        rewrite_copy_root_overwrites(&mut proto.body, &rewrite_targets)
    };
    // 每个 key 已由同一只读快照的唯一 scalar Temp 写签发，期间没有改变树；提交必须一一命中。
    assert_eq!(rewritten, rewrite_targets.len());
    physical_root_temps.extend(roots);
    rewritten != 0
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct CopyRootHirLocation {
    block: usize,
    position: usize,
}

impl CopyRootHirLocation {
    fn owns(self, other: Self, block_ends: &[usize]) -> bool {
        // site 只来自无子块的 scalar 写；其后到所属块末尾恰好是后续语句及后代，
        // 不包含兄弟 arm 或祖先块的后续语句。这是词法范围，不是执行顺序证明。
        self.position < other.position && other.position < block_ends[self.block]
    }
}

#[derive(Default)]
struct CopyRootAssignmentSite<'hir> {
    writes: usize,
    value: Option<&'hir HirExpr>,
    dead: bool,
    dead_pure: bool,
    location: Option<CopyRootHirLocation>,
    separate_endpoint_is_unobservable: bool,
}

impl CopyRootAssignmentSite<'_> {
    fn unique_value(&self) -> Option<&HirExpr> {
        (self.writes == 1).then_some(self.value).flatten()
    }

    fn unique_dead_value(&self) -> Option<&HirExpr> {
        self.unique_value().filter(|_| self.dead)
    }

    fn is_unique_dead_pure(&self) -> bool {
        self.writes == 1 && self.dead_pure
    }
}

#[derive(Default)]
struct CopyRootAssignmentSites<'hir> {
    temps: BTreeMap<TempId, CopyRootAssignmentSite<'hir>>,
    locals: BTreeMap<LocalId, CopyRootAssignmentSite<'hir>>,
    block_ends: Vec<usize>,
    next_position: usize,
}

impl<'hir> CopyRootAssignmentSites<'hir> {
    fn collect_block(
        &mut self,
        block: &'hir HirBlock,
        live_reads: &BTreeSet<TempId>,
        safety: HirExprSafety,
    ) {
        let block_id = self.block_ends.len();
        self.block_ends.push(0);
        let inert_return_suffix = gc_inert_return_suffix(&block.stmts, safety);
        for (stmt_index, stmt) in block.stmts.iter().enumerate() {
            let position = self.next_position;
            self.next_position += 1;
            if let HirStmt::Assign(assign) = stmt {
                for target in &assign.targets {
                    match target {
                        HirLValue::Temp(temp) => self.temps.entry(*temp).or_default().writes += 1,
                        HirLValue::Local(local) => {
                            self.locals.entry(*local).or_default().writes += 1
                        }
                        HirLValue::Param(_)
                        | HirLValue::Upvalue(_)
                        | HirLValue::TableAccess(_)
                        | HirLValue::Global(_) => {}
                    }
                }
                if let Some((temp, value)) = stmt.scalar_temp_assignment() {
                    let site = self.temps.entry(temp).or_default();
                    site.value = Some(value);
                    if !live_reads.contains(&temp) {
                        site.dead = true;
                        site.dead_pure |=
                            dead_pure_temp_assignment(stmt, live_reads, safety) == Some(temp);
                    }
                    site.location = Some(CopyRootHirLocation {
                        block: block_id,
                        position,
                    });
                    site.separate_endpoint_is_unobservable =
                        inert_return_suffix.contains(&(stmt_index + 1));
                }
            }
            if let HirStmt::LocalDecl(decl) = stmt {
                for local in &decl.bindings {
                    self.locals.entry(*local).or_default().writes += 1;
                }
                if let ([local], [value], None) = (
                    decl.bindings.as_slice(),
                    decl.values.fixed.as_slice(),
                    &decl.values.tail,
                ) {
                    let site = self.locals.entry(*local).or_default();
                    site.value = Some(value);
                    site.location = Some(CopyRootHirLocation {
                        block: block_id,
                        position,
                    });
                    site.separate_endpoint_is_unobservable =
                        inert_return_suffix.contains(&(stmt_index + 1));
                }
            }
            visit::for_each_nested_block(stmt, &mut |child| {
                self.collect_block(child, live_reads, safety);
            });
        }
        self.block_ends[block_id] = self.next_position;
    }
}

/// 范围中的每个位置都能作为非空安全后缀的起点；其它语句形状仍是直线证明的障碍。
fn gc_inert_return_suffix(stmts: &[HirStmt], safety: HirExprSafety) -> std::ops::Range<usize> {
    let Some((last, prefix)) = stmts.split_last() else {
        return 0..0;
    };
    if !matches!(last, HirStmt::Return(_)) || stmt_may_observe_gc_roots(last, safety) {
        return 0..0;
    }
    let start = prefix
        .iter()
        .rposition(|stmt| {
            !matches!(stmt, HirStmt::Assign(_) | HirStmt::LocalDecl(_))
                || stmt_may_observe_gc_roots(stmt, safety)
        })
        .map_or(0, |index| index + 1);
    start..stmts.len()
}

struct CopyRootMatchContext<'a> {
    sites: &'a CopyRootAssignmentSites<'a>,
    protected_temps: &'a BTreeSet<TempId>,
    facts: &'a ProtoPromotionFacts,
    existing_rewrites: &'a BTreeMap<TempId, TempId>,
}

fn copy_root_overwrite_matches_hir(
    overwrite: CopyRootOverwrite,
    producer: TempId,
    producer_site: &CopyRootAssignmentSite<'_>,
    context: &CopyRootMatchContext<'_>,
    candidate_rewrites: &mut BTreeMap<TempId, TempId>,
) -> bool {
    let temp = overwrite.temp();
    let temp_site = context.sites.temps.get(&temp);
    let Some(site) = temp_site.or_else(|| {
        context
            .facts
            .promoted_local_for_temp(temp)
            .and_then(|local| context.sites.locals.get(&local))
    }) else {
        return false;
    };
    let Some(value) = site.unique_value() else {
        return false;
    };
    let Some(producer_location) = &producer_site.location else {
        return false;
    };
    let Some(overwrite_location) = &site.location else {
        return false;
    };
    if context.protected_temps.contains(&temp)
        || !overwrite.matches_hir_expr(value)
        || !producer_location.owns(*overwrite_location, &context.sites.block_ends)
        || context.existing_rewrites.contains_key(&temp)
    {
        return false;
    }
    if temp_site.is_some() && site.is_unique_dead_pure() {
        candidate_rewrites.insert(temp, producer).is_none()
    } else {
        // Keeping the producer local alive past this raw primitive overwrite is observable only
        // if the remaining path can allocate, call user code, inspect a weak table, or otherwise
        // run before the frame returns. A live endpoint on a straight GC-inert return suffix may
        // retain its own source binding; dead endpoints still have to reuse the producer owner.
        site.separate_endpoint_is_unobservable
    }
}

fn rewrite_copy_root_overwrites(
    block: &mut HirBlock,
    rewrites: &BTreeMap<TempId, TempId>,
) -> usize {
    let mut rewritten = 0;
    for stmt in &mut block.stmts {
        if let HirStmt::Assign(assign) = stmt
            && let [HirLValue::Temp(temp)] = assign.targets.as_mut_slice()
            && let Some(producer) = rewrites.get(temp).copied()
        {
            *temp = producer;
            assign.generic_for_initializer_producer = None;
            rewritten += 1;
        }
        super::walk::for_each_nested_block_mut(stmt, &mut |child| {
            rewritten += rewrite_copy_root_overwrites(child, rewrites);
        });
    }
    rewritten
}

fn preserve_adjacent_dead_physical_overwrites(
    block: &mut HirBlock,
    live_reads: &BTreeSet<TempId>,
    protected_temps: &BTreeSet<TempId>,
    reference_captured_homes: &BTreeSet<HomeSlotKey>,
    facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
    physical_root_temps: &mut BTreeSet<TempId>,
) -> bool {
    let mut changed = false;
    for index in 1..block.stmts.len() {
        let Some(current) = dead_pure_temp_assignment(&block.stmts[index], live_reads, safety)
        else {
            continue;
        };
        let Some((previous, previous_value)) = block.stmts[index - 1].scalar_temp_assignment()
        else {
            continue;
        };
        if safety.result_is_gc_inert(previous_value) {
            continue;
        }
        let Some(home) = facts.home_slot(previous) else {
            // 没有 raw target home 的 synthetic temp 不代表 VM
            // 物理写，不是这条“把后继写接回旧 root cell”的候选。
            continue;
        };
        if current == previous {
            continue;
        }
        if facts.home_slot(current) != Some(home) {
            // 异槽相邻写不属于“把后继覆盖接回同一物理 root
            // cell”的候选；它们各自拥有独立的生命周期事务。
            continue;
        }
        if live_reads.contains(&previous) {
            // 候选拒绝[SemanticBarrier:ValueFlow]：previous identity 仍被读取，合并覆盖会改变该读取的 reaching value。
            continue;
        }
        if protected_temps.contains(&current) || protected_temps.contains(&previous) {
            // 候选拒绝[SemanticBarrier:DebugScope]：任一写入带已保留的源码 local identity，合并会抹掉一段声明可见期。
            continue;
        }
        if reference_captured_homes.contains(&home) {
            // 候选拒绝[SemanticBarrier:Capture]：同槽 capture 可观察后继写是否仍落在原 cell。
            continue;
        }
        let HirStmt::Assign(assign) = &mut block.stmts[index] else {
            unreachable!("dead temp candidate must remain an assignment")
        };
        assign.targets[0] = HirLValue::Temp(previous);
        assign.generic_for_initializer_producer = None;
        physical_root_temps.insert(previous);
        changed = true;
    }
    changed
}

fn remove_dead_entry_nil_writes_from_root_prefix(
    block: &mut HirBlock,
    reentry_start: usize,
    context: &DeadEntryNilContext<'_>,
) -> bool {
    let mut changed = false;
    let mut in_single_pass_prefix = true;
    let adjacent_visible_handoffs = block
        .stmts
        .windows(2)
        .filter_map(|pair| adjacent_same_value_visible_handoff(pair, context.facts))
        .collect::<BTreeSet<_>>();
    let last_local_read = root_prefix_last_local_reads(block, reentry_start);
    let mut index = 0;
    block.stmts.retain(|stmt| {
        let current_index = index;
        index += 1;
        if !in_single_pass_prefix {
            return true;
        }
        if current_index >= reentry_start || !root_prefix_scan_can_cross(stmt) {
            in_single_pass_prefix = false;
            return true;
        }

        let removable = dead_pure_temp_assignment(stmt, context.live_reads, context.safety)
            .is_some_and(|temp| {
                let home = context.facts.home_slot(temp);
                let has_adjacent_visible_handoff = adjacent_visible_handoffs.contains(&temp);
                let overwrites_entry_nil_with_nil =
                    context.facts.overwrites_entry_nil(temp) && dead_write_value_is_nil(stmt);
                (context.facts.overwrites_entry_nil(temp) || has_adjacent_visible_handoff)
                // 候选拒绝[SemanticBarrier:DebugScope]：debug temp 是已保留的源码 binding；删除定义会抹掉其声明可见期。
                && !context.protected_temps.contains(&temp)
                // 候选拒绝[SemanticBarrier:Lifetime]：PhysicalRoot temp 可能已由精确
                // overwrite handoff 复用；删除其 GC-inert 写会丢失原 root 终止点。
                && (!context.physical_root_temps.contains(&temp) || has_adjacent_visible_handoff)
                // 候选拒绝[SemanticBarrier:Lifetime]：entry-nil 只证明旧值非资源；新 RHS
                // 若可持有 collectable value，删除目标槽写会丢失它的独立 GC root。
                // regress_431 的 overwritten/only_root/captured 三组分别覆盖来源后写、唯一
                // root 与 capture cell；只有下列不建立新 root 的证明分支可以删除。
                && (dead_write_value_is_gc_inert(stmt, context.safety)
                    // 候选接受[NoOpRootProof]：下一句把同一个 visible value 交给同一
                    // trusted home；两次写之间无求值、GC 或 capture 观察点，首写不建立
                    // 额外 root epoch。regress_36 覆盖该分支 handoff。
                    || has_adjacent_visible_handoff
                    || dead_write_copies_stable_binding(
                        stmt,
                        context.stable_visible_bindings,
                        current_index,
                        &last_local_read,
                    ))
                // 候选拒绝[SemanticBarrier:Capture]：候选前后任一 closure 若捕获同槽，删除写入都会让它观察 nil 而非新值。
                && (has_adjacent_visible_handoff
                    // 候选接受[NoOpRootProof]：入口旧值与新值均为 nil；稍后创建
                    // 的同 home capture 观察不到这次无值、无 root 的写回。
                    || overwrites_entry_nil_with_nil
                    || home.is_some_and(|home| {
                        !context
                            .stable_visible_bindings
                            .reference_captured_homes
                            .contains(&home)
                    }))
            });
        changed |= removable;
        !removable
    });
    changed
}

fn adjacent_same_value_visible_handoff(
    pair: &[HirStmt],
    facts: &ProtoPromotionFacts,
) -> Option<TempId> {
    let [first, HirStmt::Assign(second)] = pair else {
        return None;
    };
    let (temp, first_value) = first.scalar_temp_assignment()?;
    let [second_value] = second.values.fixed.as_slice() else {
        return None;
    };
    if !matches!(first_value, HirExpr::ParamRef(_) | HirExpr::LocalRef(_))
        || second.values.tail.is_some()
        || second_value != first_value
    {
        return None;
    }
    let [target] = second.targets.as_slice() else {
        return None;
    };
    let target_home = match target {
        HirLValue::Param(param) => facts.trusted_param_home_slot(*param),
        HirLValue::Local(local) => facts.trusted_local_home_slot(*local),
        HirLValue::Temp(_)
        | HirLValue::Upvalue(_)
        | HirLValue::Global(_)
        | HirLValue::TableAccess(_) => None,
    };
    (facts.home_slot(temp).is_some() && facts.home_slot(temp) == target_home).then_some(temp)
}

fn root_prefix_scan_can_cross(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::LocalRootRelease(_) => true,
        HirStmt::LocalDecl(_)
        | HirStmt::GlobalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_) => true,
        HirStmt::If(_)
        | HirStmt::While(_)
        | HirStmt::Repeat(_)
        | HirStmt::NumericFor(_)
        | HirStmt::GenericFor(_)
        | HirStmt::Block(_) => true,
        HirStmt::Return(_) | HirStmt::Break | HirStmt::Continue | HirStmt::Goto(_) => {
            // 直接终止语句不会顺序进入当前 block 的后缀；后缀只有经过显式 label 才可能
            // 重新可达。继续扫描不可达区间是安全的；owner-wide CFG 会在任何真实重入
            // 边界前停住删除与嵌套递归。
            true
        }
        // label 自身没有求值或写入；是否形成回边由 owner-wide CFG 的精确
        // `first_reentry_target` 决定。只被前向 goto 引用的 label 仍属于单次执行前缀。
        HirStmt::Label(_) => true,
    }
}

fn root_prefix_read_scan_can_continue(stmt: &HirStmt) -> bool {
    root_prefix_scan_can_cross(stmt)
        && !matches!(
            stmt,
            HirStmt::Return(_) | HirStmt::Break | HirStmt::Continue | HirStmt::Goto(_)
        )
}

fn root_prefix_last_local_reads(
    block: &HirBlock,
    reentry_start: usize,
) -> BTreeMap<LocalId, usize> {
    let mut last_local_read = BTreeMap::new();
    for (index, stmt) in block.stmts.iter().enumerate() {
        if index >= reentry_start {
            break;
        }
        let mut collector = LastLocalReadCollector {
            index,
            reads: &mut last_local_read,
        };
        visit::visit_stmts(std::slice::from_ref(stmt), &mut collector);
        if !root_prefix_read_scan_can_continue(stmt) {
            break;
        }
    }
    last_local_read
}

fn dead_write_value_is_gc_inert(stmt: &HirStmt, safety: HirExprSafety) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    let [value] = assign.values.fixed.as_slice() else {
        return false;
    };
    safety.result_is_gc_inert(value)
}

fn dead_write_value_is_nil(stmt: &HirStmt) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    matches!(assign.values.fixed.as_slice(), [HirExpr::Nil])
}

fn dead_write_copies_stable_binding(
    stmt: &HirStmt,
    stable_visible_bindings: &StableVisibleBindings,
    current_index: usize,
    last_local_read: &BTreeMap<LocalId, usize>,
) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    match assign.values.fixed.as_slice() {
        [HirExpr::ParamRef(param)] => stable_visible_bindings.params.contains(param),
        [HirExpr::LocalRef(local)] => {
            stable_visible_bindings.locals.contains(local)
                && last_local_read
                    .get(local)
                    .is_some_and(|last| *last > current_index)
        }
        _ => false,
    }
}

struct StableVisibleBindings {
    params: BTreeSet<ParamId>,
    locals: BTreeSet<LocalId>,
    reference_captured_homes: BTreeSet<HomeSlotKey>,
}

struct LastLocalReadCollector<'a> {
    index: usize,
    reads: &'a mut BTreeMap<LocalId, usize>,
}

impl HirVisitor for LastLocalReadCollector<'_> {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let HirExpr::LocalRef(local) = expr {
            self.reads.insert(*local, self.index);
        }
    }
}

struct DeadTempPass<'a> {
    live_reads: &'a BTreeSet<TempId>,
    parameter_by_temp: BTreeMap<TempId, ParamId>,
    physical_home_temps: BTreeSet<TempId>,
    protected_temps: BTreeSet<TempId>,
    facts: &'a ProtoPromotionFacts,
    stable_visible_bindings: StableVisibleBindings,
    overwritten_visible_params: BTreeSet<ParamId>,
    physical_root_temps: BTreeSet<TempId>,
    safety: HirExprSafety,
}

impl HirRewritePass for DeadTempPass<'_> {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        let mut changed = false;
        block.stmts.retain_mut(|stmt| {
            let Some(temp) = dead_pure_temp_assignment(stmt, self.live_reads, self.safety) else {
                return true;
            };
            // 候选拒绝[SemanticBarrier:DebugScope]：debug temp 是已保留的源码 binding；
            // 候选拒绝[LayerBoundary]：HIR Preserve temp 的 definition 也不能由通用 dead-write owner 删除。
            if self.protected_temps.contains(&temp) {
                return true;
            }
            let HirStmt::Assign(assign) = stmt else {
                unreachable!("dead temp candidate must remain an assignment")
            };
            let value = &assign.values.fixed[0];
            if self.facts.copies_same_visible_home_value(temp, value) {
                // 候选接受[NoOpRootProof]：目标 raw home 与可见 Param/Local 的 trusted home 相同，删除只是去掉同一 cell 的自写回，不改变 root 集或别名含义。
                changed = true;
                return false;
            }
            if let Some(param) = self.parameter_by_temp.get(&temp).copied() {
                // 双方可信 home 证明该 SSA temp 实际覆盖参数槽；改回参数赋值才能维持 regress_342 中可观察的 GC root 释放时点。
                assign.targets[0] = HirLValue::Param(param);
                assign.generic_for_initializer_producer = None;
                changed = true;
                return true;
            }
            if self.physical_home_temps.contains(&temp) {
                if expr_may_alias_overwritten_param(value, &self.overwritten_visible_params) {
                    // 候选拒绝[SemanticBarrier:Lifetime]：RHS 参数会在当前 slot 生命周期
                    // 结束前被同 home 写覆盖。把该 temp 标成 PhysicalRoot，防止 AST
                    // cleanup 再删除这个保活 alias；完整 root transaction 的精确区间由
                    // 后置 copy-root owner 统一处理。
                    self.physical_root_temps.insert(temp);
                }
                // 候选拒绝[SemanticBarrier:Lifetime]：其余 raw-home 写不能在 HIR 删除；
                // regress_398 证明 inert/稳定副本写会在原点释放旧 root，regress_377
                // 证明不同 home 的副本会在源参数覆盖后成为唯一新 root。只有上述两类
                // 完整 transaction 才向 AST 传 PhysicalRoot，避免阻塞普通 dead primitive
                // 声明的 readability cleanup（regress_381）。
                return true;
            }
            changed = true;
            false
        });
        changed
    }
}

fn expr_may_alias_overwritten_param(expr: &HirExpr, params: &BTreeSet<ParamId>) -> bool {
    match expr {
        HirExpr::ParamRef(param) => params.contains(param),
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_may_alias_overwritten_param(&logical.lhs, params)
                || expr_may_alias_overwritten_param(&logical.rhs, params)
        }
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Vector(_)
        | HirExpr::Complex { .. }
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Unary(_)
        | HirExpr::Binary(_)
        | HirExpr::Decision(_)
        | HirExpr::Call(_)
        | HirExpr::VarArg
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => false,
    }
}

fn dead_pure_temp_assignment(
    stmt: &HirStmt,
    live_reads: &BTreeSet<TempId>,
    safety: HirExprSafety,
) -> Option<TempId> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let ([HirLValue::Temp(temp)], [value]) =
        (assign.targets.as_slice(), assign.values.fixed.as_slice())
    else {
        return None;
    };
    // 候选拒绝[SemanticBarrier:ValueArity]：tail 即使不供目标取值仍必须求值；删除
    // `t = nil, side()` 会漏掉 `side()` 的调用和它的可观察结果宽度协议。
    if assign.values.tail.is_some() {
        return None;
    }
    // 候选拒绝[SemanticBarrier:ValueFlow]：仍被读取的 temp 定义决定后续值；删除
    // `t = 1; return t` 会把读取变成未定义槽。
    if live_reads.contains(temp) {
        return None;
    }
    // 候选拒绝[SemanticBarrier:EvalCount]：不可丢弃 RHS 必须求值一次；调用、
    // table/global lookup 或分配即使结果未读也可能执行用户代码、抛错或产生对象身份。
    safety.is_discard_safe(value).then_some(*temp)
}

#[derive(Clone, Copy)]
enum VisibleBinding {
    Param(ParamId),
    Local(LocalId),
}

struct VisibleHomeWrites<'a> {
    facts: &'a ProtoPromotionFacts,
    homes: BTreeSet<HomeSlotKey>,
    released_locals: BTreeSet<LocalId>,
    unknown_home_write: bool,
}

impl<'a> VisibleHomeWrites<'a> {
    fn collect(proto: &HirProto, facts: &'a ProtoPromotionFacts) -> Self {
        let mut writes = Self {
            facts,
            homes: BTreeSet::new(),
            released_locals: BTreeSet::new(),
            unknown_home_write: false,
        };
        visit::visit_stmts(&proto.body.stmts, &mut writes);
        writes
    }

    fn may_write(&self, binding: VisibleBinding) -> bool {
        let home = match binding {
            VisibleBinding::Param(param) => self.facts.trusted_param_home_slot(param),
            VisibleBinding::Local(local) => {
                if self.released_locals.contains(&local) {
                    return true;
                }
                self.facts.trusted_local_home_slot(local)
            }
        };
        self.unknown_home_write || home.is_none_or(|home| self.homes.contains(&home))
    }
}

impl HirVisitor for VisibleHomeWrites<'_> {
    fn visit_local_root_release(&mut self, local: LocalId) {
        self.released_locals.insert(local);
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        let home = match lvalue {
            HirLValue::Param(param) => self.facts.trusted_param_home_slot(*param),
            HirLValue::Local(local) => self.facts.trusted_local_home_slot(*local),
            HirLValue::Temp(temp) => self.facts.trusted_temp_home_slot(*temp),
            HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_) => return,
        };
        if let Some(home) = home {
            self.homes.insert(home);
        } else {
            self.unknown_home_write = true;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decompile::DecompileDialect;
    use crate::hir::common::{
        HirAssign, HirCallExpr, HirClose, HirGlobalDecl, HirGoto, HirIf, HirLabel, HirLabelId,
        HirProtoRef, HirReturn, HirTableConstructor, HirValuePack, HirWhile,
    };
    use crate::hir::simplify::mention::ReferenceCapturedBindings;
    use crate::parser::{ProtoLineRange, ProtoSignature};

    fn block(stmts: Vec<HirStmt>) -> HirBlock {
        HirBlock { stmts }
    }

    fn proto(body: HirBlock, temps: Vec<TempId>) -> HirProto {
        let temp_count = temps.iter().map(|temp| temp.index() + 1).max().unwrap_or(0);
        HirProto {
            id: HirProtoRef(0),
            source: None,
            line_range: ProtoLineRange {
                defined_start: 0,
                defined_end: 0,
            },
            signature: ProtoSignature {
                num_params: 0,
                is_vararg: false,
                has_vararg_param_reg: false,
                named_vararg_table: false,
                legacy_arg_slot: false,
            },
            params: Vec::new(),
            param_debug_hints: Vec::new(),
            local_count: 0,
            vararg_param_local: None,
            local_debug_hints: Vec::new(),
            local_debug_scopes: Vec::new(),
            debug_scopes: Vec::new(),
            physical_root_temps: BTreeSet::new(),
            physical_root_locals: BTreeSet::new(),
            inline_dispositions: Default::default(),
            upvalues: Vec::new(),
            environment_upvalues: BTreeSet::new(),
            mutable_upvalues: BTreeSet::new(),
            upvalue_debug_hints: Vec::new(),
            temp_debug_locals: vec![None; temp_count],
            temp_debug_scopes: vec![None; temp_count],
            temp_count,
            exit_requirements: Vec::new(),
            body,
            children: Vec::new(),
            failure: None,
            detached_children: Vec::new(),
        }
    }

    fn assign(temp: TempId, value: HirExpr) -> HirStmt {
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(temp)],
            values: HirValuePack::fixed(vec![value]),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        }))
    }

    #[test]
    fn reference_capture_homes_cover_all_physical_binding_kinds() {
        let home = HomeSlotKey::new(0, 0);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_local_home_slot(LocalId(0), home);
        facts.record_local_home_slot(LocalId(1), home);
        facts.record_temp_home_slot_for_test(TempId(0), home);
        let mut captured = ReferenceCapturedBindings::default();
        captured.params.insert(ParamId(0));
        captured.locals.insert(LocalId(0));
        captured.temps.insert(TempId(0));

        let captured_homes = captured.complete_home_slots(&facts);
        assert_eq!(captured_homes, BTreeSet::from([home]));
        assert!(
            captured_homes.contains(
                &facts
                    .trusted_local_home_slot(LocalId(1))
                    .expect("candidate has a trusted home")
            ),
            "a different LocalId sharing the captured home must be rejected"
        );
    }

    #[test]
    fn unknown_capture_home_uses_the_complete_physical_home_universe() {
        let home = HomeSlotKey::new(1, 0);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(TempId(1), home);
        let mut captured = ReferenceCapturedBindings::default();
        captured.temps.insert(TempId(0));

        assert_eq!(captured.complete_home_slots(&facts), BTreeSet::from([home]));
    }

    #[test]
    fn home_free_captured_local_cannot_alias_a_physical_home() {
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_local(LocalId(0));
        let mut captured = ReferenceCapturedBindings::default();
        captured.locals.insert(LocalId(0));

        assert_eq!(captured.complete_home_slots(&facts), BTreeSet::new());
    }

    #[test]
    fn adjacent_root_overwrite_uses_raw_target_home_after_value_provenance_invalidation() {
        let previous = TempId(0);
        let current = TempId(1);
        let home = HomeSlotKey::new(0, 0);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(previous, home);
        facts.record_temp_home_slot_for_test(current, home);
        facts.invalidate_temp_home(previous);
        let assign = |temp, value| {
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(temp)],
                values: HirValuePack::fixed(vec![value]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            }))
        };
        let mut block = block(vec![
            assign(previous, HirExpr::ParamRef(ParamId(0))),
            assign(current, HirExpr::Nil),
        ]);
        let mut physical_roots = BTreeSet::new();

        assert!(preserve_adjacent_dead_physical_overwrites(
            &mut block,
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
            &mut physical_roots,
        ));
        let HirStmt::Assign(overwrite) = &block.stmts[1] else {
            panic!("overwrite must remain an assignment");
        };
        assert_eq!(overwrite.targets, vec![HirLValue::Temp(previous)]);
        assert_eq!(physical_roots, BTreeSet::from([previous]));
    }

    #[test]
    fn adjacent_root_overwrite_ignores_a_nonphysical_previous_definition() {
        let previous = TempId(0);
        let current = TempId(1);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(current, HomeSlotKey::new(0, 0));
        let mut block = block(vec![
            assign(previous, HirExpr::ParamRef(ParamId(0))),
            assign(current, HirExpr::Nil),
        ]);
        let original = block.clone();
        let mut physical_roots = BTreeSet::new();

        assert!(!preserve_adjacent_dead_physical_overwrites(
            &mut block,
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
            &mut physical_roots,
        ));
        assert_eq!(block, original);
        assert!(physical_roots.is_empty());
    }

    #[test]
    fn copy_root_rewrites_effectful_producer_and_exact_scalar_structured_overwrites() {
        let producer = TempId(0);
        let truthy_overwrite = TempId(1);
        let falsy_overwrite = TempId(2);
        let home = HomeSlotKey::new(1, 0);
        let mut facts = ProtoPromotionFacts::default();
        for temp in [producer, truthy_overwrite, falsy_overwrite] {
            facts.record_temp_home_slot_for_test(temp, home);
        }
        facts.record_copy_root_overwrites_for_test(
            producer,
            vec![
                (truthy_overwrite, HirExpr::Boolean(false)),
                (falsy_overwrite, HirExpr::Integer(0)),
            ],
        );
        let mut proto = proto(
            block(vec![
                assign(
                    producer,
                    HirExpr::Call(Box::new(HirCallExpr {
                        argument_roots: Vec::new(),
                        frame_root_ends: Vec::new(),
                        callee: HirExpr::ParamRef(ParamId(0)),
                        args: HirValuePack::default(),
                        method: false,
                        fastcall: None,
                        method_key: None,
                        callee_root_handoff: None,
                        method_rewrite_transaction: None,
                    })),
                ),
                HirStmt::If(Box::new(HirIf {
                    cond: HirExpr::Boolean(true),
                    then_block: block(vec![assign(truthy_overwrite, HirExpr::Boolean(false))]),
                    else_block: Some(block(vec![assign(falsy_overwrite, HirExpr::Integer(0))])),
                })),
            ]),
            vec![producer, truthy_overwrite, falsy_overwrite],
        );
        let mut protected = proto.clone();
        let protected_before = protected.body.clone();
        let mut protected_roots = BTreeSet::new();
        assert!(!preserve_copy_roots_in_proto(
            &mut protected,
            &BTreeSet::new(),
            &BTreeSet::from([producer]),
            &BTreeSet::new(),
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
            &mut protected_roots,
        ));
        assert_eq!(protected.body, protected_before);
        assert!(protected_roots.is_empty());

        let mut physical_roots = BTreeSet::new();

        assert!(preserve_copy_roots_in_proto(
            &mut proto,
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
            &mut physical_roots,
        ));
        let HirStmt::If(if_stmt) = &proto.body.stmts[1] else {
            panic!("structured overwrite owner must remain an if");
        };
        for child in [
            &if_stmt.then_block,
            if_stmt
                .else_block
                .as_ref()
                .expect("test has a false-path overwrite"),
        ] {
            let HirStmt::Assign(overwrite) = &child.stmts[0] else {
                panic!("overwrite owner must remain an assignment");
            };
            assert_eq!(overwrite.targets, vec![HirLValue::Temp(producer)]);
        }
        assert_eq!(physical_roots, BTreeSet::from([producer]));
    }

    #[test]
    fn copy_root_rewrites_same_block_direct_boolean_overwrite() {
        let producer = TempId(0);
        let overwrite = TempId(1);
        let home = HomeSlotKey::new(1, 0);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(producer, home);
        facts.record_temp_home_slot_for_test(overwrite, home);
        facts.record_copy_root_overwrites_for_test(
            producer,
            vec![(overwrite, HirExpr::Boolean(false))],
        );
        let mut proto = proto(
            block(vec![
                assign(producer, HirExpr::ParamRef(ParamId(0))),
                assign(overwrite, HirExpr::Boolean(false)),
            ]),
            vec![producer, overwrite],
        );
        let mut physical_roots = BTreeSet::new();

        assert!(preserve_copy_roots_in_proto(
            &mut proto,
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
            &mut physical_roots,
        ));
        let HirStmt::Assign(overwrite) = &proto.body.stmts[1] else {
            panic!("overwrite must remain an assignment");
        };
        assert_eq!(overwrite.targets, vec![HirLValue::Temp(producer)]);
        assert_eq!(physical_roots, BTreeSet::from([producer]));
    }

    #[test]
    fn copy_root_rejects_a_collectable_or_mismatched_hir_overwrite_atomically() {
        let producer = TempId(0);
        let overwrite = TempId(1);
        let home = HomeSlotKey::new(1, 0);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(producer, home);
        facts.record_temp_home_slot_for_test(overwrite, home);
        facts.record_copy_root_overwrites_for_test(
            producer,
            vec![(overwrite, HirExpr::Boolean(false))],
        );
        let mut proto = proto(
            block(vec![
                assign(producer, HirExpr::ParamRef(ParamId(0))),
                assign(
                    overwrite,
                    HirExpr::TableConstructor(Box::<HirTableConstructor>::default()),
                ),
            ]),
            vec![producer, overwrite],
        );
        let original = proto.body.clone();
        let mut physical_roots = BTreeSet::new();

        assert!(!preserve_copy_roots_in_proto(
            &mut proto,
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
            &mut physical_roots,
        ));
        assert_eq!(proto.body, original);
        assert!(physical_roots.is_empty());
    }

    #[test]
    fn copy_root_rejects_a_visible_capture_with_the_same_possible_home() {
        let producer = TempId(0);
        let overwrite = TempId(1);
        let home = HomeSlotKey::new(1, 0);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(producer, home);
        facts.record_temp_home_slot_for_test(overwrite, home);
        facts.record_copy_root_overwrites_for_test(
            producer,
            vec![(overwrite, HirExpr::Boolean(false))],
        );
        let mut proto = proto(
            block(vec![
                assign(producer, HirExpr::ParamRef(ParamId(0))),
                assign(overwrite, HirExpr::Boolean(false)),
            ]),
            vec![producer, overwrite],
        );
        let original = proto.body.clone();
        let mut physical_roots = BTreeSet::new();

        assert!(!preserve_copy_roots_in_proto(
            &mut proto,
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::from([home]),
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
            &mut physical_roots,
        ));
        assert_eq!(proto.body, original);
        assert!(physical_roots.is_empty());
    }

    #[test]
    fn root_prefix_crosses_closed_structures_and_owned_loop_control() {
        let closed_if = HirStmt::If(Box::new(HirIf {
            cond: HirExpr::Boolean(true),
            then_block: block(Vec::new()),
            else_block: Some(block(Vec::new())),
        }));
        let closed_loop = HirStmt::While(Box::new(HirWhile {
            cond: HirExpr::Boolean(true),
            body: block(vec![HirStmt::Continue, HirStmt::Break]),
        }));

        assert!(root_prefix_scan_can_cross(&closed_if));
        assert!(root_prefix_scan_can_cross(&closed_loop));
    }

    #[test]
    fn root_prefix_crosses_global_declaration_without_rewriting_its_identity() {
        let global_decl = HirStmt::GlobalDecl(Box::new(HirGlobalDecl {
            names: vec!["value".into()],
            values: HirValuePack::fixed(vec![HirExpr::Integer(1)]),
        }));

        // Prefix scanning only decides whether a later dead temp write is reached once. The
        // declaration remains in place; success continues linearly and failure never reaches the
        // candidate in either program.
        assert!(root_prefix_scan_can_cross(&global_decl));
    }

    #[test]
    fn root_prefix_distinguishes_forward_labels_from_reentry_boundaries() {
        let target = HirLabelId(0);
        let nested_goto = HirStmt::If(Box::new(HirIf {
            cond: HirExpr::Boolean(true),
            then_block: block(vec![HirStmt::Goto(Box::new(HirGoto { target }))]),
            else_block: None,
        }));
        let return_stmt = HirStmt::Return(Box::new(HirReturn {
            source_instr: None,
            values: HirValuePack::default(),
        }));
        let goto_stmt = HirStmt::Goto(Box::new(HirGoto { target }));
        let label = HirStmt::Label(Box::new(HirLabel {
            entry_cleanup: Vec::new(),
            id: target,
            tbc_barriers: Vec::new(),
        }));

        // The statement-level CFG, rather than a blanket nested-goto shape check, decides whether
        // this forward transfer can re-enter a candidate.
        assert!(root_prefix_scan_can_cross(&nested_goto));
        for terminal in [
            return_stmt,
            HirStmt::Break,
            HirStmt::Continue,
            goto_stmt.clone(),
        ] {
            assert!(root_prefix_scan_can_cross(&terminal));
            assert!(!root_prefix_read_scan_can_continue(&terminal));
        }
        assert!(root_prefix_scan_can_cross(&label));
        assert!(root_prefix_read_scan_can_continue(&label));

        let safety = HirExprSafety::for_dialect(DecompileDialect::Lua54);
        let mut root = LexicalBlockPath::root();
        let forward = block(vec![goto_stmt.clone(), label.clone()]);
        let forward_reentry = OwnerReentryFacts::collect(&forward, safety).unwrap();
        assert_eq!(forward_reentry.first_reentry_target(&root), None);
        let backward = block(vec![label, goto_stmt]);
        let backward_reentry = OwnerReentryFacts::collect(&backward, safety).unwrap();
        assert_eq!(backward_reentry.first_reentry_target(&root), Some(0));

        let nested_target = HirLabelId(1);
        let external_backward = block(vec![
            HirStmt::Block(Box::new(block(vec![HirStmt::Label(Box::new(HirLabel {
                entry_cleanup: Vec::new(),
                id: nested_target,
                tbc_barriers: Vec::new(),
            }))]))),
            HirStmt::Goto(Box::new(HirGoto {
                target: nested_target,
            })),
        ]);
        let external_backward_reentry =
            OwnerReentryFacts::collect(&external_backward, safety).unwrap();
        assert_eq!(
            external_backward_reentry.first_reentry_target(&root),
            Some(0)
        );
        assert_eq!(
            root.with_child(0, LexicalBlockKind::Body, |path| external_backward_reentry
                .first_reentry_target(path)),
            Some(0)
        );
    }

    #[test]
    fn unreachable_suffix_read_does_not_prove_a_visible_root_lifetime() {
        let local = LocalId(0);
        let body = block(vec![
            assign(TempId(0), HirExpr::LocalRef(local)),
            HirStmt::Return(Box::new(HirReturn {
                source_instr: None,
                values: HirValuePack::default(),
            })),
            assign(TempId(1), HirExpr::LocalRef(local)),
        ]);

        assert_eq!(
            root_prefix_last_local_reads(&body, body.stmts.len()).get(&local),
            Some(&0)
        );
    }

    #[test]
    fn return_suffix_consumes_dead_handoff_across_close_and_closed_block() {
        let temp = TempId(0);
        let home = HomeSlotKey::new(0, 0);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(temp, home);
        let mut body = block(vec![
            HirStmt::Return(Box::new(HirReturn {
                source_instr: None,
                values: HirValuePack::default(),
            })),
            HirStmt::Close(Box::new(HirClose {
                kind: crate::transformer::CloseKind::Explicit,
                from_reg: 0,
                origins: Vec::new(),
            })),
            HirStmt::Block(Box::default()),
            assign(temp, HirExpr::ParamRef(ParamId(0))),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Param(ParamId(0))],
                values: HirValuePack::fixed(vec![HirExpr::ParamRef(ParamId(0))]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            })),
        ]);
        let stable_visible_bindings = StableVisibleBindings {
            params: BTreeSet::new(),
            locals: BTreeSet::new(),
            reference_captured_homes: BTreeSet::new(),
        };
        let safety = HirExprSafety::for_dialect(DecompileDialect::Lua54);
        let owner_reentry = OwnerReentryFacts::collect(&body, safety).unwrap();
        let reentry_start = owner_reentry
            .first_reentry_target(&LexicalBlockPath::root())
            .unwrap_or(body.stmts.len());
        let empty_temps = BTreeSet::new();
        let context = DeadEntryNilContext {
            owner_reentry: &owner_reentry,
            live_reads: &empty_temps,
            protected_temps: &empty_temps,
            physical_root_temps: &empty_temps,
            stable_visible_bindings: &stable_visible_bindings,
            facts: &facts,
            safety,
        };

        assert!(remove_dead_entry_nil_writes_from_root_prefix(
            &mut body,
            reentry_start,
            &context,
        ));
        assert_eq!(body.stmts.len(), 4);
        assert!(matches!(body.stmts[0], HirStmt::Return(_)));
        assert!(matches!(body.stmts[1], HirStmt::Close(_)));
        assert!(matches!(body.stmts[2], HirStmt::Block(_)));
        assert!(matches!(body.stmts[3], HirStmt::Assign(ref assign)
            if assign.targets == [HirLValue::Param(ParamId(0))]));
    }

    #[test]
    fn external_forward_entry_keeps_the_single_pass_cleanup_proof() {
        let temp = TempId(0);
        let target = HirLabelId(0);
        let home = HomeSlotKey::new(0, 0);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(temp, home);
        let mut body = block(vec![
            HirStmt::If(Box::new(HirIf {
                cond: HirExpr::ParamRef(ParamId(1)),
                then_block: block(vec![HirStmt::Goto(Box::new(HirGoto { target }))]),
                else_block: None,
            })),
            HirStmt::Block(Box::new(block(vec![
                HirStmt::Label(Box::new(HirLabel {
                    entry_cleanup: Vec::new(),
                    id: target,
                    tbc_barriers: Vec::new(),
                })),
                HirStmt::Close(Box::new(HirClose {
                    kind: crate::transformer::CloseKind::Explicit,
                    from_reg: 0,
                    origins: Vec::new(),
                })),
                assign(temp, HirExpr::ParamRef(ParamId(0))),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Param(ParamId(0))],
                    values: HirValuePack::fixed(vec![HirExpr::ParamRef(ParamId(0))]),
                    initializer_merge_transaction: None,
                    generic_for_initializer_producer: None,
                    method_rewrite_transaction: None,
                })),
            ]))),
        ]);
        let original = body.clone();
        let stable_visible_bindings = StableVisibleBindings {
            params: BTreeSet::new(),
            locals: BTreeSet::new(),
            reference_captured_homes: BTreeSet::new(),
        };
        let safety = HirExprSafety::for_dialect(DecompileDialect::Lua54);
        let owner_reentry = OwnerReentryFacts::collect(&body, safety).unwrap();
        let empty_temps = BTreeSet::new();
        let context = DeadEntryNilContext {
            owner_reentry: &owner_reentry,
            live_reads: &empty_temps,
            protected_temps: &empty_temps,
            physical_root_temps: &empty_temps,
            stable_visible_bindings: &stable_visible_bindings,
            facts: &facts,
            safety,
        };

        assert!(remove_dead_entry_nil_writes_from_acyclic_prefixes(
            &mut body,
            &mut LexicalBlockPath::root(),
            &context,
        ));
        assert_ne!(body, original);
        let HirStmt::Block(nested) = &body.stmts[1] else {
            panic!("expected nested forward-entry block");
        };
        assert_eq!(nested.stmts.len(), 3);
    }
}
