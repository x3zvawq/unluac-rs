//! 这个子模块负责从连续 stmt 区域里扫描表构造器候选步骤。
//!
//! 它依赖 HIR 已经稳定的赋值/构造器形状，只回答“哪些 stmt 可视为构造器 seed、record、
//! setlist 或 producer”，不会在这里直接改写语句。
//! 例如：`local t = {}; t.x = 1; t.y = 2` 会在这里被扫描成一串 constructor steps。
//! 全 nil 且没有 debug identity 的 local 声明不产生求值事件；scanner 会把它记入保留计划，
//! 只有后续 constructor step 不读取这些 binding 时才继续，commit 因而能保留声明本身。
//! closed short pack 的缺失槽则显式投影为 `ImplicitNil` producer；同一声明的槽要么全部删除，
//! 要么由 source preservation plan 整句保留，不能只删一部分 materialization。
//! 旧值已证明为 nil 的简单 local assignment 也可保留，但从该点起只允许独立、无事件的
//! constructor step 前移；赋值仍在原位完成 capture cell 更新和物理 root handoff。
//! 同一 seed 的声明前缀按需归约一次，逐槽 nil 事实只在当前不可变语句快照内有效。
//! 后缀读屏障直接消费上游逐语句 binding 摘要，不按每个保留变量重新遍历表达式。
//! 调用结果 TempId 以 Promotion 的可信 home 进入 producer 计划；删除须由精确覆盖
//! 终点或完整 constructor 的强字段持有/退出事务批准，单写身份自身不签发根释放许可。
//! ConstructorRegion 只发布成功前缀的步骤，保留 producer binding/缺失槽投影、原字段
//! 表达式与批次引用。rebuild 和 commit 消费同一角色划分，不从 stmt_index 反向匹配语法。

use std::cell::OnceCell;
use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{HirExpr, HirLValue, HirStmt, HirTableConstructor, HirValuePack, LocalId};
use crate::hir::expr_safety::{expr_observes_eval_order, expr_requires_ordered_snapshot};
use crate::hir::promotion::ProtoPromotionFacts;
use crate::value_semantics::table::TableExpression;

use super::bindings::{
    BindingIndex, BindingOccurrenceIndex, StmtBindingSummary, binding_from_expr,
    binding_from_lvalue, expr_uses_binding,
};
use super::builder::ConstructorBuilder;
use super::rebuild::producer_value_can_be_dropped;
use super::rebuild::{RegionRebuildContext, try_extend_constructor_from_steps};
use super::{
    BindingId, BindingSlots, PendingProducerSource, ProducerSourcePreservation, RebuildScratch,
    RegionStep, TableBinding,
};

/// 仅含已经由 rebuild 验证事件序与完整消费的前缀；失败后缀不进入提交事实。
/// 步骤借用当前不可变 HIR，安装 constructor 或删除语句前必须结束该借用。
pub(super) struct ConstructorRegion<'a> {
    pub(super) constructor: HirTableConstructor,
    pub(super) end_index: usize,
    pub(super) preserved_stmt_indices: Vec<usize>,
    pub(super) steps: Vec<RegionStep<'a>>,
}

/// 按稳定 stmt id 记录每个 binding 最后可能扩展构造器的位置。
///
/// 空表 seed 只有在后面存在同 binding 的 record 或 SETLIST 时才需要扫描中间 producer；
/// 以最后位置作为 horizon，既允许跨过其他 seed，又能在线性预处理后排除独立 seed 的后缀扫描。
pub(super) struct ConstructorWriteIndex {
    last_write: Vec<Option<usize>>,
}

impl ConstructorWriteIndex {
    pub(super) fn new(stmts: &[HirStmt], binding_index: &BindingIndex) -> Self {
        let mut index = Self {
            last_write: vec![None; binding_index.len()],
        };
        for (stmt_id, stmt) in stmts.iter().enumerate() {
            if let Some(binding) = keyed_write_binding(stmt) {
                let binding_id = binding_index
                    .id_of(binding)
                    .expect("table record binding should be indexed");
                index.last_write[binding_id] = Some(stmt_id);
            } else if let Some(binding) = table_set_list_binding(stmt) {
                let binding_id = binding_index
                    .id_of(binding)
                    .expect("table set-list binding should be indexed");
                index.last_write[binding_id] = Some(stmt_id);
            }
        }
        index
    }

    pub(super) fn has_write_after(&self, binding_id: BindingId, stmt_id: usize) -> bool {
        self.last_write[binding_id].is_some_and(|last| last > stmt_id)
    }
}

pub(super) fn constructor_seed(stmt: &HirStmt) -> Option<(TableBinding, &HirTableConstructor)> {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            let [binding] = local_decl.bindings.as_slice() else {
                return None;
            };
            if local_decl.values.tail.is_some() {
                return None;
            }
            let [HirExpr::TableConstructor(table)] = local_decl.values.fixed.as_slice() else {
                return None;
            };
            Some((TableBinding::Local(*binding), table.as_ref()))
        }
        HirStmt::Assign(assign) => {
            let [target] = assign.targets.as_slice() else {
                return None;
            };
            let binding = binding_from_lvalue(target)?;
            if assign.values.tail.is_some() {
                return None;
            }
            let [HirExpr::TableConstructor(table)] = assign.values.fixed.as_slice() else {
                return None;
            };
            Some((binding, table.as_ref()))
        }
        _ => None,
    }
}

pub(super) fn install_constructor_seed(stmt: &mut HirStmt, constructor: HirTableConstructor) {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            local_decl.values = vec![HirExpr::TableConstructor(Box::new(constructor))].into();
        }
        HirStmt::Assign(assign) => {
            assign.values = vec![HirExpr::TableConstructor(Box::new(constructor))].into();
        }
        _ => unreachable!("constructor region must start from a constructor seed"),
    }
}

pub(super) fn constructor_uses_binding(
    constructor: &HirTableConstructor,
    binding: TableBinding,
) -> bool {
    constructor.fields.iter().any(|field| match field {
        crate::hir::common::HirTableField::Array(value) => expr_uses_binding(value, binding),
        crate::hir::common::HirTableField::Record(record) => {
            expr_uses_binding(&record.key, binding) || expr_uses_binding(&record.value, binding)
        }
    }) || constructor
        .trailing_multivalue
        .as_ref()
        .is_some_and(|tail| expr_uses_binding(tail.as_expr(), binding))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn try_rebuild_constructor_region<'a>(
    block: &'a crate::hir::common::HirBlock,
    seed_index: usize,
    binding: TableBinding,
    constructor: HirTableConstructor,
    binding_index: &BindingIndex,
    binding_occurrences: &BindingOccurrenceIndex,
    stmt_bindings: &[StmtBindingSummary],
    materialized_binding_counts: &[u32],
    debug_identity_bindings: &BindingSlots<bool>,
    promotion_facts: &ProtoPromotionFacts,
    stmt_ids: &[usize],
    scratch: &mut RebuildScratch,
) -> Option<ConstructorRegion<'a>> {
    let allocation = constructor.allocation.clone();
    let mut steps = Vec::new();
    let mut committed_steps = Vec::new();
    let mut use_horizon: Option<usize> = None;
    let mut best_end = None;
    let mut preserved_stmt_indices = Vec::new();
    let mut preserved_bindings = BTreeSet::new();
    let mut has_preserved_assignment = false;
    let preserved_binding_id = |binding| {
        binding_index
            .id_of(binding)
            .expect("preserved binding belongs to the current snapshot")
    };
    let seed_local_values = OnceCell::new();
    let mut committed_builder = ConstructorBuilder::from_constructor(constructor);
    let scan_stmts = &block.stmts[(seed_index + 1)..];
    for (offset, stmt) in scan_stmts.iter().enumerate() {
        let index = seed_index + 1 + offset;
        let remaining_uses = binding_occurrences.remaining_uses_after(stmt_ids[index]);
        if let Some(bindings) = preserved_nil_local_bindings(stmt, debug_identity_bindings) {
            preserved_stmt_indices.push(index);
            preserved_bindings.extend(bindings.into_iter().map(preserved_binding_id));
            continue;
        }
        if let Some(preserved_binding) = preserved_eventless_assignment_binding(
            stmt,
            binding,
            binding_index,
            materialized_binding_counts,
            debug_identity_bindings,
            |local| {
                seed_local_values
                    .get_or_init(|| local_nil_values_before_seed(&block.stmts[..seed_index]))
                    .get(&local)
                    .copied()
                    .unwrap_or(false)
            },
        ) {
            preserved_stmt_indices.push(index);
            preserved_bindings.insert(preserved_binding_id(preserved_binding));
            has_preserved_assignment = true;
            continue;
        }
        if stmt_uses_any_binding(stmt, &stmt_bindings[index], &preserved_bindings) {
            // 候选拒绝[SemanticBarrier:Scope]：保留的 nil local 必须仍先于它的每次读取；
            // assignment target 也必须保持“写后读”。把 `local x=nil; t.v=x` 的字段移进
            // seed 会让 x 在 initializer 中不可见；`x=1; t.v=x` 则会读到旧值。
            break;
        }
        if has_preserved_assignment && !constructor_step_is_unobservable(stmt) {
            // 候选拒绝[SemanticBarrier:EvalOrder]：保留 assignment 的 cell/root handoff 不能
            // 与 call、lookup、allocation 或 metamethod-capable constructor work 交换顺序。
            break;
        }
        let boundary_step = if let Some((owner, key, value)) = keyed_write_parts(stmt)
            && owner == binding
        {
            if !allocation.permits_record_key(key.table_key()) {
                // 候选拒绝[SemanticBarrier:TableShape]：新键不能提前进入原 DUPTABLE；
                // 模板扩大会改变运行时插入/扩容与 pairs 顺序（regress_513）。
                break;
            }
            RegionStep::Record {
                stmt_index: index,
                key,
                value,
            }
        } else if let Some((producer_bindings, source_preservation)) = producer_steps(
            stmt,
            index,
            binding,
            debug_identity_bindings,
            promotion_facts,
            &mut steps,
        ) {
            for producer_binding in producer_bindings {
                let binding_id = binding_index
                    .id_of(producer_binding)
                    .expect("producer binding should be indexed");
                let Some(last_use) = binding_occurrences.last_use(binding_id) else {
                    continue;
                };
                // 同一原始批次还要消费这个 producer 时，不能先把它冻结为区间外声明。
                // 否则 record 前缀先提交、SETLIST 再读取时会被 scope guard 拒绝，且前缀
                // 自身无法复现原数组预分配。稳定 stmt id 单调递增，直接复用现有 use 索引。
                let consumed_by_batch = last_use > stmt_ids[index]
                    && stmt_ids
                        .binary_search(&last_use)
                        .ok()
                        .is_some_and(|last| table_set_list_step(&block.stmts[last], binding));
                if source_preservation != ProducerSourcePreservation::Safe || consumed_by_batch {
                    use_horizon =
                        Some(use_horizon.map_or(last_use, |horizon| horizon.max(last_use)));
                }
            }
            continue;
        } else if let HirStmt::TableSetList(batch) = stmt
            && table_set_list_step(stmt, binding)
        {
            RegionStep::SetList {
                stmt_index: index,
                batch,
            }
        } else {
            // 其它语句不属于 constructor region grammar，遇到时结束后缀候选。
            // 例如 `setmetatable(t, mt); t.x = 1` 若跨过前置 CallStmt，会把字段写入移到
            // 元表安装之前；`if flag then t.x = 1 end` 则会把条件写变成无条件字段。即使
            // 未来扩展其它可保留语句，也必须同时提供对应的 commit removal plan。
            break;
        };
        steps.push(boundary_step);
        // Producer 的最后一次 use 尚在 region 外时，本次事务必然因 remaining_uses
        // 回滚；候选仍完整保留到 horizon，不能因其他失败原因提前丢弃。
        if use_horizon.is_some_and(|horizon| stmt_ids[index] < horizon) {
            continue;
        }
        let mut rebuild_context = RegionRebuildContext::new(
            block,
            binding_index,
            remaining_uses,
            materialized_binding_counts,
            scratch,
        );
        if let Some(preserved_producer_sources) =
            try_extend_constructor_from_steps(&mut committed_builder, &steps, &mut rebuild_context)
        {
            for stmt_index in preserved_producer_sources {
                if preserved_stmt_indices.binary_search(&stmt_index).is_err() {
                    preserved_stmt_indices.push(stmt_index);
                    preserved_stmt_indices.sort_unstable();
                }
                let HirStmt::LocalDecl(local_decl) = &block.stmts[stmt_index] else {
                    unreachable!("preservable producer source must be a local declaration")
                };
                for local in &local_decl.bindings {
                    let binding = TableBinding::Local(*local);
                    preserved_bindings.insert(preserved_binding_id(binding));
                }
            }
            best_end = Some((index, preserved_stmt_indices.clone()));
            committed_steps.append(&mut steps);
            use_horizon = None;
        } else {
            // horizon 已覆盖未来对现有 producer 的引用；后缀无法改写已失败的 segment。
            break;
        }
    }

    // 不要求“扫描到的最长前缀”整体可折叠。
    // 某些稳定构造区域后面会紧跟无关的 local producer；如果继续把它们吞进候选区，
    // 末尾那批未消费 producer 会让整段 region 失败，反而错过前面已经足够安全的
    // `{ ... }` 前缀。因此这里持续记住“最后一个成功前缀”，在真正遇到无关语句时
    // 回退到最近一次可证明安全的构造器边界。
    best_end.map(|(end_index, preserved_stmt_indices)| ConstructorRegion {
        constructor: committed_builder.into_constructor(),
        end_index,
        preserved_stmt_indices,
        steps: committed_steps,
    })
}

/// 显式全 nil 声明没有求值事件，但它的词法 binding 仍可能在区间后使用；声明保持原位，
/// caller 只移动与这些 binding 独立的 constructor work。无 RHS 的 closed pack 交给 producer
/// transaction，以便所有被消费槽一起投影成隐式 nil。
fn preserved_nil_local_bindings(
    stmt: &HirStmt,
    debug_identity_bindings: &BindingSlots<bool>,
) -> Option<Vec<TableBinding>> {
    let HirStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    if local_decl.bindings.is_empty()
        || local_decl.values.tail.is_some()
        || local_decl.values.fixed.is_empty()
        || local_decl
            .values
            .fixed
            .iter()
            .any(|value| !matches!(value, HirExpr::Nil))
    {
        return None;
    }
    let bindings = local_decl
        .bindings
        .iter()
        .copied()
        .map(TableBinding::Local)
        .collect::<Vec<_>>();
    if bindings.iter().any(|binding| {
        debug_identity_bindings
            .get(*binding)
            .copied()
            .unwrap_or_default()
    }) {
        // 候选拒绝[SemanticBarrier:DebugScope]：即使 nil 初始化没有求值事件，把后续字段
        // 提前到 debug local 声明之前仍会改变 hook 在该行观察到的 table 内容。
        return None;
    }
    Some(bindings)
}

fn preserved_eventless_assignment_binding(
    stmt: &HirStmt,
    constructor_binding: TableBinding,
    binding_index: &BindingIndex,
    materialized_binding_counts: &[u32],
    debug_identity_bindings: &BindingSlots<bool>,
    local_is_nil: impl FnOnce(LocalId) -> bool,
) -> Option<TableBinding> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let binding = simple_assignment_binding_if_eventless(assign, constructor_binding)?;
    let TableBinding::Local(local) = binding else {
        return None;
    };
    let binding_id = binding_index.id_of(binding)?;
    if materialized_binding_counts.get(binding_id).copied() != Some(2) || !local_is_nil(local) {
        // 候选拒绝[SemanticBarrier:Lifetime]：field 进入 seed 会把 table 内部 allocation/GC
        // 移到 assignment 前；只有旧值已证明为 nil 时，才不会跨过 root release 点。
        return None;
    }
    if debug_identity_bindings
        .get(binding)
        .copied()
        .unwrap_or_default()
    {
        // 候选拒绝[SemanticBarrier:DebugScope]：字段提前到 source-visible assignment 之前，
        // 会改变 hook 在赋值行观察到的 fresh table 内容。
        return None;
    }
    Some(binding)
}

/// 当前候选的声明前缀只归约一次；最近声明覆盖旧事实，用户代码屏障阻断更早来源。
fn local_nil_values_before_seed(stmts: &[HirStmt]) -> BTreeMap<LocalId, bool> {
    let mut values = BTreeMap::new();
    for stmt in stmts.iter().rev() {
        let HirStmt::LocalDecl(local_decl) = stmt else {
            break;
        };
        for (slot_index, &binding) in local_decl.bindings.iter().enumerate() {
            values.entry(binding).or_insert_with(|| {
                local_decl.values.tail.is_none()
                    && local_decl
                        .values
                        .fixed
                        .get(slot_index)
                        .is_none_or(|value| matches!(value, HirExpr::Nil))
            });
        }
        if local_decl.values.tail.is_some()
            || local_decl
                .values
                .fixed
                .iter()
                .any(|value| !local_prefix_expr_cannot_invoke_user_code(value))
        {
            break;
        }
    }
    values
}

fn local_prefix_expr_cannot_invoke_user_code(expr: &HirExpr) -> bool {
    seed_delay_expr_is_unobservable(expr)
        || matches!(
            expr,
            HirExpr::Closure(closure)
                if closure
                    .captures
                    .iter()
                    .all(|capture| seed_delay_expr_is_unobservable(&capture.value))
        )
}

fn simple_assignment_binding_if_eventless(
    assign: &crate::hir::common::HirAssign,
    constructor_binding: TableBinding,
) -> Option<TableBinding> {
    let [target] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.fixed.as_slice() else {
        return None;
    };
    if assign.values.tail.is_some() {
        return None;
    }
    let binding = binding_from_lvalue(target)?;
    if binding == constructor_binding
        || !seed_delay_expr_is_unobservable(value)
        || expr_uses_binding(value, constructor_binding)
    {
        return None;
    }
    Some(binding)
}

fn constructor_step_is_unobservable(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            local_decl.values.tail.is_none()
                && local_decl
                    .values
                    .fixed
                    .iter()
                    .all(seed_delay_expr_is_unobservable)
        }
        HirStmt::Assign(assign) => {
            let [HirLValue::TableAccess(access)] = assign.targets.as_slice() else {
                return false;
            };
            let [value] = assign.values.fixed.as_slice() else {
                return false;
            };
            assign.values.tail.is_none()
                && seed_delay_expr_is_unobservable(&access.key)
                && seed_delay_expr_is_unobservable(value)
        }
        HirStmt::TableSetList(set_list) => {
            set_list.values.tail.is_none()
                && set_list
                    .values
                    .fixed
                    .iter()
                    .all(seed_delay_expr_is_unobservable)
        }
        _ => false,
    }
}

fn stmt_uses_any_binding(
    stmt: &HirStmt,
    summary: &StmtBindingSummary,
    bindings: &BTreeSet<BindingId>,
) -> bool {
    !bindings.is_empty()
        && matches!(
            stmt,
            HirStmt::LocalDecl(_) | HirStmt::Assign(_) | HirStmt::TableSetList(_)
        )
        && summary.uses().any(|binding| bindings.contains(&binding))
}

fn keyed_write_binding(stmt: &HirStmt) -> Option<TableBinding> {
    keyed_write_parts(stmt).map(|(binding, _, _)| binding)
}

fn keyed_write_parts(stmt: &HirStmt) -> Option<(TableBinding, &HirExpr, &HirExpr)> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [HirLValue::TableAccess(access)] = assign.targets.as_slice() else {
        return None;
    };
    if assign.values.tail.is_some() {
        return None;
    }
    let [value] = assign.values.fixed.as_slice() else {
        return None;
    };
    let binding = binding_from_expr(&access.base)?;
    if expr_uses_binding(&access.key, binding) || expr_uses_binding(value, binding) {
        // 候选拒绝[SemanticBarrier:Scope]：`t[t] = v` / `t.x = t` 若进入
        // `local t = { ... }`，initializer 内的 `t` 不再指向刚创建的 owner。
        return None;
    }
    Some((binding, &access.key, value))
}

fn producer_steps<'a>(
    stmt: &'a HirStmt,
    stmt_index: usize,
    constructor_binding: TableBinding,
    debug_identity_bindings: &BindingSlots<bool>,
    promotion_facts: &ProtoPromotionFacts,
    steps: &mut Vec<RegionStep<'a>>,
) -> Option<(Vec<TableBinding>, ProducerSourcePreservation)> {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            let bindings = local_decl
                .bindings
                .iter()
                .copied()
                .map(TableBinding::Local)
                .collect::<Vec<_>>();
            let source_preservation = producer_source_preservation(
                &bindings,
                &local_decl.values,
                debug_identity_bindings,
            );
            producer_steps_from_bindings(
                bindings,
                &local_decl.values,
                constructor_binding,
                stmt_index,
                source_preservation,
                steps,
            )
            .map(|bindings| (bindings, source_preservation))
        }
        HirStmt::Assign(assign) if matches!(assign.targets.as_slice(), [HirLValue::Temp(_)]) => {
            let [HirLValue::Temp(temp)] = assign.targets.as_slice() else {
                unreachable!("checked scalar temp producer")
            };
            if !matches!(assign.values.fixed.as_slice(), [HirExpr::Call(_)])
                || promotion_facts.trusted_temp_home_slot(*temp).is_none()
            {
                return None;
            }
            // scanner 只保留原始值身份；commit 消费精确覆盖终点或终点强持有证明，
            // 不能把可信 home 与单写 TempId 自身当成任意 assignment 的删除许可。
            let bindings = vec![TableBinding::Temp(*temp)];
            let preservation =
                producer_source_preservation(&bindings, &assign.values, debug_identity_bindings);
            producer_steps_from_bindings(
                bindings,
                &assign.values,
                constructor_binding,
                stmt_index,
                preservation,
                steps,
            )
            .map(|bindings| (bindings, preservation))
        }
        // entry-nil、保留原写且只跨无事件字段的 assignment 已由 scanner 提前消费；
        // 其余 assignment 不是 producer declaration，并可能带独立 root/写后读语义。
        // `lua54_01_close#9` 的旧对象覆盖必须保留精确释放点；`x=1; t.v=x` 又要求字段维持
        // 写后读，不能把它们混入由声明删除驱动的 producer transaction。
        HirStmt::Assign(_) => None,
        _ => None,
    }
}

fn producer_steps_from_bindings<'a>(
    bindings: Vec<TableBinding>,
    values: &'a HirValuePack,
    constructor_binding: TableBinding,
    stmt_index: usize,
    source_preservation: ProducerSourcePreservation,
    steps: &mut Vec<RegionStep<'a>>,
) -> Option<Vec<TableBinding>> {
    if bindings.is_empty() {
        return None;
    }
    // 候选拒绝[SemanticBarrier:Scope]：`local t = t` 或 producer RHS 读取 owner 时，
    // 搬进 `local t = { ... }` 会让读取解析到外层/旧 binding，而不是新表 owner。
    if bindings.contains(&constructor_binding)
        || values
            .iter()
            .any(|value| expr_uses_binding(value, constructor_binding))
    {
        return None;
    }

    if values.tail.is_some() {
        // 候选拒绝[SemanticBarrier:ValueArity]：open tail 的运行时宽度不固定；
        // exact tail 也只保存一个 pack carrier 而没有逐槽 scalar projection。把它当作
        // closed producer 会伪造 nil 槽或重复整个 tail。
        return None;
    }
    if let Some(surplus) = values.fixed.get(bindings.len()..) {
        if surplus.iter().any(expr_observes_eval_order) {
            // 候选拒绝[SemanticBarrier:EvalCount]：多余 RHS 仍必须按源码顺序求值；直接
            // zip 并删除 `local value = 1, mark()` 会丢掉 mark 调用。
            return None;
        }
        if surplus
            .iter()
            .any(|value| matches!(value, HirExpr::Closure(_)))
        {
            // 候选拒绝[SemanticBarrier:Lifetime]：discarded closure 仍会建立 ByReference
            // upvalue/root；删除整句会改变被捕获对象跨后续 GC/Close 的存活期。
            return None;
        }
        if surplus
            .iter()
            .any(|value| matches!(value, HirExpr::Unresolved(_)))
        {
            // 候选拒绝[PolicyBoundary]：Unresolved 是 permissive 输出的失败证据，
            // 本 pass 不把它当成可静默丢弃的 closed scalar RHS。
            return None;
        }
        debug_assert!(surplus.iter().all(seed_delay_expr_is_unobservable));
    }

    let scalar_call = bindings.len() == 1 && matches!(values.fixed.as_slice(), [HirExpr::Call(_)]);
    let source_gc_inert = values.fixed.iter().all(producer_value_can_be_dropped);
    steps.extend(
        bindings
            .iter()
            .enumerate()
            .map(|(slot_index, binding)| RegionStep::Producer {
                binding: *binding,
                source: if slot_index < values.fixed.len() {
                    PendingProducerSource::Value {
                        stmt_index,
                        value_index: slot_index,
                    }
                } else {
                    PendingProducerSource::ImplicitNil { stmt_index }
                },
                value: values.fixed.get(slot_index).unwrap_or(&HirExpr::Nil),
                scalar_call,
                source_gc_inert,
                source_preservation,
            }),
    );
    Some(bindings)
}

fn producer_source_preservation(
    bindings: &[TableBinding],
    values: &HirValuePack,
    debug_identity_bindings: &BindingSlots<bool>,
) -> ProducerSourcePreservation {
    if values
        .fixed
        .iter()
        .any(|value| matches!(value, HirExpr::Unresolved(_)))
    {
        return ProducerSourcePreservation::UnsupportedShape;
    }
    if bindings.iter().any(|binding| {
        debug_identity_bindings
            .get(*binding)
            .copied()
            .unwrap_or_default()
    }) {
        return ProducerSourcePreservation::DebugIdentity;
    }
    if values.fixed.iter().any(expr_requires_ordered_snapshot) {
        return ProducerSourcePreservation::ObservableReplay;
    }
    if values
        .fixed
        .iter()
        .any(|value| matches!(value, HirExpr::Closure(_)))
    {
        // Closure allocation creates one identity/root even when all captures are eventless.
        // A preserved source plus an inlined field would allocate it twice; a removed partial
        // declaration would instead drop another slot's root.
        return ProducerSourcePreservation::ObservableReplay;
    }
    if values.fixed.iter().all(|value| {
        matches!(
            value,
            HirExpr::Nil
                | HirExpr::Boolean(_)
                | HirExpr::Integer(_)
                | HirExpr::Number(_)
                | HirExpr::String(_)
                | HirExpr::Int64(_)
                | HirExpr::UInt64(_)
                | HirExpr::Vector(_)
                | HirExpr::Complex { .. }
                | HirExpr::VarArg
        )
    }) {
        if bindings.len() == 1 && values.fixed.len() == 1 {
            ProducerSourcePreservation::Safe
        } else {
            // Multi-slot, nil-padded, primitive-surplus, and scalar-vararg declarations are safe
            // to retain only as one statement. The distinct plan also keeps scanner's last-use
            // horizon active so every consumable slot joins the same removal transaction.
            ProducerSourcePreservation::InertWholeStatement
        }
    } else {
        // Every current non-residual HIR expression outside the scalar set above either requires
        // an ordered snapshot or allocates a closure. Keep future expression kinds on the same
        // replay-safe side until they provide a narrower source-preservation proof.
        ProducerSourcePreservation::ObservableReplay
    }
}

pub(super) fn seed_overwrite_delay_is_unobservable(
    block: &crate::hir::common::HirBlock,
    seed_index: usize,
    end_index: usize,
    binding: TableBinding,
) -> bool {
    block.stmts[(seed_index + 1)..=end_index]
        .iter()
        .all(|stmt| match stmt {
            HirStmt::LocalDecl(decl) => {
                decl.values.tail.is_none()
                    && decl.values.fixed.iter().all(producer_value_can_be_dropped)
                    && decl
                        .values
                        .fixed
                        .iter()
                        .all(|value| !expr_uses_binding(value, binding))
            }
            HirStmt::Assign(assign) => {
                if let [HirLValue::TableAccess(access)] = assign.targets.as_slice() {
                    assign.values.tail.is_none()
                        && binding_from_expr(&access.base) == Some(binding)
                        && seed_delay_expr_is_unobservable(&access.key)
                        && assign
                            .values
                            .fixed
                            .iter()
                            .all(seed_delay_expr_is_unobservable)
                } else {
                    simple_assignment_binding_if_eventless(assign, binding).is_some()
                }
            }
            HirStmt::TableSetList(set_list) => {
                binding_from_expr(&set_list.base) == Some(binding)
                    && set_list.values.tail.is_none()
                    && set_list
                        .values
                        .fixed
                        .iter()
                        .all(seed_delay_expr_is_unobservable)
            }
            _ => false,
        })
}

pub(super) fn seed_delay_expr_is_unobservable(expr: &HirExpr) -> bool {
    matches!(
        expr,
        HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::Int64(_)
            | HirExpr::UInt64(_)
            | HirExpr::Vector(_)
            | HirExpr::Complex { .. }
            | HirExpr::ParamRef(_)
            | HirExpr::LocalRef(_)
            | HirExpr::UpvalueRef(_)
            | HirExpr::TempRef(_)
            | HirExpr::VarArg
    )
}

fn table_set_list_step(stmt: &HirStmt, binding: TableBinding) -> bool {
    table_set_list_binding(stmt) == Some(binding)
}

fn table_set_list_binding(stmt: &HirStmt) -> Option<TableBinding> {
    let HirStmt::TableSetList(set_list) = stmt else {
        return None;
    };
    let binding = binding_from_expr(&set_list.base)?;
    if set_list
        .values
        .fixed
        .iter()
        .any(|expr| expr_uses_binding(expr, binding))
        || set_list
            .values
            .tail
            .as_ref()
            .is_some_and(|tail| expr_uses_binding(tail.as_expr(), binding))
    {
        // 候选拒绝[SemanticBarrier:Scope]：SETLIST 值读取 owner 时不能搬进 owner 自身的
        // initializer；`local t = {}; t[1] = t` 与 `local t = { t }` 解析不同 binding。
        return None;
    }
    Some(binding)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use crate::hir::common::{
        HirAssign, HirBlock, HirCallExpr, HirExpr, HirGlobalRef, HirLValue, HirLocalDecl,
        HirPackTail, HirReturn, HirStmt, HirTableAccess, HirTableConstructor, HirTableField,
        HirValuePack, LocalId,
    };
    use crate::hir::promotion::ProtoPromotionFacts;

    use super::super::bindings::{
        BindingIndex, BindingOccurrenceIndex, BindingSlots, collect_stmt_binding_summary,
    };
    use super::{TableBinding, try_rebuild_constructor_region};

    fn local(binding: LocalId, value: HirExpr) -> HirStmt {
        HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: vec![binding],
            values: HirValuePack::fixed(vec![value]),
            initializer_merge_transaction: None,
        }))
    }

    fn record(table: LocalId, value: HirExpr) -> HirStmt {
        record_named(table, "field", value)
    }

    fn record_named(table: LocalId, key: &str, value: HirExpr) -> HirStmt {
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::TableAccess(Box::new(HirTableAccess {
                base: HirExpr::LocalRef(table),
                key: HirExpr::String(key.into()),
                method_setup_protocol: None,
            }))],
            values: HirValuePack::fixed(vec![value]),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        }))
    }

    fn call(name: &str) -> HirExpr {
        HirExpr::Call(Box::new(HirCallExpr {
            argument_roots: Vec::new(),
            frame_root_ends: Vec::new(),
            callee: HirExpr::GlobalRef(HirGlobalRef { key: name.into() }),
            args: HirValuePack::default(),
            method: false,
            fastcall: None,
            method_key: None,
            callee_root_handoff: None,
            method_rewrite_transaction: None,
        }))
    }

    fn returned(value: HirExpr) -> HirStmt {
        HirStmt::Return(Box::new(HirReturn {
            source_instr: None,
            values: HirValuePack::fixed(vec![value]),
        }))
    }

    fn rebuild(block: &HirBlock) -> Option<(HirTableConstructor, usize, Vec<usize>)> {
        let mut binding_index = BindingIndex::new(0, 3);
        let summaries = block
            .stmts
            .iter()
            .map(|stmt| collect_stmt_binding_summary(stmt, &mut binding_index))
            .collect::<Vec<_>>();
        let debug_identities = BindingSlots::from_debug_hints(&[], &[None, None, None]);
        let occurrences = BindingOccurrenceIndex::new(
            &binding_index,
            &summaries,
            &debug_identities,
            &BTreeSet::new(),
            &debug_identities,
            &ProtoPromotionFacts::default(),
        );
        let stmt_ids = (0..block.stmts.len()).collect::<Vec<_>>();
        let materialized_counts = vec![1; binding_index.len()];
        let mut scratch = Default::default();
        try_rebuild_constructor_region(
            block,
            0,
            TableBinding::Local(LocalId(0)),
            HirTableConstructor::default(),
            &binding_index,
            &occurrences,
            &summaries,
            &materialized_counts,
            &debug_identities,
            &ProtoPromotionFacts::default(),
            &stmt_ids,
            &mut scratch,
        )
        .map(|region| {
            (
                region.constructor,
                region.end_index,
                region.preserved_stmt_indices,
            )
        })
    }

    #[test]
    fn scalar_producer_with_later_use_is_preserved_after_partial_rebuild() {
        let block = HirBlock {
            stmts: vec![
                local(LocalId(0), HirExpr::TableConstructor(Box::default())),
                local(LocalId(1), HirExpr::Integer(7)),
                record(LocalId(0), HirExpr::LocalRef(LocalId(1))),
                returned(HirExpr::LocalRef(LocalId(1))),
            ],
        };

        let (constructor, end_index, preserved) =
            rebuild(&block).expect("eventless scalar source should support partial rebuild");

        assert_eq!(end_index, 2);
        assert_eq!(preserved, vec![1]);
        assert_eq!(
            constructor.fields,
            vec![HirTableField::Record(crate::hir::common::HirRecordField {
                key: HirExpr::String("field".into()),
                value: HirExpr::Integer(7),
            })]
        );
    }

    #[test]
    fn multi_slot_scalar_vararg_preserves_the_whole_source_for_an_unconsumed_slot() {
        let block = HirBlock {
            stmts: vec![
                local(LocalId(0), HirExpr::TableConstructor(Box::default())),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![LocalId(1), LocalId(2)],
                    values: HirValuePack::fixed(vec![HirExpr::VarArg, HirExpr::Integer(7)]),
                    initializer_merge_transaction: None,
                })),
                record(LocalId(0), HirExpr::LocalRef(LocalId(1))),
            ],
        };

        let (constructor, end_index, preserved) = rebuild(&block)
            .expect("scalar vararg slots should share the whole-statement preservation plan");

        assert_eq!(end_index, 2);
        assert_eq!(preserved, vec![1]);
        assert!(matches!(
            constructor.fields.as_slice(),
            [HirTableField::Record(field)] if field.value == HirExpr::VarArg
        ));
    }

    #[test]
    fn unconsumed_scalar_producer_is_preserved_around_rebuilt_field() {
        let block = HirBlock {
            stmts: vec![
                local(LocalId(0), HirExpr::TableConstructor(Box::default())),
                local(LocalId(1), HirExpr::Integer(7)),
                record(LocalId(0), HirExpr::Integer(9)),
            ],
        };

        let (constructor, end_index, preserved) =
            rebuild(&block).expect("unconsumed eventless source should remain in the block");

        assert_eq!(end_index, 2);
        assert_eq!(preserved, vec![1]);
        assert_eq!(constructor.fields.len(), 1);
    }

    #[test]
    fn allocated_producer_with_later_use_keeps_the_original_region() {
        let block = HirBlock {
            stmts: vec![
                local(LocalId(0), HirExpr::TableConstructor(Box::default())),
                local(LocalId(1), HirExpr::TableConstructor(Box::default())),
                record(LocalId(0), HirExpr::LocalRef(LocalId(1))),
                returned(HirExpr::LocalRef(LocalId(1))),
            ],
        };

        assert!(rebuild(&block).is_none());
    }

    #[test]
    fn closed_short_pack_projects_missing_binding_as_nil() {
        let block = HirBlock {
            stmts: vec![
                local(LocalId(0), HirExpr::TableConstructor(Box::default())),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![LocalId(1), LocalId(2)],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(7)]),
                    initializer_merge_transaction: None,
                })),
                record_named(LocalId(0), "first", HirExpr::LocalRef(LocalId(1))),
                record_named(LocalId(0), "second", HirExpr::LocalRef(LocalId(2))),
            ],
        };

        let (constructor, end_index, preserved) =
            rebuild(&block).expect("closed short pack should provide nil for missing slots");

        assert_eq!(end_index, 3);
        assert!(preserved.is_empty());
        assert_eq!(
            constructor.fields,
            vec![
                HirTableField::Record(crate::hir::common::HirRecordField {
                    key: HirExpr::String("first".into()),
                    value: HirExpr::Integer(7),
                }),
                HirTableField::Record(crate::hir::common::HirRecordField {
                    key: HirExpr::String("second".into()),
                    value: HirExpr::Nil,
                }),
            ]
        );
    }

    #[test]
    fn zero_rhs_projects_every_consumed_binding_as_nil() {
        let block = HirBlock {
            stmts: vec![
                local(LocalId(0), HirExpr::TableConstructor(Box::default())),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![LocalId(1), LocalId(2)],
                    values: HirValuePack::default(),
                    initializer_merge_transaction: None,
                })),
                record_named(LocalId(0), "first", HirExpr::LocalRef(LocalId(1))),
                record_named(LocalId(0), "second", HirExpr::LocalRef(LocalId(2))),
            ],
        };

        let (constructor, end_index, preserved) =
            rebuild(&block).expect("zero RHS should nil-pad every consumed binding");

        assert_eq!(end_index, 3);
        assert!(preserved.is_empty());
        assert_eq!(
            constructor
                .fields
                .iter()
                .map(|field| match field {
                    HirTableField::Record(field) => &field.value,
                    HirTableField::Array(_) => panic!("expected record field"),
                })
                .collect::<Vec<_>>(),
            vec![&HirExpr::Nil, &HirExpr::Nil]
        );
    }

    #[test]
    fn short_pack_preserves_the_whole_declaration_when_a_slot_is_unconsumed() {
        let block = HirBlock {
            stmts: vec![
                local(LocalId(0), HirExpr::TableConstructor(Box::default())),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![LocalId(1), LocalId(2)],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(7)]),
                    initializer_merge_transaction: None,
                })),
                record(LocalId(0), HirExpr::LocalRef(LocalId(1))),
            ],
        };

        let (constructor, end_index, preserved) =
            rebuild(&block).expect("inert multi-slot source may remain as one declaration");

        assert_eq!(end_index, 2);
        assert_eq!(preserved, vec![1]);
        assert_eq!(constructor.fields.len(), 1);
    }

    #[test]
    fn surplus_primitive_rhs_can_be_discarded() {
        let block = HirBlock {
            stmts: vec![
                local(LocalId(0), HirExpr::TableConstructor(Box::default())),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![LocalId(1)],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(7), HirExpr::Integer(8)]),
                    initializer_merge_transaction: None,
                })),
                record(LocalId(0), HirExpr::LocalRef(LocalId(1))),
            ],
        };

        let (constructor, end_index, preserved) =
            rebuild(&block).expect("primitive discarded RHS has no event or surviving root");

        assert_eq!(end_index, 2);
        assert!(preserved.is_empty());
        assert!(matches!(
            constructor.fields.as_slice(),
            [HirTableField::Record(field)] if field.value == HirExpr::Integer(7)
        ));
    }

    #[test]
    fn surplus_scalar_vararg_rhs_can_be_discarded() {
        let block = HirBlock {
            stmts: vec![
                local(LocalId(0), HirExpr::TableConstructor(Box::default())),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![LocalId(1)],
                    // 非末槽 vararg 处于 scalar context；它不读取可变 binding，也不产生事件。
                    values: HirValuePack::fixed(vec![
                        HirExpr::Integer(7),
                        HirExpr::VarArg,
                        HirExpr::Integer(8),
                    ]),
                    initializer_merge_transaction: None,
                })),
                record(LocalId(0), HirExpr::LocalRef(LocalId(1))),
            ],
        };

        let (constructor, end_index, preserved) =
            rebuild(&block).expect("discarded scalar vararg has no event or surviving root");

        assert_eq!(end_index, 2);
        assert!(preserved.is_empty());
        assert!(matches!(
            constructor.fields.as_slice(),
            [HirTableField::Record(field)] if field.value == HirExpr::Integer(7)
        ));
    }

    #[test]
    fn surplus_effectful_rhs_keeps_the_original_region() {
        let block = HirBlock {
            stmts: vec![
                local(LocalId(0), HirExpr::TableConstructor(Box::default())),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![LocalId(1)],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(7), call("mark")]),
                    initializer_merge_transaction: None,
                })),
                record(LocalId(0), HirExpr::LocalRef(LocalId(1))),
            ],
        };

        assert!(rebuild(&block).is_none());
    }

    #[test]
    fn pack_tail_is_not_treated_as_closed_nil_padding() {
        for tail in [
            HirPackTail::open(HirExpr::VarArg),
            HirPackTail::exact(HirExpr::VarArg, 2),
        ] {
            let block = HirBlock {
                stmts: vec![
                    local(LocalId(0), HirExpr::TableConstructor(Box::default())),
                    HirStmt::LocalDecl(Box::new(HirLocalDecl {
                        bindings: vec![LocalId(1), LocalId(2)],
                        values: HirValuePack::expanding(Vec::new(), tail),
                        initializer_merge_transaction: None,
                    })),
                    record_named(LocalId(0), "first", HirExpr::LocalRef(LocalId(1))),
                    record_named(LocalId(0), "second", HirExpr::LocalRef(LocalId(2))),
                ],
            };

            assert!(rebuild(&block).is_none());
        }
    }
}
