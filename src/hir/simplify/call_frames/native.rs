//! 为根块的普通调用建立一次完整源码帧事务，并验证删除后的全局声明身份。
//!
//! 调用树、Def 版本与槽距由父模块的共享 FrameBuilder 核对，实际源码低槽前缀由
//! prefix owner 核对。callee 为零返回时原槽可能未覆写，因此这里只整体吸收调用树，
//! 不单独撤销 root 保护。多个调用可复用同一匿名 LocalId；事务在同一 preview 中删除
//! 已消费的声明/读取，并把该身份的下一次独立写移为声明，禁止留下悬空 read/capture。
//! 例如先 `c=table.concat; print(c(t))` 后 `c=table; print(c.concat(t))`，必须同时
//! 核对每次原 home 与后缀身份，不能凭第一次调用布局删除后续还在读取的 source local。
//! 单返回初始化同样保留原结果 home 与目标声明；已有参数表消费原 argument-root 交接。
//! PUC 的完整构造器事务还消费构造器 owner 的字段/SETLIST 角色，并由 tables 核对
//! 原暂存槽与事件；普通 CALL 与 TAILCALL 保持各自结果协议。没有固定返回值不表示
//! callee 槽必然被清空；无物理根的辅助初始化也可能是后续完整帧所需的声明前缀。
//! PUC 与 Luau 的既有低槽单结果赋值共同消费原 CALL 和首 MOVE，后继低槽 COPY
//! 仍由原身份与写域保护；不能将 CALL scratch 独立冻结为永久声明来绕过赋值事务。
//! 比较准备和后继数值循环头可将原 CALL scratch 误留成跨段 Local；这里向作用域
//! owner 提供未提交的完整帧预览，由它同时恢复 do 末端并核对整个后缀后提交。
//! 例如 `do local n=nil; local v=g end; if captured~=f() then h() end; for ...`
//! 必须共同重发两个比较 operand 和后继控制帧，不能把比较读取视为提前退休 CALL 根。
//! 双 CALL 比较也能在此消费原 SELF receiver 的双用途 carrier；方法协议仍由共享
//! builder 签证，作用域 owner 不把有读取的 receiver 误当作死声明吸收。
//! 独立构造器与接收 CALL 的构造器共用 builder 和前缀提交；已被调用拥有的构造器
//! 不重复建计划，其余候选同批验证，避免拆开原来必须共同退休的帧。
//! PUC 空表与 Luau 静态模板赋值先在空闲槽分配，再 MOVE 到已有低槽 local；同一事务
//! 可收回相邻 allocation/COPY，避免给原临时槽留下永久声明。全局/索引赋值有独立
//! 提交事件，不使用这个许可；被删 scratch 的后续读取/capture 仍由整批 preview 拒绝。
//! 多结果 RETURN 的连续准备区同样重发原 COPY；Luau 连续低槽直返优化不能省去原高槽写。
//! 永久来源与 cleanup 事务分开，不能因清理已消费而重新猜测返回槽。单结果 CALL 紧邻
//! 被同槽惰性常量覆盖时可丢弃结果，但必须同时保留调用帧与随后声明，不能只删 producer。

use super::*;
use crate::hir::common::{HirBinding, HirInlineRetentionReason, HirLocalDecl, TempId};
use crate::hir::simplify::mention::{BindingReadCollector, BindingWriteCollector};
use crate::hir::visit::visit_stmts;

mod indexed;

struct Plan {
    start: usize,
    sink: usize,
    base: HomeSlotKey,
    values: HirValuePack,
    result_local: Option<LocalId>,
    discarded_result: Option<LocalId>,
    assignment_targets: Vec<LocalId>,
    indexed_target: Option<crate::hir::common::HirTableAccess>,
    retained_copies: Vec<(usize, LocalId, LocalId)>,
    removed: Vec<usize>,
}

struct Preview {
    proto: HirProto,
    removed: Vec<bool>,
}

impl Plan {
    fn prefix_request(&self) -> (usize, prefix::PrefixRequest) {
        (
            self.start,
            prefix::PrefixRequest {
                home: self.base,
                required: self
                    .retained_copies
                    .iter()
                    .flat_map(|(_, target, source)| [*target, *source])
                    .chain(self.assignment_targets.iter().copied())
                    .collect(),
            },
        )
    }
}

fn scalar_binding(stmt: &HirStmt) -> Option<(HirBinding, &HirExpr)> {
    if let Some((local, value)) = scalar_local(stmt) {
        return Some((HirBinding::Local(local), value));
    }
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    match (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) {
        ([HirLValue::Temp(temp)], [value], None) => Some((HirBinding::Temp(*temp), value)),
        _ => None,
    }
}

/// 交给作用域 owner 的未提交帧预览。只消费能由最终调用或 If/for 来源重建
/// 入口请求的计划；赋值目标从最终 Assign 恢复 required，retained-COPY 的独立端点
/// 及结果声明义务不能在跨 owner 时丢失，因此仍留给原完整计划事务。
/// 原同 home 构造器的结果声明可由最终 LocalDecl 重建入口；与后继调用同批消费，
/// 避免未关闭的 nil/global scope 与未完成构造器前缀互相等待。
/// 先结束原 DFS 删除与 value-epoch 验证，再让作用域 owner 重新编号并验证完整后缀。
pub(in crate::hir::simplify) fn prepare_source_frames(
    proto: HirProto,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
) -> Option<HirProto> {
    let restrictions = frame_restrictions(&proto, facts);
    let (mut plans, count) = collect_native_plans(
        NativeFrameContext {
            proto: &proto,
            barred: &restrictions.barred,
            closed: &restrictions.closed,
            constants_fit_rk: tables::constants_fit_rk(&proto),
        },
        facts,
        dialect,
    );
    plans.retain(|plan| {
        plan.retained_copies.is_empty()
            && plan.result_local.is_none_or(|local| {
                facts.trusted_local_home_slot(local) == Some(plan.base)
                    && matches!((plan.values.fixed.as_slice(), &plan.values.tail),
                        ([HirExpr::TableConstructor(table)], None)
                            if facts.allocation_result_home(table) == Some(plan.base))
            })
            && plan.discarded_result.is_none()
            // 候选拒绝[LayerBoundary]：计算左值也占用入口帧；作用域 owner 尚只从 RHS 恢复请求。
            && plan.indexed_target.is_none()
    });
    if plans.is_empty() {
        return Some(proto);
    }
    let mut preview = apply_preview(proto, &plans, count)?;
    compact_scope(&mut preview.proto.body, &preview.removed, &mut 0);
    Some(preview.proto)
}

pub(super) fn restore(
    proto: &mut HirProto,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    barred: &BTreeSet<HomeSlotKey>,
    closed: &BTreeSet<HomeSlotKey>,
    is_chunk_entry: bool,
) -> bool {
    let (plans, stmt_count) = collect_native_plans(
        NativeFrameContext {
            proto,
            barred,
            closed,
            constants_fit_rk: tables::constants_fit_rk(proto),
        },
        facts,
        dialect,
    );
    commit_plans(proto, facts, dialect, is_chunk_entry, plans, stmt_count)
}

/// 普通帧和独立构造器共用同一坐标/占用索引；未提交的 scope preview 与直接提交
/// 不各自重建一套候选协议，所有重叠筛选都发生在删除任何语句之前。
fn collect_native_plans(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
) -> (Vec<Plan>, usize) {
    let mut plans = Vec::new();
    let mut stmt_count = 0;
    collect_plans(
        context.proto,
        &context.proto.body,
        facts,
        dialect,
        context.barred,
        context.closed,
        context.constants_fit_rk,
        &mut stmt_count,
        &mut plans,
    );
    let mut constructors = Vec::new();
    let mut constructor_stmt_count = 0;
    collect_constructor_plans(
        context,
        facts,
        dialect,
        &mut constructor_stmt_count,
        &mut constructors,
    );
    // 构造器释放的 callee 身份可能被下一次 CALL 的准备区复用，两者必须共同退休。
    // 已由外层调用消费的构造器不再建立第二个事务；其余候选在同一源码帧预览中验证。
    let occupied = plans
        .iter()
        .flat_map(|plan| plan.removed.iter().copied().chain([plan.sink]))
        .collect::<BTreeSet<_>>();
    plans.extend(constructors.into_iter().filter(|plan| {
        !occupied.contains(&plan.sink) && plan.removed.iter().all(|index| !occupied.contains(index))
    }));
    plans.sort_unstable_by_key(|plan| plan.sink);
    (plans, stmt_count)
}

fn commit_plans(
    proto: &mut HirProto,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    is_chunk_entry: bool,
    mut plans: Vec<Plan>,
    stmt_count: usize,
) -> bool {
    // 较早事务借用的后缀 COPY 是其覆盖证明的一部分；同批后来的候选不能再次消费它。
    let mut retained_statements = BTreeSet::new();
    plans.retain(|plan| {
        if retained_statements.contains(&plan.sink)
            || plan
                .removed
                .iter()
                .any(|index| retained_statements.contains(index))
        {
            return false;
        }
        retained_statements.extend(plan.retained_copies.iter().map(|(index, _, _)| *index));
        true
    });
    if plans.is_empty() {
        return false;
    }
    let Some(mut preview) = build_preview(proto, &plans, stmt_count) else {
        return false;
    };
    let preserved = match validate_plan_batch(&mut preview, &plans, facts, dialect, is_chunk_entry)
    {
        Ok(preserved) => preserved,
        Err(index) => {
            plans.retain(|plan| plan.start < index);
            if plans.is_empty() {
                return false;
            }
            let Some(revised) = build_preview(proto, &plans, stmt_count) else {
                return false;
            };
            preview = revised;
            let Ok(preserved) =
                validate_plan_batch(&mut preview, &plans, facts, dialect, is_chunk_entry)
            else {
                return false;
            };
            preserved
        }
    };
    let mut preserved = preserved;
    preserved.extend(plans.iter().filter_map(|plan| plan.result_local));
    compact_scope(&mut preview.proto.body, &preview.removed, &mut 0);
    for local in preserved {
        preview
            .proto
            .inline_dispositions
            .preserve_local(local, HirInlineRetentionReason::PhysicalFramePrefix);
    }
    *proto = preview.proto;
    true
}

/// 两类声明/依赖验证都返回首个无证候选的开始位置；统一截断一次，避免后段阻塞独立前缀。
fn validate_plan_batch(
    preview: &mut Preview,
    plans: &[Plan],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    is_chunk_entry: bool,
) -> Result<BTreeSet<LocalId>, usize> {
    let Preview { proto, removed } = preview;
    let candidates = plans
        .iter()
        .map(Plan::prefix_request)
        .collect::<BTreeMap<_, _>>();
    let preserved = prefix::validate_prefixes(
        proto,
        facts,
        dialect,
        is_chunk_entry,
        removed,
        &candidates,
        false,
    )?;
    let retained = plans
        .iter()
        .flat_map(|plan| {
            plan.retained_copies
                .iter()
                .map(move |&(index, target, source)| (index, (target, source, plan.start)))
        })
        .collect::<BTreeMap<_, _>>();
    let mut failed = 0;
    if !retained.is_empty() {
        visit_scope_mut(&mut proto.body, &mut 0, &mut |index, stmt| {
            let Some(&(target, source, owner)) = retained.get(&index) else {
                return Some(());
            };
            if removed[index]
                || !matches!(stmt, HirStmt::Assign(assign)
                if assign.targets.as_slice() == [HirLValue::Local(target)]
                    && assign.values.fixed.as_slice() == [HirExpr::LocalRef(source)]
                    && assign.values.tail.is_none())
            {
                failed = owner;
                return None;
            }
            Some(())
        })
        .ok_or(failed)?;
    }
    Ok(preserved)
}

#[expect(
    clippy::too_many_arguments,
    reason = "共享一个 proto 快照、全局语句坐标及调用帧约束，不为词法子块重建分析"
)]
fn collect_plans(
    proto: &HirProto,
    block: &HirBlock,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    barred: &BTreeSet<HomeSlotKey>,
    closed: &BTreeSet<HomeSlotKey>,
    constants_fit_rk: bool,
    stmt_count: &mut usize,
    plans: &mut Vec<Plan>,
) {
    let first_plan = plans.len();
    let mut flat = Vec::new();
    flatten_scope(block, stmt_count, &mut flat);
    let nested = tables::nested_producers(flat.iter().map(|entry| entry.map(|entry| entry.stmt)));
    let following_frame_floor = following_frame_floors(&flat, facts, dialect);
    // 后继 SETTABLE 直接读取的低槽表是已需存在的前缀身份。唯一 base 准备仍由
    // indexed 事务整体消费，不提前声明；这里仅为跨写表存活的索引结果提供锚点。
    let mut following_table_base = vec![None; flat.len()];
    let mut table_base = None;
    for (index, entry) in flat.iter().enumerate().rev() {
        following_table_base[index] = table_base;
        let Some(entry) = entry else {
            table_base = None;
            continue;
        };
        if scalar_local(entry.stmt).is_some() {
            continue;
        }
        table_base = match entry.stmt {
            HirStmt::Assign(assign) => match assign.targets.as_slice() {
                [HirLValue::TableAccess(access)] => match access.base {
                    HirExpr::LocalRef(local) => facts
                        .native_table_write_layout(access)
                        .filter(|layout| {
                            facts.trusted_local_home_slot(local) == Some(layout.base)
                                && layout
                                    .value
                                    .is_some_and(|value| layout.base.slot() < value.slot())
                        })
                        .map(|layout| (local, layout.base, access.as_ref())),
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        };
    }
    let mut start = 0;
    let mut lookup_attempt_start = None;
    let mut constructor_high = None::<usize>;
    for (index, entry) in flat.iter().enumerate() {
        if index < start {
            continue;
        }
        let Some(FlatStmt { id: stmt_id, stmt }) = *entry else {
            start = index + 1;
            constructor_high = None;
            continue;
        };
        if let HirStmt::GenericFor(for_) = stmt {
            let run = flat[start..index]
                .iter()
                .map(|entry| entry.as_ref().unwrap().stmt)
                .collect::<Vec<_>>();
            if let Some(mut plan) = generic_for_dispatch_plan(
                NativeFrameContext {
                    proto,
                    barred,
                    closed,
                    constants_fit_rk,
                },
                &run,
                facts,
                dialect,
                for_,
            ) {
                plan.removed = flat[start + plan.start..index]
                    .iter()
                    .map(|entry| entry.unwrap().id)
                    .collect();
                plan.start = *plan
                    .removed
                    .first()
                    .expect("dispatch frame consumes initializer");
                plan.sink = stmt_id;
                plans.push(plan);
                start = index + 1;
                constructor_high = None;
                continue;
            }
        }
        if matches!(stmt, HirStmt::If(_) | HirStmt::NumericFor(_)) {
            let run = flat[start..index]
                .iter()
                .map(|entry| entry.as_ref().unwrap().stmt)
                .collect::<Vec<_>>();
            let context = NativeFrameContext {
                proto,
                barred,
                closed,
                constants_fit_rk,
            };
            let candidate = match stmt {
                HirStmt::If(if_) => comparison_plan(context, &run, facts, dialect, &if_.cond),
                HirStmt::NumericFor(for_) => numeric_for_plan(context, &run, facts, dialect, for_),
                _ => unreachable!(),
            };
            if let Some(mut plan) = candidate {
                plan.removed = flat[start + plan.start..index]
                    .iter()
                    .map(|entry| entry.unwrap().id)
                    .collect();
                plan.start = *plan
                    .removed
                    .first()
                    .expect("header frame consumes a producer");
                plan.sink = stmt_id;
                plans.push(plan);
            }
            start = index + 1;
            constructor_high = None;
            continue;
        }
        if !matches!(dialect, DecompileDialect::Luajit | DecompileDialect::Luau)
            && index > start
            && lookup_attempt_start != Some(start)
            && let Some((target, value @ HirExpr::TableAccess(access))) = scalar_local(stmt)
            && let Some(home) = facts.trusted_local_home_slot(target)
            && !barred.contains(&home)
            && !closed.contains(&home)
            && [&access.base, &access.key].iter().any(|value| {
                matches!(value, HirExpr::LocalRef(local) if facts.trusted_local_home_slot(*local)
                    .is_some_and(|input| input.slot() >= home.slot()))
            })
            && (following_frame_floor[index]
                .original_calls
                .is_some_and(|floor| home.slot() < floor)
                || following_table_base[index].is_some_and(|(local, original, write)| {
                    (local, original) == (target, home)
                        && facts.table_write_base_preparation(write, value).is_none()
                }))
            && facts.table_read_result_home(access) == Some(home)
        {
            // 同一未闭合 run 只尝试一次，避免每个索引都重建增长中的定义索引。
            lookup_attempt_start = Some(start);
            let run = flat[start..index]
                .iter()
                .map(|entry| entry.unwrap().stmt)
                .collect::<Vec<_>>();
            let context = NativeFrameContext {
                proto,
                barred,
                closed,
                constants_fit_rk,
            };
            if let Some(mut plan) =
                lookup_initializer(context, &run, facts, dialect, target, access, home)
            {
                plan.removed = flat[start + plan.start..index]
                    .iter()
                    .map(|entry| entry.unwrap().id)
                    .collect();
                plan.start = plan.removed[0];
                plan.sink = stmt_id;
                plans.push(plan);
                start = index + 1;
                constructor_high = None;
                continue;
            }
        }
        if dialect == DecompileDialect::Luau
            && let Some(Some(previous)) = index.checked_sub(1).and_then(|i| flat.get(i))
            && let Some(mut plan) = scalar_array_lookup_plan(
                NativeFrameContext {
                    proto,
                    barred,
                    closed,
                    constants_fit_rk,
                },
                facts,
                previous.stmt,
                stmt,
                following_frame_floor[index].original_calls,
            )
        {
            plan.start = previous.id;
            plan.sink = stmt_id;
            plan.removed.push(previous.id);
            plans.push(plan);
            start = index + 1;
            constructor_high = None;
            continue;
        }
        if index > start
            && let Some(Some(previous)) =
                index.checked_sub(1).and_then(|previous| flat.get(previous))
            && let Some((call, width)) = batched_initializer(previous.stmt, stmt, facts)
        {
            // locals 的整组空声明只是待消费的初始化事务；按原 CALL 帧重发后，
            // 声明在 RHS 后生效，不能让额外 nil/永久前缀抬高调用准备区。
            let run = flat[start..index - 1]
                .iter()
                .map(|entry| entry.unwrap().stmt)
                .collect::<Vec<_>>();
            let frame = facts.native_call_frame(call).unwrap();
            let context = NativeFrameContext {
                proto,
                barred,
                closed,
                constants_fit_rk,
            };
            if let Some(mut builder) =
                frame_builder(context, &run, facts, dialect, frame.home.slot())
                && let Some(call) = builder.call(
                    call,
                    run.len(),
                    frame.home.slot(),
                    true,
                    CallWidth::Fixed(width),
                )
                && (builder.first_event.is_none() || builder.next_event == run.len())
            {
                let first = builder.first_event.unwrap_or(run.len());
                let assignment = multi_result_assignment(
                    proto, &flat, index, width, frame.home, facts, dialect, barred, closed,
                )
                .filter(|(end, _)| {
                    // 后继更高调用帧仍依赖这组声明占位，不能为较短赋值先撤销它。
                    // 同槽后继只选择候选；实际位置及后缀读写仍由完整事务签证。
                    following_frame_floor[*end].original_calls == Some(frame.home.slot())
                });
                let sink_index = assignment.as_ref().map_or(index, |(end, _)| *end);
                let removed = flat[start + first..sink_index]
                    .iter()
                    .map(|entry| entry.unwrap().id)
                    .collect::<Vec<_>>();
                plans.push(Plan {
                    start: removed[0],
                    sink: flat[sink_index].unwrap().id,
                    base: frame.home,
                    values: HirValuePack {
                        fixed: Vec::new(),
                        tail: Some(HirPackTail::exact(HirExpr::Call(Box::new(call)), width)),
                    },
                    result_local: None,
                    discarded_result: None,
                    assignment_targets: assignment.map_or_else(Vec::new, |(_, targets)| targets),
                    indexed_target: None,
                    retained_copies: Vec::new(),
                    removed,
                });
                start = sink_index + 1;
            } else {
                start = index + 1;
            }
            constructor_high = None;
            continue;
        }
        if let Some(Some(previous)) = index.checked_sub(1).and_then(|previous| flat.get(previous))
            && let Some(mut plan) = completed_table_assignment(
                proto,
                &[previous.stmt, stmt],
                facts,
                dialect,
                barred,
                closed,
                1,
            )
        {
            plan.start = previous.id;
            plan.sink = stmt_id;
            plan.removed.push(previous.id);
            plans.push(plan);
            start = index + 1;
            constructor_high = None;
            continue;
        }
        let indexed_sink = match stmt {
            HirStmt::Assign(assign)
                if indexed::is_candidate(assign)
                    && (matches!(assign.values.fixed.as_slice(), [HirExpr::Binary(_)])
                        || matches!(assign.values.fixed.as_slice(), [HirExpr::LocalRef(value)]
                            if index.checked_sub(1).and_then(|previous| flat.get(previous))
                                .and_then(Option::as_ref)
                                .and_then(|previous| scalar_local(previous.stmt))
                                .is_some_and(|(local, expr)| local == *value && matches!(expr, HirExpr::Binary(_))))) =>
            {
                Some((index, assign.as_ref()))
            }
            _ if matches!(scalar_local(stmt), Some((_, HirExpr::Binary(_)))) => flat
                .get(index + 1)
                .and_then(Option::as_ref)
                .and_then(|next| {
                    let HirStmt::Assign(assign) = next.stmt else {
                        return None;
                    };
                    (indexed::is_candidate(assign)
                        && matches!(assign.values.fixed.as_slice(), [HirExpr::LocalRef(value)]
                                if scalar_local(stmt).is_some_and(|(local, _)| local == *value)))
                    .then_some((index + 1, assign.as_ref()))
                }),
            _ => None,
        };
        if let Some((end, assign)) = indexed_sink
            && end > start
            // 未完成构造器的字段准备属于原构造事务，不在这里拆走其 CONCAT 或 key。
            && !nested.contains(&(end - 1))
        {
            let run = flat[start..end]
                .iter()
                .map(|entry| entry.unwrap().stmt)
                .collect::<Vec<_>>();
            if let Some(mut plan) = indexed::plan(
                NativeFrameContext {
                    proto,
                    barred,
                    closed,
                    constants_fit_rk,
                },
                &run,
                facts,
                dialect,
                assign,
            ) {
                plan.removed = flat[start + plan.start..end]
                    .iter()
                    .map(|entry| entry.unwrap().id)
                    .collect();
                plan.start = *plan
                    .removed
                    .first()
                    .expect("indexed frame consumes producers");
                plan.sink = flat[end].unwrap().id;
                plans.push(plan);
                start = end + 1;
                constructor_high = None;
                continue;
            }
            if end == index {
                start = index + 1;
                constructor_high = None;
                continue;
            }
            // 完整字段帧尚无证据时，原独立 CONCAT 初始化仍可尝试；不因候选出现停用旧能力。
        }
        if matches!(
            dialect,
            DecompileDialect::Lua51
                | DecompileDialect::Lua52
                | DecompileDialect::Lua53
                | DecompileDialect::Lua54
                | DecompileDialect::Lua55
                | DecompileDialect::Luau
        ) && index > start
            && let HirStmt::Assign(assign) = stmt
            && let ([target], [HirExpr::LocalRef(source)], None) = (
                assign.targets.as_slice(),
                assign.values.fixed.as_slice(),
                &assign.values.tail,
            )
            && let Some(Some(previous)) =
                index.checked_sub(1).and_then(|previous| flat.get(previous))
            && let Some((producer, HirExpr::Call(call))) = scalar_local(previous.stmt)
            && producer == *source
            && let Some(frame) = facts.native_call_frame(call)
            && facts.trusted_local_home_slot(*source) == Some(frame.home)
            && let Some(assignment_targets) = call_assignment_targets(
                target,
                frame.home,
                facts,
                dialect,
                constants_fit_rk,
                barred,
            )
            // 候选拒绝[LayerBoundary]：未结束构造器的字段 producer 仍属于整个构造/SETLIST 事务；先消费内层
            // CALL 会冻结外层 seed 的前缀，使原开放数组无法合并（regress_33）。
            && (!assignment_targets.is_empty() || !nested.contains(&(index - 1)))
        {
            // PUC/Luau 的活动低槽赋值在空闲区准备单结果调用，再 MOVE 回目标。把该 scratch
            // 留成独立 local 会让每次重编译再开一槽；完整事务保留目标与两次原写。
            let run = flat[start..index]
                .iter()
                .map(|entry| entry.unwrap().stmt)
                .collect::<Vec<_>>();
            let context = NativeFrameContext {
                proto,
                barred,
                closed,
                constants_fit_rk,
            };
            let (move_homes, retained_copies) = retained_result_copies(&flat, index, call, facts)
                .unwrap_or_else(|| {
                    (
                        assignment_targets
                            .iter()
                            .filter_map(|target| facts.trusted_local_home_slot(*target))
                            .collect(),
                        Vec::new(),
                    )
                });
            if let Some(mut builder) =
                frame_builder(context, &run, facts, dialect, frame.home.slot()).map(
                    |mut builder| {
                        builder.result_move = Some((*source, run.len() - 1, move_homes));
                        builder
                    },
                )
                && let Some(value) = builder.expr(
                    &HirExpr::LocalRef(*source),
                    run.len(),
                    frame.home.slot(),
                    None,
                    false,
                    true,
                    None,
                )
                && let Some(first) = builder.first_event
                && builder.next_event == run.len()
            {
                let removed = flat[start + first..index]
                    .iter()
                    .map(|entry| entry.unwrap().id)
                    .collect::<Vec<_>>();
                plans.push(Plan {
                    start: removed[0],
                    sink: stmt_id,
                    base: frame.home,
                    values: vec![value].into(),
                    result_local: None,
                    discarded_result: None,
                    assignment_targets,
                    indexed_target: None,
                    retained_copies,
                    removed,
                });
            }
            start = index + 1;
            constructor_high = None;
            continue;
        }
        if let HirStmt::Return(ret) = stmt
            && !ret.values.fixed.is_empty()
        {
            let run = flat[start..index]
                .iter()
                .map(|entry| entry.as_ref().unwrap().stmt)
                .collect::<Vec<_>>();
            if let Some(mut plan) = return_plan(
                NativeFrameContext {
                    proto,
                    barred,
                    closed,
                    constants_fit_rk,
                },
                &run,
                facts,
                dialect,
                ret,
            ) {
                plan.removed = flat[start + plan.start..index]
                    .iter()
                    .map(|entry| entry.unwrap().id)
                    .collect();
                plan.start = *plan
                    .removed
                    .first()
                    .expect("return frame consumes a producer");
                plan.sink = stmt_id;
                plans.push(plan);
            }
            start = index + 1;
            constructor_high = None;
            continue;
        }
        if let Some((local, HirExpr::TableConstructor(_))) = scalar_local(stmt)
            && let Some(home) = facts.trusted_local_home_slot(local)
        {
            constructor_high =
                Some(constructor_high.map_or(home.slot(), |old| old.max(home.slot())));
        }
        let initializer =
            dialect == DecompileDialect::Luau && source_call_initializer(proto, stmt, facts)
                || fastcall_copy_initializer(
                    stmt,
                    flat.get(index + 1)
                        .and_then(Option::as_ref)
                        .map(|next| next.stmt),
                    facts,
                    following_frame_floor[index].all,
                    nested.contains(&index),
                )
                || (constructor_high.is_some()
                    && !nested.contains(&index)
                    && scalar_local(stmt).is_some_and(|(_, value)| {
                        let HirExpr::Call(call) = value else {
                            return false;
                        };
                        facts
                            .native_call_frame(call)
                            .or_else(|| facts.native_fastcall_frame(call))
                            .is_some_and(|frame| {
                                // 已完成的低槽对象不是当前 CALL 的构造器参数。否则 obj 后的
                                // :add():add() 会被逐个提前提交并冻结中间声明，阻止外层帧整体恢复。
                                constructor_high.is_some_and(|high| high >= frame.home.slot())
                            })
                    }))
                || scalar_local(stmt).is_some_and(|(target, value)| {
                    let HirExpr::Call(call) = value else {
                        return false;
                    };
                    let Some(frame) = facts
                        .native_call_frame(call)
                        .or_else(|| facts.native_fastcall_frame(call))
                    else {
                        return false;
                    };
                    if flat.get(index + 1).and_then(Option::as_ref).is_some_and(|next|
                        matches!(scalar_local(next.stmt), Some((copy, HirExpr::LocalRef(source)))
                            if *source == target && facts.trusted_local_home_slot(copy)
                                .is_none_or(|home| home.slot() <= frame.home.slot()))) {
                        return false;
                    }
                    following_frame_floor[index]
                        .all
                        .is_some_and(|floor| frame.home.slot() < floor)
                });
        let concat_initializer = scalar_local(stmt).and_then(|(local, value)| {
            let HirExpr::Binary(binary) = value else {
                return None;
            };
            if matches!(dialect, DecompileDialect::Luajit | DecompileDialect::Luau)
                || binary.op != crate::hir::common::HirBinaryOpKind::Concat
            {
                return None;
            }
            let home = facts.operation_result_home(binary.source_site?)?;
            (facts.trusted_local_home_slot(local) == Some(home)
                && following_frame_floor[index]
                    .all
                    .is_none_or(|floor| home.slot() < floor))
            .then_some((local, binary, home))
        });
        let discarded_result = (|| {
            let HirStmt::LocalDecl(decl) = stmt else {
                return None;
            };
            let ([local], [HirExpr::Call(call)], None) = (
                decl.bindings.as_slice(),
                decl.values.fixed.as_slice(),
                &decl.values.tail,
            ) else {
                return None;
            };
            let next = flat.get(index + 1)?.as_ref()?.stmt;
            let (target, value) = scalar_local(next)?;
            if target != *local
                || !matches!(next, HirStmt::Assign(_))
                || !matches!(
                    value,
                    HirExpr::Nil | HirExpr::Boolean(_) | HirExpr::Integer(_) | HirExpr::Number(_)
                )
                || proto
                    .local_debug_hints
                    .get(local.index())
                    .is_some_and(Option::is_some)
                || proto
                    .local_debug_scopes
                    .get(local.index())
                    .is_some_and(Option::is_some)
                || matches!(proto.inline_dispositions.local(*local), crate::hir::common::HirInlineDisposition::Preserve(reasons)
                    if reasons.iter().any(|reason| *reason != HirInlineRetentionReason::PhysicalFramePrefix))
            {
                return None;
            }
            let frame = facts.native_call_frame(call)?;
            (facts.trusted_local_home_slot(*local) == Some(frame.home)
                && frame.results
                    == Some(ResultPack::Fixed(crate::transformer::RegRange {
                        start: crate::transformer::Reg(frame.home.slot()),
                        len: 1,
                    }))
                && !closed.contains(&frame.home)
                && !barred.contains(&frame.home))
            .then_some((*local, call, frame.home))
        })();
        if let Some((local, call, home)) = discarded_result {
            let run = flat[start..index]
                .iter()
                .map(|entry| entry.unwrap().stmt)
                .collect::<Vec<_>>();
            let context = NativeFrameContext {
                proto,
                barred,
                closed,
                constants_fit_rk,
            };
            if let Some(mut builder) = frame_builder(context, &run, facts, dialect, home.slot())
                && let Some(call) =
                    builder.call(call, run.len(), home.slot(), true, CallWidth::Single)
                && (builder.first_event.is_none() || builder.next_event == run.len())
            {
                let first = builder.first_event.unwrap_or(run.len());
                let removed = flat[start + first..index]
                    .iter()
                    .map(|entry| entry.unwrap().id)
                    .collect::<Vec<_>>();
                plans.push(Plan {
                    start: removed.first().copied().unwrap_or(stmt_id),
                    sink: stmt_id,
                    base: home,
                    values: vec![HirExpr::Call(Box::new(call))].into(),
                    result_local: None,
                    discarded_result: Some(local),
                    assignment_targets: Vec::new(),
                    indexed_target: None,
                    retained_copies: Vec::new(),
                    removed,
                });
            }
            start = index + 1;
            constructor_high = None;
            continue;
        }
        let sink = match stmt {
            HirStmt::GenericFor(for_) if for_.iterator.fixed.is_empty() => {
                for_.iterator.tail.as_ref().and_then(|tail| {
                    let HirExpr::Call(call) = tail.as_expr() else {
                        return None;
                    };
                    let frame = facts.generic_for_body_frame(for_)?;
                    if tail
                        .exact_width()
                        .is_some_and(|width| width != frame.iterator_width)
                        || facts.native_call_layout(call)?.home != *frame.controls.first()?
                    {
                        return None;
                    }
                    Some((call.as_ref(), CallWidth::Fixed(frame.iterator_width)))
                })
            }
            HirStmt::CallStmt(sink) => Some((&sink.call, CallWidth::Ignore)),
            HirStmt::Return(ret) if ret.values.fixed.is_empty() => {
                ret.values.tail.as_ref().and_then(|tail| {
                    if tail.exact_width().is_some() {
                        return None;
                    }
                    let HirExpr::Call(call) = tail.as_expr() else {
                        return None;
                    };
                    Some((call.as_ref(), CallWidth::Tail))
                })
            }
            _ if initializer => scalar_local(stmt).and_then(|(target, value)| {
                let HirExpr::Call(call) = value else {
                    return None;
                };
                let frame = facts
                    .native_call_frame(call)
                    .or_else(|| facts.native_fastcall_frame(call))?;
                (facts.trusted_local_home_slot(target) == Some(frame.home))
                    .then_some((call.as_ref(), CallWidth::Single))
            }),
            _ => None,
        };
        if sink.is_some() || concat_initializer.is_some() {
            // 无条件 scope 入口没有求值；只借用当前连续语句，出口 marker 切断 run。
            let stmts = flat[start..=index]
                .iter()
                .map(|entry| entry.as_ref().unwrap().stmt)
                .collect::<Vec<_>>();
            let context = NativeFrameContext {
                proto,
                barred,
                closed,
                constants_fit_rk,
            };
            let candidate = match sink {
                Some((call, width)) => plan(
                    context,
                    &stmts,
                    facts,
                    dialect,
                    stmts.len() - 1,
                    call,
                    width,
                ),
                None => concat_initializer.and_then(|(local, binary, home)| {
                    let run = &stmts[..stmts.len() - 1];
                    let mut builder = frame_builder(context, run, facts, dialect, home.slot())?;
                    let value = builder.concat(binary, run.len(), home.slot())?;
                    let start = builder.first_event?;
                    (builder.next_event == run.len()).then_some(Plan {
                        start,
                        sink: run.len(),
                        base: home,
                        values: vec![value].into(),
                        result_local: Some(local),
                        discarded_result: None,
                        assignment_targets: Vec::new(),
                        indexed_target: None,
                        retained_copies: Vec::new(),
                        removed: Vec::new(),
                    })
                }),
            };
            if let Some(mut plan) = candidate {
                plan.removed = flat[start + plan.start..index]
                    .iter()
                    .map(|entry| entry.as_ref().unwrap().id)
                    .collect();
                plan.start = *plan
                    .removed
                    .first()
                    .expect("accepted frame consumes a producer");
                plan.sink = stmt_id;
                plans.push(plan);
            }
        }
        let constructor_step =
            !matches!(dialect, DecompileDialect::Luajit | DecompileDialect::Luau)
                && (super::super::table_constructors::constructor_write(stmt).is_some()
                    || matches!(stmt, HirStmt::LocalRootRelease(_)));
        let pending_initializer = matches!(stmt, HirStmt::LocalDecl(decl)
            if decl.values.is_empty() && decl.initializer_merge_transaction.is_some())
            || matches!(stmt, HirStmt::Assign(assign) if assign.generic_for_initializer_producer.is_some());
        if initializer
            || concat_initializer.is_some()
            || (scalar_binding(stmt).is_none() && !constructor_step && !pending_initializer)
        {
            // 含表的完整 initializer 每段最多尝试一次；拒绝的表也不能作为后续调用树
            // 的中间 producer。普通无表嵌套调用仍沿现有单次 CallStmt 扫描。
            start = index + 1;
            constructor_high = None;
        }
    }
    // 构造器事务可能已消费最初的值，却为后继原槽写留下 empty LocalDecl。
    // 紧邻的一组空声明及其首写被本批完整帧消费时，声明必须同批退休；
    // 整体 preview 仍逐身份拒绝任何在重写前的 read/capture，不能靠空声明掩盖缺失值。
    // 真实 LOADNIL 仍有独立写入义务，不从空声明外形推断可以删除。
    let original_nil_locals = facts
        .nil_write_groups()
        .flat_map(|group| {
            group
                .iter()
                .filter_map(|temp| facts.promoted_local_for_temp(*temp))
        })
        .collect::<BTreeSet<_>>();
    let mut empty_declarations = BTreeMap::new();
    let mut pending = Vec::new();
    let mut first_local = None;
    for entry in &flat {
        let Some(entry) = entry else {
            pending.clear();
            first_local = None;
            continue;
        };
        if let HirStmt::LocalDecl(decl) = entry.stmt
            && removable_empty_declaration(proto, &original_nil_locals, decl)
        {
            first_local.get_or_insert(decl.bindings[0]);
            pending.push(entry.id);
            continue;
        }
        if let Some(local) = first_local.take()
            && scalar_local(entry.stmt).is_some_and(|(written, _)| written == local)
        {
            empty_declarations.insert(entry.id, (std::mem::take(&mut pending), local));
        }
        pending.clear();
    }
    for plan in &mut plans[first_plan..] {
        if let Some((declarations, local)) = empty_declarations.remove(&plan.start)
            && plan.removed.first() == Some(&plan.start)
            && facts.trusted_local_home_slot(local) == Some(plan.base)
        {
            plan.start = declarations[0];
            plan.removed.splice(0..0, declarations);
        }
    }
}
/// initializer CALL 与 dispatch root endpoints 属于同一循环头事务。
/// marker 只提供原配对；完整 CALL、控制槽、成功结果槽及最终声明前缀仍分别核对。
fn generic_for_dispatch_plan(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    for_: &crate::hir::common::HirGenericFor,
) -> Option<Plan> {
    let frame = facts.generic_for_body_frame(for_)?;
    let dispatch = for_.body_frame_source?;
    if frame.controls.len() != frame.iterator_width {
        return None;
    }
    let base = *frame.controls.first()?;
    let results = for_
        .dispatch_results
        .iter()
        .zip(&frame.bindings)
        .map(|(result, home)| (result.result_def, *home))
        .collect::<BTreeMap<_, _>>();
    let mut seen_results = BTreeSet::new();
    let mut release_start = run.len();
    while let Some(HirStmt::Assign(assign)) = release_start.checked_sub(1).map(|index| run[index]) {
        let Some(release) = assign.generic_for_dispatch_release else {
            break;
        };
        let home = *results.get(&release.result_def)?;
        let target_matches = match assign.targets.as_slice() {
            [HirLValue::Temp(temp)] => *temp == release.released,
            [HirLValue::Local(local)] => {
                facts.promoted_local_for_temp(release.released) == Some(*local)
                    && facts.trusted_local_home_slot(*local) == Some(home)
            }
            _ => false,
        };
        if release.dispatch != dispatch
            || !target_matches
            || facts.trusted_temp_home_slot(release.released) != Some(home)
            || assign.values.fixed.as_slice() != [HirExpr::Nil]
            || assign.values.tail.is_some()
            || context.barred.contains(&home)
            || context.closed.contains(&home)
            || !seen_results.insert(release.result_def)
        {
            return None;
        }
        release_start -= 1;
    }
    if seen_results.is_empty() {
        return None;
    }
    let initializer = release_start.checked_sub(1)?;
    let HirStmt::Assign(assign) = run[initializer] else {
        return None;
    };
    let call = super::super::generic_for_iterators::single_call_initializer(assign, for_)?;
    if assign
        .targets
        .iter()
        .zip(&frame.controls)
        .any(|(target, home)| {
            let HirLValue::Temp(temp) = target else {
                return true;
            };
            facts.trusted_temp_home_slot(*temp) != Some(*home)
                || context
                    .proto
                    .temp_debug_locals
                    .get(temp.index())
                    .is_some_and(Option::is_some)
                || context.barred.contains(home)
                || context.closed.contains(home)
        })
    {
        return None;
    }
    let prefix_run = &run[..initializer];
    let mut builder = frame_builder(context, prefix_run, facts, dialect, base.slot())?;
    let call = builder.call(
        call,
        prefix_run.len(),
        base.slot(),
        true,
        CallWidth::Fixed(frame.iterator_width),
    )?;
    if builder.first_event.is_some() && builder.next_event != prefix_run.len() {
        return None;
    }
    Some(Plan {
        start: builder.first_event.unwrap_or(initializer),
        sink: run.len(),
        base,
        values: HirValuePack {
            fixed: Vec::new(),
            tail: Some(HirPackTail::open(HirExpr::Call(Box::new(call)))),
        },
        result_local: None,
        discarded_result: None,
        assignment_targets: Vec::new(),
        indexed_target: None,
        retained_copies: Vec::new(),
        removed: Vec::new(),
    })
}

fn batched_initializer<'a>(
    previous: &HirStmt,
    stmt: &'a HirStmt,
    facts: &ProtoPromotionFacts,
) -> Option<(&'a HirCallExpr, usize)> {
    let (HirStmt::LocalDecl(decl), HirStmt::Assign(assign)) = (previous, stmt) else {
        return None;
    };
    let token = decl.initializer_merge_transaction?;
    if assign.initializer_merge_transaction != Some(token)
        || !decl.values.is_empty()
        || decl.bindings.len() < 2
        || decl.bindings.len() != assign.targets.len()
        || !assign.values.fixed.is_empty()
    {
        return None;
    }
    let tail = assign.values.tail.as_ref()?;
    let HirExpr::Call(call) = tail.as_expr() else {
        return None;
    };
    let frame = facts.native_call_frame(call)?;
    let width = decl.bindings.len();
    if tail.exact_width() != Some(width)
        || frame.results
            != Some(ResultPack::Fixed(crate::transformer::RegRange {
                start: crate::transformer::Reg(frame.home.slot()),
                len: width,
            }))
        || !decl
            .bindings
            .iter()
            .zip(&assign.targets)
            .enumerate()
            .all(|(index, (local, target))| {
                matches!(target, HirLValue::Local(target) if target == local)
                    && facts.trusted_local_home_slot(*local)
                        == Some(HomeSlotKey::new(frame.home.slot() + index, 0))
            })
    {
        return None;
    }
    Some((call, width))
}

/// 低槽 Local 写与低槽表字段写共用单结果 CALL 帧。字段目标在源码 RHS 前求值，
/// 因此仅接受未捕获的直接低槽 base 和原内嵌 key，不能提前快照可被 CALL 改写的 base。
fn call_assignment_targets(
    target: &HirLValue,
    result: HomeSlotKey,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    constants_fit_rk: bool,
    barred: &BTreeSet<HomeSlotKey>,
) -> Option<Vec<LocalId>> {
    match target {
        HirLValue::Local(local) => facts
            .trusted_local_home_slot(*local)
            .filter(|home| home.slot() < result.slot())
            .map(|_| vec![*local]),
        HirLValue::TableAccess(access)
            if constants_fit_rk
                && !matches!(dialect, DecompileDialect::Luau | DecompileDialect::Luajit) =>
        {
            let layout = facts.native_table_write_layout(access)?;
            let base = match &access.base {
                HirExpr::LocalRef(local) => facts.trusted_local_home_slot(*local),
                HirExpr::ParamRef(param) => facts.trusted_param_home_slot(*param),
                _ => None,
            }?;
            (base == layout.base
                && base.slot() < result.slot()
                && !barred.contains(&base)
                && layout.key.is_none()
                && layout.value == Some(result)
                && matches!(
                    access.key,
                    HirExpr::String(_) | HirExpr::Integer(_) | HirExpr::Number(_)
                ))
            .then(Vec::new)
        }
        _ => None,
    }
}

/// PUC 多结果赋值先在空闲区返回，再从末项向首项写入现存低槽。消费的是这次
/// 返回值版本；同 Local 的后续独立写仍由 apply_preview 的 missing 事务重声明。
#[expect(
    clippy::too_many_arguments,
    reason = "复用当前批次的原槽、身份和词法快照"
)]
fn multi_result_assignment(
    proto: &HirProto,
    flat: &[Option<FlatStmt<'_>>],
    initializer: usize,
    width: usize,
    base: HomeSlotKey,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    barred: &BTreeSet<HomeSlotKey>,
    closed: &BTreeSet<HomeSlotKey>,
) -> Option<(usize, Vec<LocalId>)> {
    if matches!(dialect, DecompileDialect::Luau | DecompileDialect::Luajit) {
        return None;
    }
    let HirStmt::Assign(assign) = flat[initializer]?.stmt else {
        return None;
    };
    let end = initializer + width;
    let copies = flat.get(initializer + 1..=end)?;
    let mut targets = Vec::with_capacity(width);
    let mut unique = BTreeSet::new();
    for (offset, (source, entry)) in assign.targets.iter().rev().zip(copies).enumerate() {
        let HirLValue::Local(source) = source else {
            return None;
        };
        let entry = (*entry)?;
        if entry.id != flat[initializer]?.id + offset + 1 {
            return None;
        }
        let HirStmt::Assign(copy) = entry.stmt else {
            return None;
        };
        let ([HirLValue::Local(target)], [HirExpr::LocalRef(read)], None) = (
            copy.targets.as_slice(),
            copy.values.fixed.as_slice(),
            &copy.values.tail,
        ) else {
            return None;
        };
        let home = facts.trusted_local_home_slot(*source)?;
        let target_home = facts.trusted_local_home_slot(*target)?;
        let writes = facts.complete_local_definition_write_homes(*source);
        if source != read
            || home.slot() != base.slot() + width - offset - 1
            || target_home.slot() >= base.slot()
            || !unique.insert(*target)
            || proto.local_debug_hints[source.index()].is_some()
            || proto.local_debug_scopes[source.index()].is_some()
            || proto.inline_dispositions.local(*source).must_preserve()
            || !writes.is_disjoint(barred)
            || !writes.is_disjoint(closed)
            || writes
                .iter()
                .any(|write| *write != home && *write != target_home)
        {
            return None;
        }
        targets.push(*target);
    }
    targets.reverse();
    Some((end, targets))
}

#[derive(Clone, Copy)]
struct FlatStmt<'a> {
    id: usize,
    stmt: &'a HirStmt,
}

/// 单次逆序归并后续原求值帧的最低槽：结果低于整个后续帧时才独立恢复初始化。
/// 不能提前冻结 `print(make(), other())` 的高槽 make 结果，否则会抬高 print 的 caller top。
/// CONCAT/RETURN 同样拥有准备区，不能先把其中的 CALL 结果固化为永久声明。
#[derive(Clone, Copy, Default)]
struct FollowingFrameFloor {
    all: Option<usize>,
    original_calls: Option<usize>,
}

fn following_frame_floors(
    flat: &[Option<FlatStmt<'_>>],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
) -> Vec<FollowingFrameFloor> {
    use crate::hir::visit::HirVisitor;
    struct Calls<'a> {
        facts: &'a ProtoPromotionFacts,
        floor: FollowingFrameFloor,
    }
    impl HirVisitor<'_> for Calls<'_> {
        fn visit_expr(&mut self, expr: &HirExpr) {
            if let HirExpr::Binary(binary) = expr
                && binary.op == crate::hir::common::HirBinaryOpKind::Concat
                && let Some(buffer) = self.facts.native_concat_buffer(binary)
            {
                let slot = buffer.start.index();
                self.floor.all = Some(self.floor.all.map_or(slot, |old| old.min(slot)));
            }
        }

        fn visit_stmt(&mut self, stmt: &HirStmt) {
            if let HirStmt::Return(ret) = stmt
                && let Some(frame) = self.facts.native_return_frame(ret)
            {
                let slot = frame.home.slot();
                self.floor.all = Some(self.floor.all.map_or(slot, |old| old.min(slot)));
            }
        }

        fn visit_call(&mut self, call: &HirCallExpr) {
            let slot = self
                .facts
                .native_call_layout(call)
                .map_or(0, |frame| frame.home.slot());
            self.floor.all = Some(self.floor.all.map_or(slot, |old| old.min(slot)));
            // 合成 factory 调用没有原 CALL 参数区；不据它猜原 buffer 布局。
            // 有原来源但缺布局的调用仍以零下界阻断独立原 initializer 恢复。
            if call.source_site.is_some() {
                self.floor.original_calls =
                    Some(self.floor.original_calls.map_or(slot, |old| old.min(slot)));
            }
        }
    }
    let mut result = vec![FollowingFrameFloor::default(); flat.len()];
    let mut calls = Calls {
        facts,
        floor: FollowingFrameFloor::default(),
    };
    for (index, entry) in flat.iter().enumerate().rev() {
        let Some(entry) = entry else {
            calls.floor = FollowingFrameFloor::default();
            continue;
        };
        result[index] = calls.floor;
        if let HirStmt::NumericFor(for_) = entry.stmt
            && let Some(base) = numeric_header_base(for_, dialect)
        {
            // 三个 header 值属于同一个准备区，不能先把较低槽 CALL 固定为源码 local。
            calls.floor = FollowingFrameFloor {
                all: Some(base.slot()),
                original_calls: Some(base.slot()),
            };
            continue;
        }
        if scalar_local(entry.stmt).is_none() {
            calls.floor = FollowingFrameFloor::default();
            if !matches!(entry.stmt, HirStmt::CallStmt(_) | HirStmt::Return(_)) {
                continue;
            }
        }
        crate::hir::visit::visit_stmt_header(entry.stmt, &mut calls);
    }
    result
}

fn flatten_scope<'a>(
    block: &'a HirBlock,
    cursor: &mut usize,
    output: &mut Vec<Option<FlatStmt<'a>>>,
) {
    for stmt in &block.stmts {
        let id = *cursor;
        *cursor += 1;
        if let HirStmt::Block(child) = stmt {
            flatten_scope(child, cursor, output);
            output.push(None);
        } else if let HirStmt::NumericFor(for_) = stmt {
            output.push(Some(FlatStmt { id, stmt }));
            output.push(None);
            flatten_scope(&for_.body, cursor, output);
            output.push(None);
        } else if let HirStmt::While(while_) = stmt {
            // 条件每轮求值；循环体的完整帧不能消费循环外或条件的准备。
            output.push(None);
            output.push(Some(FlatStmt { id, stmt }));
            output.push(None);
            flatten_scope(&while_.body, cursor, output);
            output.push(None);
        } else if let HirStmt::GenericFor(for_) = stmt {
            output.push(Some(FlatStmt { id, stmt }));
            flatten_scope(&for_.body, cursor, output);
            output.push(None);
        } else if let HirStmt::If(if_) = stmt {
            output.push(Some(FlatStmt { id, stmt }));
            flatten_scope(&if_.then_block, cursor, output);
            output.push(None);
            if let Some(else_block) = &if_.else_block {
                flatten_scope(else_block, cursor, output);
                output.push(None);
            }
        } else {
            output.push(Some(FlatStmt { id, stmt }));
        }
    }
}

fn numeric_header_base(
    for_: &crate::hir::common::HirNumericFor,
    dialect: DecompileDialect,
) -> Option<HomeSlotKey> {
    // Luau 的物理顺序是 limit/step/index，求值顺序仍为 start/limit/step。
    // JIT 的 FR2 帧隙由 FrameBuilder.call 消费，不改变三个控制值的槽序。
    let order = if dialect == DecompileDialect::Luau {
        [2, 0, 1]
    } else {
        [0, 1, 2]
    };
    let base = for_.control_homes[usize::from(dialect == DecompileDialect::Luau)];
    for_.control_homes
        .iter()
        .enumerate()
        .all(|(offset, home)| *home == HomeSlotKey::new(base.slot() + order[offset], 0))
        .then_some(base)
}

/// 比较头的两个准备按原 Def、原槽与事件顺序共同消费；CALL 结果仍作为原 scratch
/// 存活，不以“只读于条件”撤销根义务。后续声明身份与源码前缀由同批事务核对。
fn comparison_plan(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    condition: &HirExpr,
) -> Option<Plan> {
    if matches!(dialect, DecompileDialect::Luajit | DecompileDialect::Luau) {
        return None;
    }
    let mut operand = condition;
    let mut not_depth = 0;
    while let HirExpr::Unary(unary) = operand
        && unary.op == crate::hir::common::HirUnaryOpKind::Not
    {
        operand = &unary.expr;
        not_depth += 1;
    }
    let HirExpr::Binary(binary) = operand else {
        return None;
    };
    let prepared = facts.comparison_preparation_inputs(binary);
    let (lhs_producer, rhs_producer, base) = if let Some(prepared) = prepared {
        prepared
    } else {
        use crate::hir::common::HirBinaryOpKind;
        if !matches!(
            binary.op,
            HirBinaryOpKind::Eq
                | HirBinaryOpKind::Lt
                | HirBinaryOpKind::Le
                | HirBinaryOpKind::Gt
                | HirBinaryOpKind::Ge
        ) {
            return None;
        }
        let (HirExpr::Call(lhs), HirExpr::Call(rhs)) = (&binary.lhs, &binary.rhs) else {
            return None;
        };
        let lhs_frame = facts.native_call_layout(lhs)?;
        let rhs_frame = facts.native_call_layout(rhs)?;
        let layout = facts.native_binary_layout(binary)?;
        if layout.lhs != Some(lhs_frame.home)
            || layout.rhs != Some(rhs_frame.home)
            || rhs_frame.home.slot() != lhs_frame.home.slot() + 1
        {
            return None;
        }
        // 两侧 CALL 各自重发原帧。左侧 SELF receiver 的双用途 carrier 由共享
        // method builder 消费；不能把 receiver 声明塞进无读取的 nil run。
        (
            facts.operation_result_temp(lhs.source_site?)?,
            facts.operation_result_temp(rhs.source_site?)?,
            lhs_frame.home,
        )
    };
    let mut builder = frame_builder(context, run, facts, dialect, base.slot())?;
    let lhs = builder.expr(
        &binary.lhs,
        run.len(),
        base.slot(),
        None,
        true,
        false,
        Some(lhs_producer),
    )?;
    let rhs = builder.expr(
        &binary.rhs,
        run.len(),
        base.slot() + 1,
        None,
        true,
        false,
        Some(rhs_producer),
    )?;
    let start = builder.first_event?;
    if builder.next_event != run.len() {
        return None;
    }
    let rebuilt = crate::hir::common::HirBinaryExpr {
        source_site: binary.source_site,
        op: binary.op,
        lhs,
        rhs,
    };
    if prepared.is_some() && facts.comparison_preparation_frame(&rebuilt) != Some(base) {
        return None;
    }
    let mut condition = condition.clone();
    let mut operand = &mut condition;
    for _ in 0..not_depth {
        let HirExpr::Unary(unary) = operand else {
            unreachable!()
        };
        operand = &mut unary.expr;
    }
    *operand = HirExpr::Binary(Box::new(rebuilt));
    Some(Plan {
        start,
        sink: run.len(),
        base,
        values: vec![condition].into(),
        result_local: None,
        discarded_result: None,
        assignment_targets: Vec::new(),
        indexed_target: None,
        retained_copies: Vec::new(),
        removed: Vec::new(),
    })
}

/// 三个 header 控制值按原事件顺序共同消费，不能独立缩短某个 CALL 结果的根区间。
fn numeric_for_plan(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    for_: &crate::hir::common::HirNumericFor,
) -> Option<Plan> {
    let base = numeric_header_base(for_, dialect)?;
    if ![&for_.start, &for_.limit, &for_.step]
        .iter()
        .any(|value| match value {
            HirExpr::TempRef(_) => true,
            HirExpr::LocalRef(local) => facts
                .trusted_local_home_slot(*local)
                .is_some_and(|home| home.slot() >= base.slot()),
            _ => false,
        })
    {
        // 整个控制值已是表达式时没有 header carrier 可收回；嵌入调用的 receiver/field
        // alias 留给已有 method owner，否则新前缀保留会截断其首事件证明（407）。
        return None;
    }
    let mut builder = frame_builder(context, run, facts, dialect, base.slot())?;
    let luau_top = if dialect == DecompileDialect::Luau {
        Some(facts.numeric_for_body_frame(for_)?.binding.slot() + 1)
    } else {
        None
    };
    let mut values = Vec::with_capacity(3);
    for (offset, value) in [&for_.start, &for_.limit, &for_.step]
        .into_iter()
        .enumerate()
    {
        values.push(if let Some(top) = luau_top {
            luau_numeric_control(
                &mut builder,
                value,
                for_.control_homes[offset],
                for_.control_values[offset],
                top,
            )?
        } else {
            builder.expr(
                value,
                run.len(),
                base.slot() + offset,
                None,
                false,
                true,
                for_.control_values[offset],
            )?
        });
    }
    let start = builder.first_event?;
    if builder.next_event != run.len() {
        return None;
    }
    Some(Plan {
        start,
        sink: run.len(),
        base,
        values: values.into(),
        result_local: None,
        discarded_result: None,
        assignment_targets: Vec::new(),
        indexed_target: None,
        retained_copies: Vec::new(),
        removed: Vec::new(),
    })
}

/// compileStatFor 先预留控制区与可写 index，再以 compileExprTemp 求三个值。
/// 只有 top-1 目标上的 CALL 原位返回，其余 CALL 在 top 返回并紧邻 MOVE 到控制槽。
/// 控制 COPY 在循环语法中重发，不使用“后缀仍保留 COPY”的另一种证书。
fn luau_numeric_control(
    builder: &mut FrameBuilder<'_>,
    value: &HirExpr,
    target: HomeSlotKey,
    original: Option<TempId>,
    top: usize,
) -> Option<HirExpr> {
    let definition = match value {
        HirExpr::TempRef(temp) => Some((
            HirBinding::Temp(*temp),
            *builder.temp_definitions.get(temp)?,
        )),
        HirExpr::LocalRef(local)
            if builder.facts.trusted_local_home_slot(*local)?.slot() >= builder.base =>
        {
            Some((
                HirBinding::Local(*local),
                builder.definition(*local, builder.run.len())?,
            ))
        }
        _ => None,
    };
    let expression = if let Some((_, index)) = definition {
        scalar_binding(builder.run[index])?.1
    } else {
        value
    };
    let HirExpr::Call(call) = expression else {
        return builder.expr(
            value,
            builder.run.len(),
            target.slot(),
            None,
            false,
            true,
            original,
        );
    };
    let facts = builder.facts;
    let frame = facts.native_call_frame(call)?;
    let producer = facts.operation_result_temp(call.source_site?)?;
    let original = original?;
    let slot = if target.slot() + 1 == top {
        target.slot()
    } else {
        top
    };
    if frame.home != HomeSlotKey::new(slot, 0)
        || facts.trusted_temp_home_slot(original) != Some(target)
        || facts
            .complete_temp_non_move_write_homes(producer)
            .iter()
            .any(|home| *home != frame.home)
    {
        return None;
    }
    let moves = facts.trusted_immediate_moves(producer)?;
    if target == frame.home {
        if original != producer || !moves.is_empty() {
            return None;
        }
    } else if !matches!(moves, [copy] if copy.source == Some(producer)
        && copy.source_home == frame.home && copy.target == original && copy.target_home == target)
    {
        return None;
    }
    if facts
        .complete_temp_definition_write_homes(producer)
        .iter()
        .any(|home| *home != frame.home && *home != target)
    {
        return None;
    }
    let before = if let Some((binding, index)) = definition {
        if index < builder.next_event {
            return None;
        }
        let context = builder.native?;
        match binding {
            HirBinding::Temp(temp) => {
                if (temp != producer && temp != original)
                    || context.proto.inline_dispositions.temp(temp).must_preserve()
                {
                    return None;
                }
            }
            HirBinding::Local(local) => {
                if (facts.promoted_local_for_temp(producer) != Some(local)
                    && facts.promoted_local_for_temp(original) != Some(local))
                    || context.proto.local_debug_scopes[local.index()].is_some()
                    || context.proto.local_debug_hints[local.index()].is_some()
                    || context
                        .proto
                        .inline_dispositions
                        .local(local)
                        .must_preserve()
                {
                    return None;
                }
            }
            _ => return None,
        }
        if context.closed.contains(&target) || context.closed.contains(&frame.home) {
            return None;
        }
        index
    } else {
        builder.run.len()
    };
    let call = builder.call(call, before, slot, false, CallWidth::Single)?;
    if let Some((_, index)) = definition {
        builder.finish_event(index)?;
    }
    Some(HirExpr::Call(Box::new(call)))
}

fn plan(
    context: NativeFrameContext<'_>,
    stmts: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    sink: usize,
    call: &HirCallExpr,
    width: CallWidth,
) -> Option<Plan> {
    if call.fastcall.is_some() {
        let mut plan = fastcall_plan(context, &stmts[..sink], facts, dialect, sink, call, width)?;
        plan.result_local = scalar_local(stmts[sink]).map(|(local, _)| local);
        return Some(plan);
    }
    let frame = facts.native_call_frame(call)?;
    let run = &stmts[..sink];
    let mut builder = frame_builder(context, run, facts, dialect, frame.home.slot())?;
    let call = builder.call(call, run.len(), frame.home.slot(), true, width)?;
    let first = builder.first_event?;
    if builder.next_event != run.len() {
        return None;
    }
    Some(Plan {
        start: first,
        sink,
        base: frame.home,
        values: if matches!(width, CallWidth::Tail | CallWidth::Fixed(_)) {
            HirValuePack {
                fixed: Vec::new(),
                tail: Some(HirPackTail::open(HirExpr::Call(Box::new(call)))),
            }
        } else {
            vec![HirExpr::Call(Box::new(call))].into()
        },
        result_local: scalar_local(stmts[sink]).map(|(local, _)| local),
        discarded_result: None,
        assignment_targets: Vec::new(),
        indexed_target: None,
        retained_copies: Vec::new(),
        removed: Vec::new(),
    })
}

/// FASTCALL 参数准备按原 direct/COPY/开放域恢复，之后执行 fallback lookup；Boolean 可附常量消息。
/// 原 header false 由 ValueDecision 配对，恢复 AND 时在相同槽重发；不假定 fast path 必成功。
fn fastcall_plan(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    sink: usize,
    call: &HirCallExpr,
    width: CallWidth,
) -> Option<Plan> {
    if call.fastcall.is_some_and(|protocol| {
        protocol.tail_is_direct()
            && (0..call.args.fixed.len()).all(|index| protocol.fixed_is_direct(index))
    }) && call.args.tail.is_some()
        && matches!(width, CallWidth::Single | CallWidth::Ignore)
    {
        return fastcall_open_plan(context, run, facts, dialect, sink, call, width);
    }
    if matches!(width, CallWidth::Single | CallWidth::Ignore)
        && (fastcall_has_copy_arguments(call)
            || matches!(call.fastcall,
                Some(crate::transformer::FastCallProtocol::Mask { builtin, .. })
                    if builtin != 1 || matches!(width, CallWidth::Single)))
    {
        return fastcall_fixed_arguments_plan(context, run, facts, dialect, sink, call, width);
    }
    // Luau Bytecode.h 的 LBF_ASSERT = 1；保留原编号，不凭 fallback 名字猜内建语义。
    let protocol @ crate::transformer::FastCallProtocol::Mask {
        builtin: 1,
        direct_tail: false,
        ..
    } = call.fastcall?
    else {
        return None;
    };
    if dialect != DecompileDialect::Luau
        || !matches!(width, CallWidth::Ignore)
        || call.method != HirMethodCall::None
        || call.args.tail.is_some()
    {
        return None;
    }
    let [argument, message @ ..] = call.args.fixed.as_slice() else {
        return None;
    };
    if message.len() > 1 || !(0..call.args.fixed.len()).all(|index| protocol.fixed_is_direct(index))
    {
        return None;
    }
    let frame = facts.native_fastcall_frame(call)?;
    let ValuePack::Fixed(args) = frame.args else {
        return None;
    };
    if args.len != call.args.fixed.len()
        || args.start.index() != frame.home.slot() + 1
        || frame.results != Some(ResultPack::Ignore)
        || !frame.arguments_unaliased
    {
        return None;
    }
    let mut builder = frame_builder(context, run, facts, dialect, frame.home.slot())?;
    let value = match argument {
        HirExpr::LocalRef(local) => {
            if facts.trusted_local_home_slot(*local)
                != Some(HomeSlotKey::new(args.start.index(), 0))
            {
                return None;
            }
            scalar_local(run[builder.definition(*local, run.len())?])?.1
        }
        value => value,
    };
    if matches!(value, HirExpr::LogicalAnd(_)) {
        let prewrite = facts.boolean_argument_prewrite(call, 0)?;
        if prewrite.home != HomeSlotKey::new(args.start.index(), 0)
            || matches!(argument, HirExpr::LocalRef(local) if facts.promoted_local_for_temp(prewrite.result) != Some(*local))
        {
            return None;
        }
        let index = *builder.temp_definitions.get(&prewrite.initial)?;
        if !matches!(scalar_binding(run[index]), Some((HirBinding::Temp(temp), HirExpr::Boolean(false))) if temp == prewrite.initial)
        {
            return None;
        }
        builder.finish_event(index)?;
    } else if !(matches!(value, HirExpr::Binary(_))
        || matches!(value, HirExpr::Unary(unary)
            if unary.source_site.is_none()
                && unary.op == crate::hir::HirUnaryOpKind::Not
                && matches!(unary.expr, HirExpr::Binary(_))))
    {
        return None;
    }
    builder.boolean_frame = Some(args.start.index());
    let argument = builder.expr(
        argument,
        run.len(),
        args.start.index(),
        None,
        false,
        true,
        facts.call_argument_value(call, 0).filter(|producer| {
            matches!(argument, HirExpr::LocalRef(local) if facts.promoted_local_for_temp(*producer) == Some(*local))
        }),
    )?;
    let mut arguments = vec![argument];
    if let [message] = message {
        let value = match message {
            HirExpr::LocalRef(local) => {
                scalar_local(run[builder.definition(*local, run.len())?])?.1
            }
            value => value,
        };
        if !matches!(value, HirExpr::String(_)) {
            return None;
        }
        arguments.push(builder.expr(
            message, run.len(), args.start.index() + 1, None, false, true,
            facts.call_argument_value(call, 1).filter(|producer| {
                matches!(message, HirExpr::LocalRef(local) if facts.promoted_local_for_temp(*producer) == Some(*local))
            }),
        )?);
    }
    // fallback lookup 在所有参数准备后发生；它可能已经提升为复用低槽的 local。
    // 同一帧消费该 producer，不能把查找移到可能执行元方法的比较之前。
    let callee = builder.expr(
        &call.callee,
        run.len(),
        frame.home.slot(),
        None,
        true,
        false,
        None,
    )?;
    if !matches!(&callee, HirExpr::GlobalRef(global) if global.key.as_utf8() == Some("assert")) {
        return None;
    }
    let first = builder.first_event?;
    if builder.next_event != run.len() {
        return None;
    }
    let mut rebuilt = call.clone();
    rebuilt.callee = callee;
    rebuilt.args = arguments.into();
    Some(Plan {
        start: first,
        sink,
        base: frame.home,
        values: vec![HirExpr::Call(Box::new(rebuilt))].into(),
        result_local: None,
        discarded_result: None,
        assignment_targets: Vec::new(),
        indexed_target: None,
        retained_copies: Vec::new(),
        removed: Vec::new(),
    })
}

/// 开放参数 CALL 先完成，再执行 fallback lookup；固定参数仍先写入原槽，不压缩尾部返回宽度。
fn fastcall_open_plan(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    sink: usize,
    call: &HirCallExpr,
    width: CallWidth,
) -> Option<Plan> {
    if dialect != DecompileDialect::Luau || call.method != HirMethodCall::None {
        return None;
    }
    let tail = call.args.tail.as_ref()?;
    if tail.exact_width().is_some() {
        return None;
    }
    let HirExpr::Call(argument) = tail.as_expr() else {
        return None;
    };
    let frame = facts.native_fastcall_frame(call)?;
    let ValuePack::Open(argument_home) = frame.args else {
        return None;
    };
    if !match (width, frame.results) {
        (CallWidth::Ignore, Some(ResultPack::Ignore)) => true,
        (CallWidth::Single, Some(ResultPack::Fixed(pack))) => {
            pack.start.index() == frame.home.slot() && pack.len == 1
        }
        _ => false,
    } || !frame.arguments_unaliased
        || argument_home.index() != frame.home.slot() + 1
    {
        return None;
    }
    let mut builder = frame_builder(context, run, facts, dialect, frame.home.slot())?;
    let roots = call
        .argument_roots
        .iter()
        .map(|root| (root.argument, root.producer))
        .collect::<BTreeMap<_, _>>();
    let mut fixed = Vec::with_capacity(call.args.fixed.len());
    for (index, value) in call.args.fixed.iter().enumerate() {
        let value = builder.expr(
            value,
            run.len(),
            argument_home.index() + index,
            None,
            false,
            true,
            facts
                .call_argument_value(call, index)
                .or_else(|| roots.get(&index).copied()),
        )?;
        // 候选拒绝[ProofIncomplete]：开放帧固定前缀只证明常量/低槽快照；复合 Boolean 等仍需其原预写事务。
        if !matches!(
            value,
            HirExpr::Nil
                | HirExpr::Boolean(_)
                | HirExpr::Integer(_)
                | HirExpr::Number(_)
                | HirExpr::String(_)
                | HirExpr::LocalRef(_)
                | HirExpr::ParamRef(_)
        ) {
            return None;
        }
        fixed.push(value);
    }
    let argument = builder.call(
        argument,
        run.len(),
        argument_home.index() + fixed.len(),
        false,
        CallWidth::Open,
    )?;
    let callee = builder.expr(
        &call.callee,
        run.len(),
        frame.home.slot(),
        None,
        true,
        false,
        Some(frame.callee),
    )?;
    if !fastcall_callee_is_named(&callee) {
        return None;
    }
    let first = builder.first_event?;
    if builder.next_event != run.len() {
        return None;
    }
    let mut rebuilt = call.clone();
    rebuilt.callee = callee;
    rebuilt.args.fixed = fixed;
    rebuilt.args.tail = Some(HirPackTail::open(HirExpr::Call(Box::new(argument))));
    Some(Plan {
        start: first,
        sink,
        base: frame.home,
        values: vec![HirExpr::Call(Box::new(rebuilt))].into(),
        result_local: None,
        discarded_result: None,
        assignment_targets: Vec::new(),
        indexed_target: None,
        retained_copies: Vec::new(),
        removed: Vec::new(),
    })
}

/// 原 debug 声明直接给出 CALL 结果身份；不从后续调用或临时名字猜测独立 initializer。
/// 只恢复已有同槽声明的 RHS，完整准备事件、词法前缀和后续读写仍由同一帧事务核对。
fn source_call_initializer(proto: &HirProto, stmt: &HirStmt, facts: &ProtoPromotionFacts) -> bool {
    let matched = || {
        let HirStmt::LocalDecl(decl) = stmt else {
            return None;
        };
        let ([local], [HirExpr::Call(call)], None) = (
            decl.bindings.as_slice(),
            decl.values.fixed.as_slice(),
            &decl.values.tail,
        ) else {
            return None;
        };
        let scope = proto
            .local_debug_scopes
            .get(local.index())
            .copied()
            .flatten()?;
        let initializer = proto
            .debug_scopes
            .get(scope)
            .copied()
            .flatten()?
            .initializer_temp?;
        let frame = facts
            .native_call_frame(call)
            .or_else(|| facts.native_fastcall_frame(call))?;
        (facts.operation_result_temp(call.source_site?) == Some(initializer)
            && facts.promoted_local_for_temp(initializer) == Some(*local)
            && facts.trusted_local_home_slot(*local) == Some(frame.home)
            && matches!(frame.results, Some(ResultPack::Fixed(pack))
                if pack.start.index() == frame.home.slot() && pack.len == 1))
        .then_some(())
    };
    matched().is_some()
}

/// 已有结果声明回到原 CALL 槽；非 direct 参数只能是低槽读取，不提前截断参数表达式树。
/// 这不是普通嵌套 CALL 的独立 initializer 许可，后者仍由后续帧下界决定提交时机。
fn fastcall_copy_initializer(
    stmt: &HirStmt,
    next: Option<&HirStmt>,
    facts: &ProtoPromotionFacts,
    following_floor: Option<usize>,
    nested: bool,
) -> bool {
    if nested || !matches!(stmt, HirStmt::LocalDecl(_)) {
        return false;
    }
    let Some((target, HirExpr::Call(call))) = scalar_local(stmt) else {
        return false;
    };
    if !fastcall_has_copy_arguments(call) {
        return false;
    }
    let Some(frame) = facts.native_fastcall_frame(call) else {
        return false;
    };
    if following_floor.is_some_and(|floor| floor <= frame.home.slot())
        || call
            .source_site
            .and_then(|source| facts.operation_result_temp(source))
            .is_some_and(|temp| facts.temp_is_transferred_call_argument(temp))
        || !matches!(frame.results, Some(ResultPack::Fixed(pack))
        if pack.start.index() == frame.home.slot() && pack.len == 1)
        || facts.trusted_local_home_slot(target) != Some(frame.home)
        || call
            .source_site
            .and_then(|source| facts.operation_result_temp(source))
            .and_then(|temp| facts.promoted_local_for_temp(temp))
            != Some(target)
    {
        return false;
    }
    !next.is_some_and(|next| matches!(scalar_local(next),
        Some((copy, HirExpr::LocalRef(source))) if *source == target
            && facts.trusted_local_home_slot(copy).is_none_or(|home| home.slot() <= frame.home.slot())))
}

fn fastcall_has_copy_arguments(call: &HirCallExpr) -> bool {
    matches!(call.fastcall,
        Some(protocol @ crate::transformer::FastCallProtocol::Mask { direct_tail: false, .. })
            if (0..call.args.fixed.len()).any(|index| !protocol.fixed_is_direct(index)))
}

/// 原 FASTCALL 已签发 builtin 身份，重建仍须保留裸全局或库字段拼写以重发快路径。
fn fastcall_callee_is_named(callee: &HirExpr) -> bool {
    let identifier = |name: &crate::lua_string::LuaString| {
        name.as_utf8()
            .is_some_and(|name| DecompileDialect::Luau.is_identifier_name(name))
    };
    match callee {
        HirExpr::GlobalRef(global) => identifier(&global.key),
        HirExpr::TableAccess(access) => matches!((&access.base, &access.key),
            (HirExpr::GlobalRef(global), HirExpr::String(key)) if identifier(&global.key) && identifier(key)),
        _ => false,
    }
}

/// 非 direct 参数保持快速路径的低槽直读和 fallback 的逐参数 COPY，然后才求 callee。
/// direct 参数先按原槽准备，嵌入常量在 fallback 才 LOADK；不按当前语句位置任意排序。
/// 这两条路径必须一起恢复；不能按普通 CALL 的 callee-first 顺序提前移动参数准备。
/// 全 direct 参数使用同一准备协议；是否存在 COPY 不决定表分配事务的恢复资格。
fn fastcall_fixed_arguments_plan(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    sink: usize,
    call: &HirCallExpr,
    width: CallWidth,
) -> Option<Plan> {
    let protocol @ crate::transformer::FastCallProtocol::Mask {
        direct_tail: false, ..
    } = call.fastcall?
    else {
        return None;
    };
    if dialect != DecompileDialect::Luau
        || call.method != HirMethodCall::None
        || call.args.tail.is_some()
        || !(1..=3).contains(&call.args.fixed.len())
    {
        return None;
    }
    let frame = facts.native_fastcall_frame(call)?;
    let ValuePack::Fixed(args) = frame.args else {
        return None;
    };
    if args.len != call.args.fixed.len()
        || args.start.index() != frame.home.slot() + 1
        || !match (width, frame.results) {
            (CallWidth::Ignore, Some(ResultPack::Ignore)) => true,
            (CallWidth::Single, Some(ResultPack::Fixed(pack))) => {
                pack.start.index() == frame.home.slot() && pack.len == 1
            }
            _ => false,
        }
        || !frame.arguments_unaliased
    {
        return None;
    }
    let copies = facts.fastcall_argument_copies(call)?;
    if copies.len()
        != (0..args.len)
            .filter(|index| !protocol.fixed_is_direct(*index))
            .count()
    {
        return None;
    }
    let mut builder = frame_builder(context, run, facts, dialect, frame.home.slot())?;
    let mut arguments = vec![None; args.len];
    let mut copies = copies.iter();
    for prepare_direct in [true, false] {
        for (index, argument) in call.args.fixed.iter().enumerate() {
            let direct = protocol.fixed_is_direct(index);
            let embedded = protocol.fixed_is_embedded_constant(index);
            if (direct && !embedded) != prepare_direct {
                continue;
            }
            let slot = args.start.index() + index;
            if direct {
                let value = builder.expr(
                    argument,
                    run.len(),
                    slot,
                    None,
                    false,
                    true,
                    facts.call_argument_value(call, index),
                )?;
                let literal = matches!(
                    value,
                    HirExpr::Nil
                        | HirExpr::Boolean(_)
                        | HirExpr::Integer(_)
                        | HirExpr::Number(_)
                        | HirExpr::String(_)
                );
                let lookup = !embedded
                    && matches!(&value, HirExpr::TableAccess(access)
                if facts.table_read_result_home(access) == Some(HomeSlotKey::new(slot, 0))
                    && facts.native_table_read_layout(access).is_some_and(|layout|
                        layout.key.is_none()
                            && layout.base.slot() < frame.home.slot()
                            && builder.direct_home(&access.base) == Some(layout.base)));
                // CALL 的单结果与完整原槽准备由 builder.call 签证；direct 阶段仍先于
                // fallback COPY/lookup，不能借此移动未纳入同一事务的根释放。
                let call = !embedded && matches!(value, HirExpr::Call(_));
                // compileExprFastcallN 对非 local 参数调用 compileExprTempTop；已有
                // builder 证明表字段/事件，原 allocation 还须落在当前 direct 参数槽。
                let table = !embedded
                    && matches!(&value, HirExpr::TableConstructor(table)
                        if facts.allocation_result_home(table).is_some_and(|home| home.slot() == slot));
                // 嵌入常量不能变成有事件的 RHS；其余表达式尚无此准备协议的证明。
                if !literal && !lookup && !call && !table {
                    return None;
                }
                arguments[index] = Some(value);
                continue;
            }
            let copy = copies.next()?;
            if copy.argument != index
                || copy.home != HomeSlotKey::new(slot, 0)
                || copy.source_home.slot() >= frame.home.slot()
            {
                return None;
            }
            let value = builder.expr(
                argument,
                run.len(),
                slot,
                None,
                false,
                true,
                Some(copy.producer),
            )?;
            let home = match &value {
                HirExpr::LocalRef(local) => facts.trusted_local_home_slot(*local),
                HirExpr::ParamRef(param) => facts.trusted_param_home_slot(*param),
                _ => None,
            };
            if home != Some(copy.source_home) {
                return None;
            }
            arguments[index] = Some(value);
        }
    }
    let arguments = arguments.into_iter().collect::<Option<Vec<_>>>()?;
    let callee = builder.expr(
        &call.callee,
        run.len(),
        frame.home.slot(),
        None,
        true,
        false,
        Some(frame.callee),
    )?;
    // 全局 builtin 拼写保留原 FASTCALL 分类；不把一般函数别名当作重新产生快路径的证书。
    if !fastcall_callee_is_named(&callee) {
        return None;
    }
    let first = builder.first_event?;
    if builder.next_event != run.len() {
        return None;
    }
    let rebuilt = HirCallExpr {
        callee,
        args: arguments.into(),
        method: call.method,
        method_key: call.method_key.clone(),
        callee_root_handoff: call.callee_root_handoff,
        method_rewrite_transaction: call.method_rewrite_transaction,
        frame_root_ends: call.frame_root_ends.clone(),
        source_site: call.source_site,
        fastcall: call.fastcall,
        argument_roots: call.argument_roots.clone(),
    };
    Some(Plan {
        start: first,
        sink,
        base: frame.home,
        values: vec![HirExpr::Call(Box::new(rebuilt))].into(),
        result_local: None,
        discarded_result: None,
        assignment_targets: Vec::new(),
        indexed_target: None,
        retained_copies: Vec::new(),
        removed: Vec::new(),
    })
}

fn return_plan(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    ret: &crate::hir::common::HirReturn,
) -> Option<Plan> {
    let frame = facts.native_return_frame(ret)?;
    let mut builder = frame_builder(context, run, facts, dialect, frame.home.slot())?;
    let single_concat = ret.values.fixed.first().is_some_and(|value| {
        let value = match value {
            HirExpr::LocalRef(local) => builder
                .definition(*local, run.len())
                .and_then(|index| scalar_local(run[index]))
                .map(|(_, value)| value),
            value => Some(value),
        };
        matches!(value, Some(HirExpr::Binary(binary))
            if binary.op == crate::hir::common::HirBinaryOpKind::Concat)
    });
    match frame.values {
        ValuePack::Fixed(pack)
            if ret.values.tail.is_none()
                && pack.len == ret.values.fixed.len()
                && (pack.len > 1 || single_concat) => {}
        ValuePack::Open(_)
            if ret
                .values
                .tail
                .as_ref()
                .is_some_and(|tail| tail.exact_width().is_none()) => {}
        _ => return None,
    }
    let fixed = ret
        .values
        .fixed
        .iter()
        .enumerate()
        .map(|(index, expr)| {
            builder.expr(
                expr,
                run.len(),
                frame.home.slot() + index,
                None,
                false,
                true,
                None,
            )
        })
        .collect::<Option<Vec<_>>>()?;
    let tail = match &ret.values.tail {
        Some(tail) => {
            let HirExpr::Call(call) = tail.as_expr() else {
                return None;
            };
            Some(HirPackTail::open(HirExpr::Call(Box::new(builder.call(
                call,
                run.len(),
                frame.home.slot() + fixed.len(),
                false,
                CallWidth::Open,
            )?))))
        }
        None => None,
    };
    if dialect == DecompileDialect::Luau
        && tail.is_none()
        && let Some(first) = fixed.first().and_then(|value| builder.direct_home(value))
        && fixed.iter().enumerate().all(|(index, value)| {
            builder.direct_home(value) == Some(HomeSlotKey::new(first.slot() + index, 0))
        })
        && first != frame.home
    {
        // Luau 直接返回连续的既有 local，不重发准备区 COPY；不能删掉原槽覆盖。
        return None;
    }
    let start = builder.first_event?;
    if builder.next_event != run.len() {
        return None;
    }
    Some(Plan {
        start,
        sink: run.len(),
        base: frame.home,
        values: HirValuePack { fixed, tail },
        result_local: None,
        discarded_result: None,
        assignment_targets: Vec::new(),
        indexed_target: None,
        retained_copies: Vec::new(),
        removed: Vec::new(),
    })
}

/// 原 CALL 的连续写回仍以低槽赋值保留时，可由这些语句履行累积 MOVE 责任。
/// 声明不能领取此证明；整批 preview 后还须确认各依赖语句未被删除、改写或迁为声明。
#[expect(
    clippy::type_complexity,
    reason = "只在一次帧候选中返回原写槽和冻结的语句依赖"
)]
fn retained_result_copies(
    flat: &[Option<FlatStmt<'_>>],
    index: usize,
    call: &HirCallExpr,
    facts: &ProtoPromotionFacts,
) -> Option<(BTreeSet<HomeSlotKey>, Vec<(usize, LocalId, LocalId)>)> {
    let result = facts.operation_result_temp(call.source_site?)?;
    let home = facts.trusted_temp_home_slot(result)?;
    let steps = facts.trusted_immediate_moves(result)?;
    if steps.is_empty() {
        return None;
    }
    let mut homes = BTreeSet::new();
    let mut retained = Vec::new();
    let mut previous_temp = result;
    let mut previous_local = facts.promoted_local_for_temp(result)?;
    for (offset, step) in steps.iter().enumerate() {
        let entry = flat.get(index + offset)?.as_ref()?;
        let HirStmt::Assign(assign) = entry.stmt else {
            return None;
        };
        let ([HirLValue::Local(target)], [HirExpr::LocalRef(source)], None) = (
            assign.targets.as_slice(),
            assign.values.fixed.as_slice(),
            &assign.values.tail,
        ) else {
            return None;
        };
        if step.target_home.slot() >= home.slot()
            || step.source != Some(previous_temp)
            || *source != previous_local
            || facts.trusted_local_home_slot(*target) != Some(step.target_home)
            || facts.trusted_local_home_slot(*source) != Some(step.source_home)
        {
            return None;
        }
        homes.insert(step.target_home);
        previous_temp = step.target;
        previous_local = *target;
        if offset != 0 {
            retained.push((entry.id, *target, *source));
        }
    }
    Some((homes, retained))
}

fn frame_builder<'a>(
    context: NativeFrameContext<'a>,
    run: &'a [&'a HirStmt],
    facts: &'a ProtoPromotionFacts,
    dialect: DecompileDialect,
    base: usize,
) -> Option<FrameBuilder<'a>> {
    let mut definitions = BTreeMap::<LocalId, Vec<usize>>::new();
    let mut temp_definitions = BTreeMap::new();
    for (index, stmt) in run.iter().enumerate() {
        if let Some((local, _)) = scalar_local(stmt) {
            definitions.entry(local).or_default().push(index);
        } else if let Some((HirBinding::Temp(temp), _)) = scalar_binding(stmt) {
            if temp_definitions.insert(temp, index).is_some() {
                return None;
            }
        } else if !(super::super::table_constructors::constructor_write(stmt).is_some()
            || matches!(stmt, HirStmt::LocalRootRelease(_)))
        {
            return None;
        }
    }
    let constructors = tables::index(run, &definitions);
    Some(FrameBuilder {
        run,
        definitions,
        constructors,
        constructor_depth: 0,
        indexed_key_base: None,
        puc_operand: false,
        facts,
        dialect,
        base,
        next_event: 0,
        first_event: None,
        methods: 0,
        native: Some(context),
        result_move: None,
        temp_definitions,
        boolean_frame: None,
    })
}

/// 空声明只能连同原帧退休；真实 nil、源码调试身份和显式保留义务不可过滤。
fn removable_empty_declaration(
    proto: &HirProto,
    original_nil: &BTreeSet<LocalId>,
    decl: &HirLocalDecl,
) -> bool {
    !decl.bindings.is_empty()
        && decl.values.is_empty()
        && decl.initializer_merge_transaction.is_none()
        && decl.bindings.iter().all(|local| {
            !original_nil.contains(local)
                && proto.local_debug_hints[local.index()].is_none()
                && proto.local_debug_scopes[local.index()].is_none()
                && !proto.inline_dispositions.local(*local).must_preserve()
        })
}

/// 每个直线构造区只选择最后一个 record 终点，不逐字段重建增长中的候选前缀。
fn constructor_ends(
    flat: &[Option<FlatStmt<'_>>],
    empty: &BTreeSet<usize>,
) -> BTreeMap<usize, usize> {
    let mut ends = BTreeMap::new();
    let mut definitions = BTreeMap::new();
    for (index, entry) in flat.iter().enumerate() {
        let Some(entry) = entry else {
            definitions.clear();
            continue;
        };
        if empty.contains(&entry.id) {
            continue;
        }
        if let Some((local, value)) = scalar_local(entry.stmt) {
            if let HirExpr::TableConstructor(table) = value {
                definitions.insert(
                    local,
                    (
                        index,
                        matches!(
                            table.allocation,
                            HirTableAllocation::LuauTemplate { .. }
                                | HirTableAllocation::PucBatched(_)
                        ),
                    ),
                );
            } else {
                definitions.remove(&local);
            }
            continue;
        }
        if let Some(write) = super::super::table_constructors::constructor_write(entry.stmt) {
            let super::super::table_constructors::TableBinding::Local(local) = write.binding()
            else {
                continue;
            };
            if let Some(&(seed, record_allowed)) = definitions.get(&local)
                && (record_allowed || matches!(entry.stmt, HirStmt::TableSetList(_)))
            {
                ends.insert(seed, index);
            }
        } else {
            definitions.clear();
        }
    }
    ends
}
/// 独立构造器也由相同槽/事件 owner 消费 callee COPY，不能留下永久的临时根。
/// 原调用参数区中的表必须等待包含接收 CALL 的事务；拆掉它会抬高接收 caller top。
fn collect_constructor_plans(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    stmt_count: &mut usize,
    plans: &mut Vec<Plan>,
) {
    use crate::hir::visit::HirVisitor;
    struct Arguments<'a> {
        facts: &'a ProtoPromotionFacts,
        owned: BTreeSet<LocalId>,
    }
    impl HirVisitor<'_> for Arguments<'_> {
        fn visit_call(&mut self, call: &HirCallExpr) {
            self.owned.extend(
                call.argument_roots
                    .iter()
                    .filter_map(|root| self.facts.promoted_local_for_temp(root.producer)),
            );
            let Some(frame) = self.facts.native_call_layout(call) else {
                return;
            };
            let start = match frame.args {
                ValuePack::Fixed(pack) => pack.start,
                ValuePack::Open(start) => start,
            };
            let implicit_receiver = usize::from(call.method == HirMethodCall::Implicit);
            for (offset, value) in call.args.fixed.iter().enumerate() {
                if let HirExpr::LocalRef(local) = value
                    && self.facts.trusted_local_home_slot(*local)
                        == Some(HomeSlotKey::new(
                            start.index() + implicit_receiver + offset,
                            0,
                        ))
                {
                    self.owned.insert(*local);
                }
            }
        }
    }
    let mut arguments = Arguments {
        facts,
        owned: BTreeSet::new(),
    };
    visit_stmts(&context.proto.body.stmts, &mut arguments);
    let mut flat = Vec::new();
    flatten_scope(&context.proto.body, stmt_count, &mut flat);
    let original_nil_locals = facts
        .nil_write_groups()
        .flat_map(|group| {
            group
                .iter()
                .filter_map(|temp| facts.promoted_local_for_temp(*temp))
        })
        .collect::<BTreeSet<_>>();
    let empty = flat
        .iter()
        .filter_map(|entry| {
            let entry = entry.as_ref()?;
            let HirStmt::LocalDecl(decl) = entry.stmt else {
                return None;
            };
            removable_empty_declaration(context.proto, &original_nil_locals, decl)
                .then_some(entry.id)
        })
        .collect::<BTreeSet<_>>();
    // 每个直线构造区只在最后一次 record 写审理，避免对逐渐增长的字段前缀重复建树。
    let ends = constructor_ends(&flat, &empty);
    let mut first_seed = None;
    let mut start = 0;
    for (index, entry) in flat.iter().enumerate() {
        let Some(entry) = entry else {
            first_seed = None;
            start = index + 1;
            continue;
        };
        if empty.contains(&entry.id) {
            continue;
        }
        if first_seed.is_none()
            && ends.contains_key(&index)
            && let HirStmt::LocalDecl(decl) = entry.stmt
            && let ([local], [HirExpr::TableConstructor(_)], None) = (
                decl.bindings.as_slice(),
                decl.values.fixed.as_slice(),
                &decl.values.tail,
            )
        {
            first_seed = Some((index, *local));
        }
        if let Some(write) = super::super::table_constructors::constructor_write(entry.stmt)
            && let super::super::table_constructors::TableBinding::Local(local) = write.binding()
            && let Some((seed, owner)) = first_seed
            && owner == local
            && ends.get(&seed) == Some(&index)
        {
            if !arguments.owned.contains(&owner)
                && let Some(base) = facts.trusted_local_home_slot(owner)
            {
                // 构造器 owner 留下的空声明没有求值事件；只从 builder 输入过滤，
                // 原坐标仍进入 removed，由整批 preview 核对后续每个 read/capture/重新声明。
                let run = flat[start..=index]
                    .iter()
                    .filter(|entry| !empty.contains(&entry.as_ref().unwrap().id))
                    .map(|entry| entry.as_ref().unwrap().stmt)
                    .collect::<Vec<_>>();
                let seed_in_run = flat[start..seed]
                    .iter()
                    .filter(|entry| !empty.contains(&entry.as_ref().unwrap().id))
                    .count();
                if let Some(mut builder) = frame_builder(context, &run, facts, dialect, base.slot())
                    && let HirExpr::TableConstructor(table) =
                        scalar_local(run[seed_in_run]).unwrap().1
                    && (!matches!(table.allocation, HirTableAllocation::PucBatched(_))
                        || facts.allocation_result_home(table) == Some(base))
                    && let Some(value) = builder.constructor(seed_in_run, table, base.slot())
                    && builder.next_event == run.len()
                {
                    plans.push(Plan {
                        start: flat[seed].unwrap().id,
                        sink: entry.id,
                        base,
                        values: vec![value].into(),
                        result_local: Some(owner),
                        discarded_result: None,
                        assignment_targets: Vec::new(),
                        indexed_target: None,
                        retained_copies: Vec::new(),
                        removed: flat[seed..index]
                            .iter()
                            .map(|entry| entry.unwrap().id)
                            .collect(),
                    });
                }
            }
            first_seed = None;
            start = index + 1;
        } else if scalar_local(entry.stmt).is_none()
            && super::super::table_constructors::constructor_write(entry.stmt).is_none()
        {
            first_seed = None;
            start = index + 1;
        }
    }
}

/// 原 table 临时位于新标量声明之上；整个 initializer 重放 table/SETLIST/GETTABLE，
/// 不给 scratch 留下永久声明。旧身份的其它 read/capture 仍由同一 preview 拒绝。
/// 低于后续原 CALL 或作为后继 SETTABLE 的稳定低槽表，可成为独立索引声明；
/// 中间 base/key 由同一读取帧完整消费，原唯一目标快照则留给 indexed 事务。
fn lookup_initializer(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    target: LocalId,
    access: &crate::hir::common::HirTableAccess,
    home: HomeSlotKey,
) -> Option<Plan> {
    let mut builder = frame_builder(context, run, facts, dialect, home.slot())?;
    let value = builder.puc_lookup(access, run.len(), home.slot())?;
    let start = builder.first_event?;
    if builder.next_event != run.len() {
        return None;
    }
    Some(Plan {
        start,
        sink: run.len(),
        base: home,
        values: vec![value].into(),
        result_local: Some(target),
        discarded_result: None,
        assignment_targets: Vec::new(),
        indexed_target: None,
        retained_copies: Vec::new(),
        removed: Vec::new(),
    })
}

fn scalar_array_lookup_plan(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    producer: &HirStmt,
    sink: &HirStmt,
    original_call_floor: Option<usize>,
) -> Option<Plan> {
    let (source, HirExpr::TableConstructor(table)) = scalar_local(producer)? else {
        return None;
    };
    let HirStmt::LocalDecl(decl) = sink else {
        return None;
    };
    let ([target], [HirExpr::TableAccess(access)], None) = (
        decl.bindings.as_slice(),
        decl.values.fixed.as_slice(),
        &decl.values.tail,
    ) else {
        return None;
    };
    let base = facts.trusted_local_home_slot(*target)?;
    // 与普通 CALL initializer 共用后续原调用下界；无已证窗口时保留 scratch。
    // 参数/操作数区必须等待包含接收 CALL 的完整事务，不能先冻结一个永久 local。
    if base.slot() >= original_call_floor? {
        return None;
    }
    let source_home = facts.trusted_local_home_slot(source)?;
    let homes = facts.complete_local_definition_write_homes(source);
    if !matches!(access.base, HirExpr::LocalRef(local) if local == source)
        || source == *target
        || context
            .proto
            .local_debug_hints
            .get(source.index())
            .is_some_and(Option::is_some)
        || context
            .proto
            .local_debug_scopes
            .get(source.index())
            .is_some_and(Option::is_some)
        || context
            .proto
            .inline_dispositions
            .local(source)
            .must_preserve()
        || (context.barred.contains(&source_home)
            && !facts.allocation_result_reference_unaliased(table))
        || homes.iter().any(|home| *home != source_home)
        || !homes.is_disjoint(context.closed)
        || facts.allocation_result_home(table) != Some(source_home)
    {
        return None;
    }
    Some(Plan {
        start: 0,
        sink: 0,
        base,
        values: vec![tables::scalar_array_lookup(facts, table, access, base)?].into(),
        result_local: Some(*target),
        discarded_result: None,
        assignment_targets: Vec::new(),
        indexed_target: None,
        retained_copies: Vec::new(),
        removed: Vec::new(),
    })
}

/// 完整构造器在 freereg 求值，再 MOVE 到已有低槽 local；只消除两条紧邻语句间的声明。
/// PUC 空表与 Luau 静态模板共用此前缀事务，字段树原样保留，不重新合并任何字段写。
fn completed_table_assignment(
    proto: &HirProto,
    stmts: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    barred: &BTreeSet<HomeSlotKey>,
    closed: &BTreeSet<HomeSlotKey>,
    sink: usize,
) -> Option<Plan> {
    if dialect == DecompileDialect::Luajit {
        return None;
    }
    let HirStmt::Assign(assign) = &stmts[sink] else {
        return None;
    };
    let ([HirLValue::Local(target)], [HirExpr::LocalRef(source)], None) = (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) else {
        return None;
    };
    let start = sink.checked_sub(1)?;
    let (producer, HirExpr::TableConstructor(table)) = scalar_local(stmts[start])? else {
        return None;
    };
    let base = facts.trusted_local_home_slot(producer)?;
    let allocation_home = facts.allocation_result_home(table)?;
    let target_home = facts.trusted_local_home_slot(*target)?;
    let write_homes = facts.complete_local_definition_write_homes(producer);
    let supported_constructor = if dialect == DecompileDialect::Luau {
        matches!(table.allocation, HirTableAllocation::LuauTemplate { .. })
            && table.fields.iter().all(|field| matches!(field,
                HirTableField::Record(record) if matches!(record.key, HirExpr::String(_))
                    && matches!(record.value, HirExpr::Nil | HirExpr::Boolean(_) | HirExpr::Integer(_) | HirExpr::Number(_) | HirExpr::String(_))))
    } else {
        table.fields.is_empty() && table.allocation.batched_capacity_matches(0, 0) == Some(true)
    };
    if producer != *source
        || allocation_home != base
        || target_home.slot() >= base.slot()
        || !supported_constructor
        || table.trailing_multivalue.is_some()
        || proto
            .local_debug_hints
            .get(producer.index())
            .is_some_and(Option::is_some)
        || proto
            .local_debug_scopes
            .get(producer.index())
            .is_some_and(Option::is_some)
        || proto.inline_dispositions.local(producer).must_preserve()
        // 透明 MOVE 的低槽目标可能已被捕获；该写在 sink 原位保留。这里只删除
        // scratch 身份，不删目标 cell 写，额外隐藏写仍不属于本事务。
        || (barred.contains(&base) && !facts.allocation_result_reference_unaliased(table))
        || write_homes.iter().any(|home| *home != base && *home != target_home)
        || !facts
            .complete_local_definition_write_homes(producer)
            .is_disjoint(closed)
    {
        return None;
    }
    Some(Plan {
        start,
        sink,
        base,
        values: vec![HirExpr::TableConstructor(table.clone())].into(),
        result_local: None,
        discarded_result: None,
        assignment_targets: vec![*target],
        indexed_target: None,
        retained_copies: Vec::new(),
        removed: Vec::new(),
    })
}

/// 每次批次只克隆一次树，所有剩余读写/capture 共用一次扫描；不为每个 LocalId 扫后缀。
fn build_preview(proto: &HirProto, plans: &[Plan], stmt_count: usize) -> Option<Preview> {
    apply_preview(proto.clone(), plans, stmt_count)
}

/// 原 nil 批次可同时覆盖旧 owner 并声明新的槽。Locals 已原位绑定整个组；
/// 若旧声明被本次帧消费，紧邻的 empty 新成员与全 nil 写可一起成为完整声明。
/// DFS 相邻还须是同一块的语句相邻，不能越过透明 block 的入口或出口。
fn adjacent_nil_declarations(
    proto: &HirProto,
    removed: &[bool],
) -> BTreeMap<usize, (usize, BTreeSet<LocalId>)> {
    let mut flat = Vec::new();
    flatten_scope(&proto.body, &mut 0, &mut flat);
    flat.windows(2)
        .filter_map(|pair| {
            let (previous, next) = (pair[0]?, pair[1]?);
            if previous.id + 1 != next.id || removed[previous.id] {
                return None;
            }
            let (HirStmt::LocalDecl(decl), HirStmt::Assign(assign)) = (previous.stmt, next.stmt)
            else {
                return None;
            };
            let targets = assign
                .targets
                .iter()
                .map(|target| {
                    let HirLValue::Local(local) = target else {
                        return None;
                    };
                    Some(*local)
                })
                .collect::<Option<BTreeSet<_>>>()?;
            (!decl.bindings.is_empty()
                && targets.len() == assign.targets.len()
                && decl.bindings.iter().all(|local| targets.contains(local))
                && decl.values.is_empty()
                && decl.initializer_merge_transaction.is_none()
                && assign.initializer_merge_transaction.is_none()
                && assign.values.tail.is_none()
                && assign.targets.len() == assign.values.fixed.len()
                && assign
                    .values
                    .fixed
                    .iter()
                    .all(|value| matches!(value, HirExpr::Nil)))
            .then(|| {
                (
                    next.id,
                    (previous.id, decl.bindings.iter().copied().collect()),
                )
            })
        })
        .collect()
}

fn apply_preview(mut preview: HirProto, plans: &[Plan], stmt_count: usize) -> Option<Preview> {
    let mut removed = vec![false; stmt_count];
    for plan in plans {
        for &index in &plan.removed {
            removed[index] = true;
        }
    }
    let mut sinks = plans.iter().peekable();
    visit_scope_mut(&mut preview.body, &mut 0, &mut |index, stmt| {
        let Some(plan) = sinks.peek().filter(|plan| plan.sink == index) else {
            return Some(());
        };
        if plan.discarded_result.is_some() {
            let [HirExpr::Call(call)] = plan.values.fixed.as_slice() else {
                unreachable!()
            };
            *stmt = HirStmt::CallStmt(Box::new(crate::hir::common::HirCallStmt {
                call: call.as_ref().clone(),
            }));
            sinks.next();
            return Some(());
        }
        if let Some(local) = plan.result_local
            && super::super::table_constructors::constructor_write(stmt).is_some()
        {
            // record 与 Batch 都是完整构造事务的终点；保持 seed 的声明身份，
            // 不能把整张新构造器仍赋给原最后一个 record 左值。
            *stmt = HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: vec![local],
                values: plan.values.clone(),
                initializer_merge_transaction: None,
            }));
            sinks.next();
            return Some(());
        }
        match stmt {
            HirStmt::CallStmt(sink) => {
                let [HirExpr::Call(call)] = plan.values.fixed.as_slice() else {
                    unreachable!()
                };
                sink.call = call.as_ref().clone();
            }
            HirStmt::LocalDecl(sink) => {
                sink.values = plan.values.clone();
            }
            HirStmt::Assign(sink) => {
                if let Some(target) = &plan.indexed_target {
                    sink.targets = vec![HirLValue::TableAccess(Box::new(target.clone()))];
                } else if !plan.assignment_targets.is_empty() {
                    sink.targets = plan
                        .assignment_targets
                        .iter()
                        .copied()
                        .map(HirLValue::Local)
                        .collect();
                }
                sink.values = plan.values.clone();
            }
            HirStmt::Return(sink) => {
                sink.values = plan.values.clone();
            }
            HirStmt::GenericFor(sink) => {
                sink.rewrite_iterator(|iterator| *iterator = plan.values.clone());
            }
            HirStmt::NumericFor(sink) => {
                let [start, limit, step] = plan.values.fixed.as_slice() else {
                    unreachable!("numeric header plan has three fixed values")
                };
                sink.start = start.clone();
                sink.limit = limit.clone();
                sink.step = step.clone();
            }
            HirStmt::If(sink) => {
                let [condition] = plan.values.fixed.as_slice() else {
                    unreachable!("comparison plan has one condition")
                };
                sink.cond = condition.clone();
            }
            _ => unreachable!(),
        }
        sinks.next();
        Some(())
    })?;
    let nil_declarations = adjacent_nil_declarations(&preview, &removed);
    // 标记被消费的 value epoch，而非从函数入口把所有同名 local 都看作未声明。
    // 已有声明上的 Assign 也必须等到下一次独立写才允许重新读取。
    let mut missing = BTreeMap::<HirBinding, bool>::new();
    let discarded = plans
        .iter()
        .filter_map(|plan| plan.discarded_result.map(|local| (plan.sink, local)))
        .collect::<BTreeMap<_, _>>();
    visit_scope_mut(&mut preview.body, &mut 0, &mut |index, stmt| {
        if let HirStmt::LocalRootRelease(local) = stmt
            && missing.contains_key(&HirBinding::Local(*local))
        {
            // 完整帧已撤销该 epoch 的额外源码根；对应 release 不再有 local 可清。
            // 保留 missing 到下一次独立定义，不能借删除 release 允许后续悬空读取。
            removed[index] = true;
            return Some(());
        }
        if removed[index] {
            if super::super::table_constructors::constructor_write(stmt).is_some() {
                return Some(());
            }
            if let HirStmt::LocalDecl(decl) = stmt {
                for &local in &decl.bindings {
                    missing.insert(HirBinding::Local(local), true);
                }
            } else if let HirStmt::Assign(assign) = stmt {
                // 完整 generic-for initializer 可同时消费多个控制 Temp；后缀仍逐身份查悬空读取。
                for target in &assign.targets {
                    let binding = match target {
                        HirLValue::Temp(temp) => HirBinding::Temp(*temp),
                        HirLValue::Local(local) => HirBinding::Local(*local),
                        _ => return None,
                    };
                    missing.entry(binding).or_default();
                }
            } else {
                let (binding, _) = scalar_binding(stmt)?;
                missing.entry(binding).or_default();
            }
            return Some(());
        }
        if matches!(stmt, HirStmt::Block(_)) {
            return Some(());
        }
        let mut read_missing = false;
        let mut written_missing = BTreeSet::new();
        let mut mentions = (
            BindingReadCollector(|binding| {
                read_missing |= missing.contains_key(&binding);
            }),
            BindingWriteCollector(|binding| {
                if missing.contains_key(&binding) {
                    written_missing.insert(binding);
                }
            }),
        );
        if matches!(
            stmt,
            HirStmt::GenericFor(_) | HirStmt::NumericFor(_) | HirStmt::If(_) | HirStmt::While(_)
        ) {
            crate::hir::visit::visit_stmt_header(stmt, &mut mentions);
        } else {
            visit_stmts(std::slice::from_ref(stmt), &mut mentions);
        }
        if read_missing {
            return None;
        }
        if matches!(stmt, HirStmt::Assign(assign) if assign.generic_for_dispatch_release.is_some())
            && !written_missing.is_empty()
        {
            // 外层构造器不能独自删除或另造 dispatch endpoint 的声明；须由循环头联合消费。
            return None;
        }
        if let Some(&local) = discarded.get(&index) {
            // CALL 与紧邻常量写之间没有观察；结束结果绑定，并在下一次原槽写重建声明。
            missing.insert(HirBinding::Local(local), true);
        }
        if written_missing.is_empty() {
            return Some(());
        }
        if let HirStmt::Assign(assign) = stmt
            && assign.targets.len() > 1
        {
            if written_missing
                .iter()
                .all(|binding| missing.get(binding) == Some(&false))
            {
                // 原声明仍在，仅当前值版本的 COPY 被消费；多结果 RHS 已先查悬空读。
                // 整组写原位重新定义这些已有身份，不应把它们变成新的 local 声明。
                for binding in &written_missing {
                    missing.remove(binding);
                }
                return Some(());
            }
            let nil_declaration = nil_declarations.get(&index);
            let bindings = assign
                .targets
                .iter()
                .map(|target| {
                    let HirLValue::Local(local) = target else {
                        return None;
                    };
                    (missing.get(&HirBinding::Local(*local)) == Some(&true)
                        || nil_declaration.is_some_and(|(_, bindings)| bindings.contains(local)))
                    .then_some(*local)
                })
                .collect::<Option<Vec<_>>>()?;
            if let Some((declaration, declared)) = nil_declaration {
                let targets = bindings.iter().copied().collect::<BTreeSet<_>>();
                if targets.len() != bindings.len() || !declared.is_subset(&targets) {
                    return None;
                }
                removed[*declaration] = true;
            }
            for local in &bindings {
                missing.remove(&HirBinding::Local(*local));
            }
            *stmt = HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings,
                values: std::mem::take(&mut assign.values),
                initializer_merge_transaction: None,
            }));
            return Some(());
        }
        let (binding, _) = scalar_binding(stmt)?;
        if written_missing.len() != 1 {
            return None;
        }
        let needs_declaration = missing.remove(&binding)?;
        if !needs_declaration || matches!(stmt, HirStmt::LocalDecl(_)) {
            return Some(());
        }
        let HirStmt::Assign(assign) = stmt else {
            return None;
        };
        let HirBinding::Local(local) = binding else {
            return None;
        };
        // 原匿名定义已完整消费；后缀首个独立写成为同一身份的新声明起点。
        *stmt = HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: vec![local],
            values: std::mem::take(&mut assign.values),
            initializer_merge_transaction: None,
        }));
        Some(())
    })?;
    Some(Preview {
        proto: preview,
        removed,
    })
}

/// 词法 Block、条件各臂与已有布局证明的数值/泛型循环共用 DFS 坐标。
fn visit_scope_mut(
    block: &mut HirBlock,
    cursor: &mut usize,
    action: &mut impl FnMut(usize, &mut HirStmt) -> Option<()>,
) -> Option<()> {
    for stmt in &mut block.stmts {
        let index = *cursor;
        *cursor += 1;
        action(index, stmt)?;
        if let HirStmt::Block(child) = stmt {
            visit_scope_mut(child, cursor, action)?;
        } else if let HirStmt::NumericFor(for_) = stmt {
            visit_scope_mut(&mut for_.body, cursor, action)?;
        } else if let HirStmt::While(while_) = stmt {
            visit_scope_mut(&mut while_.body, cursor, action)?;
        } else if let HirStmt::GenericFor(for_) = stmt {
            visit_scope_mut(&mut for_.body, cursor, action)?;
        } else if let HirStmt::If(if_) = stmt {
            visit_scope_mut(&mut if_.then_block, cursor, action)?;
            if let Some(else_block) = &mut if_.else_block {
                visit_scope_mut(else_block, cursor, action)?;
            }
        }
    }
    Some(())
}

fn compact_scope(block: &mut HirBlock, removed: &[bool], cursor: &mut usize) {
    block.stmts.retain_mut(|stmt| {
        let index = *cursor;
        *cursor += 1;
        if let HirStmt::Block(child) = stmt {
            compact_scope(child, removed, cursor);
        } else if let HirStmt::NumericFor(for_) = stmt {
            compact_scope(&mut for_.body, removed, cursor);
        } else if let HirStmt::While(while_) = stmt {
            compact_scope(&mut while_.body, removed, cursor);
        } else if let HirStmt::GenericFor(for_) = stmt {
            compact_scope(&mut for_.body, removed, cursor);
        } else if let HirStmt::If(if_) = stmt {
            compact_scope(&mut if_.then_block, removed, cursor);
            if let Some(else_block) = &mut if_.else_block {
                compact_scope(else_block, removed, cursor);
            }
        }
        !removed[index]
    });
}
