//! 在原写入位置恢复完整 LOADNIL 批次、闭包创建声明及原槽复用所需的词法末端。
//!
//! Promotion 保存原指令的有序 canonical 定义组；普通 HIR 完整帧收敛后，只接受仍然
//! 完整、每员单写且无 read/capture 的全 nil 赋值。源槽覆盖是原语句已有的义务，与旧
//! 根来自 CALL、循环 skip 或分支无关；源码前缀证明在原点重发整组物理写，而非猜旧值。
//! 例如 `for i=long_numeric_string(),1 do ... end; if flag then local a,b=nil,nil;
//! observe() end` 中，skip 可留下原字符串；必须原位清空全部原槽，不能在 for/if 前
//! 新建 holder，也不能只保留原 LOADNIL 的一个成员。成功后整组 LocalDecl 进入 AST，
//! 避免普通多目标赋值降低先拆散它，再把无逻辑读的 nil 当作死声明删除。
//! 声明起点不是完整生命周期证明。线性 nil/未读全局读取 run 的后继原帧若重用首槽，
//! 则在同一预览中恢复整个 run 的 do 末端；其它活出值、部分槽退休或未知前缀不借此授权。
//! 未读全局值也能独立形成 run：`do local v=lookup end; local function f() ... end; f()`
//! 中原 CLOSURE 覆盖 v 的槽，不能因没有 LOADNIL 而让 v 活过 f 内的 GC。闭包声明的 home
//! 来自保留的原定义；此处不从 closure 的子 proto 或 MOVE 后的 carrier 反猜创建位置。
//! 单写闭包若只由紧邻 CALL 读取，后继原帧复用其槽时也恢复两条语句的 do 末端；
//! 闭包对象可以被弱表观察，但 caller binding 不能被 capture 或在 run 外再次读取。
//! 临时多返回组只被逐项 COPY 到低槽、且后继原帧完整复用结果区时，可保留 COPY 并
//! 结束临时声明；含其它值版本的多结果赋值由 native assignment owner 处理。
//! 低槽表写若保持原内嵌常量与操作数槽，可以留在闭包 run 内；元方法仍在原位置执行，
//! 不能为提前缩域把观察搬到闭包退休后。
//! 后缀也验证原声明、调用与 for 的帧，避免 `do local n=nil; local v=lookup end; f()`
//! 被扩成父块 Local，导致 v 跨过原低槽 f 的 GC 观察继续存活。
//! 条件消费原内嵌常量及全局读取来源，区分完整 callee 准备入口与内层 CALL 执行时点；
//! 不把内联后的字面量或比较的语义左右次序当成原物理准备顺序。
//! 未树化的普通 CALL、比较与后继 for 准备由 native frame owner 在同一预览中先消费；这里随后
//! 重建候选坐标和完整后缀请求，不把未验证的中间帧或旧 DFS 编号发布给其它 pass。
//! 入口表示源码表达式的完整空闲前缀：动态 key 可先写 base 上一槽，再写 base，
//! 必须同时消费两次原准备及其顺序；不能把“第一条写指令的槽”一律当作 free-base。
//! 候选、读写计数及声明验证均按整棵树批量处理；只在存在候选时复制一次事务预览。

use std::collections::{BTreeMap, BTreeSet};

use crate::decompile::DecompileDialect;
use crate::hir::common::{
    HirBinding, HirBlock, HirExpr, HirInlineRetentionReason, HirLValue, HirLocalDecl, HirProto,
    HirStmt, LocalId, TempId,
};
use crate::hir::promotion::ProtoPromotionFacts;
use crate::hir::simplify::mention::{BindingReadCollector, BindingWriteCollector};
use crate::hir::simplify::walk::for_each_nested_block_mut;
use crate::hir::visit::visit_stmts;

use super::{PrefixRequest, validate_prefixes};

struct NilCandidate {
    temps: Vec<TempId>,
    existing: Option<Vec<LocalId>>,
}

enum NilMaterialization {
    Declare(Vec<LocalId>),
    Existing,
}

pub(in crate::hir::simplify) fn restore_materializations(
    proto: &mut HirProto,
    facts: &mut ProtoPromotionFacts,
    dialect: DecompileDialect,
    is_chunk_entry: bool,
) -> bool {
    let mut has_scope_candidate = false;
    for stmt in &proto.body.stmts {
        crate::hir::visit::visit_stmt_structure(stmt, &mut |stmt| {
            has_scope_candidate |= matches!(
                stmt.scalar_temp_assignment(),
                Some((_, HirExpr::GlobalRef(_)))
            ) || matches!(stmt, HirStmt::LocalDecl(decl)
                if matches!(decl.values.fixed.as_slice(), [HirExpr::Closure(_)]));
        });
    }
    if !facts.has_nil_writes() && !has_scope_candidate {
        return false;
    }
    // 调用/比较/循环准备和词法末端相互依赖，必须在同一事务中完成。native owner
    // 只交出已消费原槽/事件与 value epoch 的预览；下面重新编号并验证全部源码前缀。
    let Some(prepared) =
        crate::hir::simplify::call_frames::prepare_source_frames(proto.clone(), facts, dialect)
    else {
        return false;
    };
    let mut read = BTreeSet::new();
    let mut writes = BTreeMap::<TempId, usize>::new();
    let mut local_read = BTreeMap::<LocalId, usize>::new();
    let mut local_writes = BTreeMap::<LocalId, usize>::new();
    visit_stmts(
        &prepared.body.stmts,
        &mut (
            BindingReadCollector(|binding| {
                if let HirBinding::Temp(temp) = binding {
                    read.insert(temp);
                } else if let HirBinding::Local(local) = binding {
                    *local_read.entry(local).or_default() += 1;
                }
            }),
            BindingWriteCollector(|binding| {
                if let HirBinding::Temp(temp) = binding {
                    *writes.entry(temp).or_default() += 1;
                } else if let HirBinding::Local(local) = binding {
                    *local_writes.entry(local).or_default() += 1;
                }
            }),
        ),
    );
    let mut candidates = BTreeMap::new();
    collect_candidates(
        &prepared.body,
        facts,
        &read,
        &writes,
        &prepared.temp_debug_locals,
        &mut 0,
        &mut candidates,
    );
    let original_local_groups = facts
        .nil_write_groups()
        .filter_map(|temps| {
            let locals = temps
                .iter()
                .map(|temp| facts.promoted_local_for_temp(*temp))
                .collect::<Option<Vec<_>>>()?;
            Some((locals[0], locals))
        })
        .collect::<BTreeMap<_, _>>();
    let mut nil_locals = BTreeSet::new();
    for stmt in &prepared.body.stmts {
        crate::hir::visit::visit_stmt_structure(stmt, &mut |stmt| {
            let HirStmt::LocalDecl(decl) = stmt else {
                return;
            };
            let Some(first) = decl.bindings.first() else {
                return;
            };
            if original_local_groups.get(first) != Some(&decl.bindings)
                || decl.values.tail.is_some()
                || decl.values.fixed.len() != decl.bindings.len()
                || !decl
                    .values
                    .fixed
                    .iter()
                    .all(|value| matches!(value, HirExpr::Nil))
            {
                return;
            }
            let Some(base) = facts.trusted_local_home_slot(*first) else {
                return;
            };
            if decl.bindings.iter().enumerate().any(|(offset, local)| {
                local_read.contains_key(local)
                    || local_writes.get(local) != Some(&1)
                    || facts.trusted_local_home_slot(*local).is_none_or(|home| {
                        home.slot() != base.slot() + offset
                            || !facts
                                .complete_local_definition_write_homes(*local)
                                .iter()
                                .copied()
                                .eq(std::iter::once(home))
                    })
            }) {
                return;
            }
            nil_locals.extend(decl.bindings.iter().copied());
        });
    }
    if candidates.is_empty() && nil_locals.is_empty() && !has_scope_candidate {
        return false;
    }

    // 临时事实与语法一起提交：失败时不发布空 LocalId 或 Temp→Local 合并，后层也不会
    // 看见一个尚未占据原物理槽的 binding。只复制这一 proto 的事实，不建立持久第二套分析。
    let mut preview = prepared;
    let mut preview_facts = facts.clone();
    let mut replacements = BTreeMap::new();
    for (&index, candidate) in &candidates {
        if let Some(locals) = &candidate.existing {
            for (&temp, &local) in candidate.temps.iter().zip(locals) {
                preview_facts.record_temp_to_local_merge(temp, local);
                preview
                    .inline_dispositions
                    .promote_temp_to_local(temp, local);
                preview
                    .inline_dispositions
                    .preserve_local(local, HirInlineRetentionReason::PhysicalFramePrefix);
            }
            replacements.insert(index, NilMaterialization::Existing);
            continue;
        }
        let temps = &candidate.temps;
        let mut locals = Vec::with_capacity(temps.len());
        for &temp in temps {
            let local = materialized_local(&mut preview, &mut preview_facts, temp);
            locals.push(local);
            nil_locals.insert(local);
        }
        replacements.insert(index, NilMaterialization::Declare(locals));
    }
    let mut count = 0;
    materialize(&mut preview.body, &replacements, &mut count);
    let constants_fit_rk = crate::hir::simplify::call_frames::constants_fit_rk(&preview);
    let mut body = std::mem::take(&mut preview.body);
    let mut scopes = MaterializationScopes {
        proto: &mut preview,
        facts: &mut preview_facts,
        read: &read,
        writes: &writes,
        local_read: &local_read,
        local_writes: &local_writes,
        nil_locals: &nil_locals,
        dialect,
        constants_fit_rk,
        closed_run: false,
    };
    let scoped = scopes.block(&mut body);
    let closed_run = scopes.closed_run;
    preview.body = body;
    if !scoped || (candidates.is_empty() && nil_locals.is_empty() && !closed_run) {
        return false;
    }
    for &local in &nil_locals {
        preview
            .inline_dispositions
            .preserve_local(local, HirInlineRetentionReason::PhysicalFramePrefix);
    }
    let mut requests = BTreeMap::new();
    count = 0;
    for stmt in &preview.body.stmts {
        crate::hir::visit::visit_stmt_structure(stmt, &mut |stmt| {
            let home = match stmt {
                HirStmt::LocalDecl(decl)
                    if decl.bindings.iter().any(|local| nil_locals.contains(local)) =>
                {
                    preview_facts.trusted_local_home_slot(decl.bindings[0])
                }
                _ => statement_frame(stmt, &preview_facts, dialect),
            };
            if let Some(home) = home {
                requests.insert(
                    count,
                    PrefixRequest {
                        home,
                        required: match stmt {
                            HirStmt::Assign(assign) => assign
                                .targets
                                .iter()
                                .filter_map(|target| {
                                    if let HirLValue::Local(local) = target {
                                        Some(*local)
                                    } else {
                                        None
                                    }
                                })
                                .collect(),
                            _ => BTreeSet::new(),
                        },
                    },
                );
            }
            count += 1;
        });
    }
    let Ok(preserved) = validate_prefixes(
        &preview,
        &preview_facts,
        dialect,
        is_chunk_entry,
        &vec![false; count],
        &requests,
        true,
    ) else {
        // 候选拒绝[ProofIncomplete]：不补空槽，也不跨未知声明或控制流猜测源码前缀。
        return false;
    };
    for local in preserved {
        preview
            .inline_dispositions
            .preserve_local(local, HirInlineRetentionReason::PhysicalFramePrefix);
    }
    *proto = preview;
    *facts = preview_facts;
    true
}

fn materialized_local(
    proto: &mut HirProto,
    facts: &mut ProtoPromotionFacts,
    temp: TempId,
) -> LocalId {
    let local = LocalId(proto.local_count);
    proto.local_count += 1;
    proto
        .local_debug_hints
        .push(proto.temp_debug_locals.get(temp.index()).cloned().flatten());
    proto
        .local_debug_scopes
        .push(proto.temp_debug_scopes.get(temp.index()).copied().flatten());
    facts.record_local_home_slot(local, facts.trusted_temp_home_slot(temp).unwrap());
    facts.record_temp_to_local_merge(temp, local);
    proto.inline_dispositions.promote_temp_to_local(temp, local);
    proto
        .inline_dispositions
        .preserve_local(local, HirInlineRetentionReason::PhysicalFramePrefix);
    local
}

fn statement_frame(
    stmt: &HirStmt,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
) -> Option<crate::hir::promotion::HomeSlotKey> {
    match stmt {
        HirStmt::LocalDecl(decl) => decl
            .bindings
            .first()
            .and_then(|local| facts.trusted_local_home_slot(*local)),
        HirStmt::NumericFor(for_) => facts
            .numeric_for_body_frame(for_)
            .map(|frame| frame.controls[0]),
        HirStmt::CallStmt(call) => facts.native_call_layout(&call.call).map(|frame| frame.home),
        HirStmt::GenericFor(for_) => facts
            .generic_for_body_frame(for_)
            .and_then(|frame| frame.controls.first().copied()),
        HirStmt::Return(ret) => single_value_frame(&ret.values, facts, dialect),
        HirStmt::Assign(assign) => {
            let entry = single_value_frame(&assign.values, facts, dialect)?;
            if let ([HirLValue::Local(local)], [HirExpr::GlobalRef(_)], None) = (
                assign.targets.as_slice(),
                assign.values.fixed.as_slice(),
                &assign.values.tail,
            ) && facts.trusted_local_home_slot(*local) == Some(entry)
                && matches!(
                    dialect,
                    DecompileDialect::Lua51
                        | DecompileDialect::Lua52
                        | DecompileDialect::Lua53
                        | DecompileDialect::Lua54
                        | DecompileDialect::Lua55
                )
            {
                // 原 GETTABLE/GETTABUP 可直接写回已声明 local，不占 freereg；
                // CALL 即使目标相同仍有独立准备区，不能套用这项直接写回许可。
                None
            } else {
                Some(entry)
            }
        }
        HirStmt::If(if_) => expression_frame(&if_.cond, facts, dialect),
        HirStmt::While(while_) => expression_frame(&while_.cond, facts, dialect),
        _ => None,
    }
}

fn single_value_frame(
    values: &crate::hir::common::HirValuePack,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
) -> Option<crate::hir::promotion::HomeSlotKey> {
    let value = if values.fixed.is_empty() {
        values.tail.as_ref().map(|tail| tail.as_expr())
    } else if values.fixed.len() == 1 && values.tail.is_none() {
        values.fixed.first()
    } else {
        None
    };
    value.and_then(|value| expression_frame(value, facts, dialect))
}

fn expression_frame(
    value: &HirExpr,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
) -> Option<crate::hir::promotion::HomeSlotKey> {
    match value {
        HirExpr::Call(call) => facts.native_call_layout(call).map(|frame| frame.home),
        HirExpr::GlobalRef(global) => facts.global_read_frame(global, dialect),
        HirExpr::TableAccess(access) => {
            if let Some(home) = facts.upvalue_table_read_frame(access) {
                return Some(home);
            }
            if let Some(home) = facts.table_preparation_frame(access, dialect) {
                return Some(home);
            }
            let layout = facts.native_table_read_layout(access)?;
            let result = facts.table_read_result_home(access)?;
            if layout.key.is_none()
                && matches!(access.key, HirExpr::String(_) | HirExpr::Integer(_))
                && let Some(base) = expression_frame(&access.base, facts, dialect)
                && layout.base == base
                && result == base
            {
                // 连续字段读取复用同一暂存槽；首 GETTABLE 的入口来自原来源，
                // 后续 GETFIELD 原位覆写，不另造永久 base local。
                return Some(base);
            }
            let base = match &access.base {
                HirExpr::LocalRef(local) => facts.trusted_local_home_slot(*local)?,
                HirExpr::ParamRef(param) => facts.trusted_param_home_slot(*param)?,
                _ => return None,
            };
            // 原低槽 base 不另行求值，key 的完整入口与结果都在同一 scratch。
            // 例如 object[global_key] 先观察全局 key，再原位写表读取结果；不同槽的
            // base/key 准备或仅知道最终结果的访问，不能从此处取得整条条件入口。
            let key = expression_frame(&access.key, facts, dialect)?;
            (layout.base == base
                && base.slot() < key.slot()
                && layout.key == Some(key)
                && result == key)
                .then_some(key)
        }
        HirExpr::Unary(unary) if unary.op == crate::hir::common::HirUnaryOpKind::Not => {
            expression_frame(&unary.expr, facts, dialect)
        }
        HirExpr::Unary(unary) => {
            let home = facts.unary_operand_home(unary)?;
            if facts.unary_result_home(unary) != Some(home) {
                return None;
            }
            expression_frame(&unary.expr, facts, dialect)
                .or_else(|| facts.operation_operand_preparation(unary.source_site?, &unary.expr))
                .filter(|entry| *entry == home)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            // while 的 break 合并可把原条件接成短路链；首项仍无条件先求值，
            // 原 CALL 的入口槽不因后续谓词变化。右项不能证明整条语句的入口。
            expression_frame(&logical.lhs, facts, dialect)
        }
        HirExpr::Binary(binary) => {
            if let Some(home) = expression_frame(&binary.lhs, facts, dialect) {
                return Some(home);
            }
            if let Some(source) = binary.source_site
                && let Some(home) = facts.operation_operand_preparation(source, &binary.lhs)
                && if binary.op == crate::hir::common::HirBinaryOpKind::Concat {
                    facts.native_concat_buffer(binary)?.start.index() == home.slot()
                } else {
                    facts.native_binary_layout(binary)?.lhs == Some(home)
                }
            {
                return Some(home);
            }
            if let Some(home) = facts.comparison_preparation_frame(binary) {
                return Some(home);
            }
            // 只有原比较内嵌的字面量才不占准备槽。大数字/字符串即使已经内联为
            // 字面量，也可能有原 LOADK；不能据 HIR 外形跨过它。右侧保留整个外层
            // CALL 的 callee 入口，例如 tonumber(f()) 从 tonumber 而非内层 f 开始。
            if !matches!(
                binary.op,
                crate::hir::common::HirBinaryOpKind::Eq
                    | crate::hir::common::HirBinaryOpKind::Lt
                    | crate::hir::common::HirBinaryOpKind::Le
            ) {
                return None;
            }
            let layout = facts.native_binary_layout(binary)?;
            let home = expression_frame(&binary.rhs, facts, dialect)?;
            if layout.rhs != Some(home) {
                return None;
            }
            let direct = match &binary.lhs {
                HirExpr::LocalRef(local) => facts.trusted_local_home_slot(*local),
                HirExpr::ParamRef(param) => facts.trusted_param_home_slot(*param),
                _ => None,
            };
            if let Some(direct) = direct {
                // 已在源码前缀中的同一低槽直接参与比较，不产生新的 operand scratch。
                // Temp 可能尚待物化，Upvalue 则需要 GETUPVAL；两者不能借这个许可。
                return (layout.lhs == Some(direct) && direct.slot() < home.slot()).then_some(home);
            }
            (layout.lhs.is_none()
                && matches!(
                    binary.lhs,
                    HirExpr::Nil
                        | HirExpr::Boolean(_)
                        | HirExpr::Integer(_)
                        | HirExpr::Number(_)
                        | HirExpr::String(_)
                ))
            .then_some(home)
        }
        _ => None,
    }
}

struct MaterializationScopes<'a> {
    proto: &'a mut HirProto,
    facts: &'a mut ProtoPromotionFacts,
    read: &'a BTreeSet<TempId>,
    writes: &'a BTreeMap<TempId, usize>,
    local_read: &'a BTreeMap<LocalId, usize>,
    local_writes: &'a BTreeMap<LocalId, usize>,
    nil_locals: &'a BTreeSet<LocalId>,
    dialect: DecompileDialect,
    constants_fit_rk: bool,
    closed_run: bool,
}

impl MaterializationScopes<'_> {
    /// PUC 的低槽表写不占当前空闲前缀，且所有操作数的原布局仍一致；元方法
    /// 可以观察旧闭包，因此把原语句留在 run 中，不把关闭作用域当作提前清零。
    fn is_low_table_write(&self, stmt: &HirStmt, floor: usize) -> bool {
        if !self.constants_fit_rk
            || matches!(
                self.dialect,
                DecompileDialect::Luau | DecompileDialect::Luajit
            )
        {
            return false;
        }
        let HirStmt::Assign(assign) = stmt else {
            return false;
        };
        let ([HirLValue::TableAccess(access)], [value], None) = (
            assign.targets.as_slice(),
            assign.values.fixed.as_slice(),
            &assign.values.tail,
        ) else {
            return false;
        };
        let Some(layout) = self.facts.native_table_write_layout(access) else {
            return false;
        };
        let operand = |value: &HirExpr, original: Option<crate::hir::promotion::HomeSlotKey>| {
            let home = match value {
                HirExpr::LocalRef(local) => self.facts.trusted_local_home_slot(*local),
                HirExpr::ParamRef(param) => self.facts.trusted_param_home_slot(*param),
                HirExpr::Nil
                | HirExpr::Boolean(_)
                | HirExpr::Integer(_)
                | HirExpr::Number(_)
                | HirExpr::String(_) => return original.is_none(),
                _ => return false,
            };
            home.is_some_and(|home| home.slot() < floor && Some(home) == original)
        };
        operand(&access.base, Some(layout.base))
            && operand(&access.key, layout.key)
            && operand(value, layout.value)
    }

    /// 临时多返回值先落到原连续结果槽，再按现存顺序写入低槽目标；这里只结束
    /// 临时声明，不合并或重排 COPY。每个结果只由对应 COPY 读取，后继帧重用首槽。
    fn result_copy_scope(&self, stmts: &[HirStmt], start: usize) -> Option<usize> {
        let HirStmt::LocalDecl(decl) = &stmts[start] else {
            return None;
        };
        let width = decl.bindings.len();
        if width < 2 || !decl.values.fixed.is_empty() {
            return None;
        }
        let tail = decl.values.tail.as_ref()?;
        let HirExpr::Call(call) = tail.as_expr() else {
            return None;
        };
        let frame = self.facts.native_call_layout(call)?;
        if tail.exact_width() != Some(width)
            || !matches!(frame.results, Some(crate::transformer::ResultPack::Fixed(pack))
                if pack.start.index() == frame.home.slot() && pack.len == width)
        {
            return None;
        }
        let end = start + width + 1;
        if statement_frame(stmts.get(end)?, self.facts, self.dialect) != Some(frame.home) {
            return None;
        }
        let sources = decl
            .bindings
            .iter()
            .enumerate()
            .map(|(offset, &local)| {
                let home = self.facts.trusted_local_home_slot(local)?;
                (home.slot() == frame.home.slot() + offset
                    && self.local_read.get(&local) == Some(&1)
                    && self.local_writes.get(&local) == Some(&1))
                .then_some((local, home))
            })
            .collect::<Option<BTreeMap<_, _>>>()?;
        let mut copied = BTreeSet::new();
        for stmt in &stmts[start + 1..end] {
            let HirStmt::Assign(assign) = stmt else {
                return None;
            };
            let ([HirLValue::Local(target)], [HirExpr::LocalRef(source)], None) = (
                assign.targets.as_slice(),
                assign.values.fixed.as_slice(),
                &assign.values.tail,
            ) else {
                return None;
            };
            let home = *sources.get(source)?;
            let target_home = self.facts.trusted_local_home_slot(*target)?;
            if target_home.slot() >= frame.home.slot()
                || !copied.insert(*source)
                || !self
                    .facts
                    .complete_local_definition_write_homes(*source)
                    .iter()
                    .all(|written| *written == home || *written == target_home)
            {
                // 候选拒绝[ProofIncomplete]：不能丢弃其它物理写、别名读取或部分结果。
                return None;
            }
        }
        Some(end)
    }

    fn block(&mut self, block: &mut HirBlock) -> bool {
        let mut run: Option<(usize, usize, usize)> = None;
        let mut scopes = BTreeMap::new();
        for index in 0..block.stmts.len() {
            if let Some(end) = self.result_copy_scope(&block.stmts, index) {
                scopes.insert(index, end);
                self.closed_run = true;
            }
        }
        for (index, window) in block.stmts.windows(3).enumerate() {
            let HirStmt::LocalDecl(decl) = &window[0] else {
                continue;
            };
            let ([local], [HirExpr::Closure(closure)], None) = (
                decl.bindings.as_slice(),
                decl.values.fixed.as_slice(),
                &decl.values.tail,
            ) else {
                continue;
            };
            let HirStmt::CallStmt(call) = &window[1] else {
                continue;
            };
            let Some(home) = self
                .facts
                .closure_statement_home(*local, closure, &call.call)
            else {
                continue;
            };
            if call.call.callee != HirExpr::LocalRef(*local)
                || self.local_read.get(local) != Some(&1)
                || self.local_writes.get(local) != Some(&1)
            {
                // 候选拒绝[ProofIncomplete]：只消费单写闭包的唯一直接调用与后继整槽覆盖，
                // 其它读取/capture、COPY 写域或未知准备入口不能借展示需要缩短作用域。
                continue;
            }
            let mut end = index + 2;
            while block
                .stmts
                .get(end)
                .is_some_and(|stmt| self.is_low_table_write(stmt, home.slot()))
            {
                end += 1;
            }
            if block
                .stmts
                .get(end)
                .and_then(|stmt| statement_frame(stmt, self.facts, self.dialect))
                != Some(home)
            {
                continue;
            }
            scopes.insert(index, end);
            self.closed_run = true;
        }
        for (index, stmt) in block.stmts.iter_mut().enumerate() {
            if let Some((start, base, next)) = run
                && let Some(frame) = statement_frame(stmt, self.facts, self.dialect)
                && frame.slot() < next
            {
                if frame.slot() != base {
                    return false;
                }
                // 后继原帧重用整段的首槽。这里只包住新 nil 与无 read/capture 的
                // 直接全局读取声明；没有活出区间的 binding，也不提前发出任何清零。
                scopes.insert(start, index);
                self.closed_run = true;
                run = None;
            }
            if let HirStmt::LocalDecl(decl) = stmt
                && !decl.bindings.is_empty()
                && decl
                    .bindings
                    .iter()
                    .all(|local| self.nil_locals.contains(local))
            {
                let base = self
                    .facts
                    .trusted_local_home_slot(decl.bindings[0])
                    .unwrap()
                    .slot();
                if let Some((start, first, next)) = run {
                    if next != base {
                        return false;
                    }
                    run = Some((start, first, next + decl.bindings.len()));
                } else {
                    run = Some((index, base, base + decl.bindings.len()));
                }
            } else {
                if let Some((temp, HirExpr::GlobalRef(global))) = stmt.scalar_temp_assignment()
                    && !self.read.contains(&temp)
                    && self.writes.get(&temp) == Some(&1)
                    && self
                        .proto
                        .temp_debug_locals
                        .get(temp.index())
                        .is_none_or(Option::is_none)
                    && let Some(home) = self.facts.trusted_temp_home_slot(temp)
                    && self.facts.global_read_frame(global, self.dialect) == Some(home)
                    && run.is_none_or(|(_, _, next)| home.slot() == next)
                    && self
                        .facts
                        .complete_temp_definition_write_homes(temp)
                        .iter()
                        .copied()
                        .eq(std::iter::once(home))
                {
                    let (start, base, next) = run.unwrap_or((index, home.slot(), home.slot()));
                    let local = materialized_local(self.proto, self.facts, temp);
                    let HirStmt::Assign(assign) = stmt else {
                        unreachable!()
                    };
                    *stmt = HirStmt::LocalDecl(Box::new(HirLocalDecl {
                        bindings: vec![local],
                        values: assign.values.clone(),
                        initializer_merge_transaction: None,
                    }));
                    run = Some((start, base, next + 1));
                } else {
                    run = None;
                }
            }
            let mut valid = true;
            for_each_nested_block_mut(stmt, &mut |child| valid &= self.block(child));
            if !valid {
                return false;
            }
        }
        if !scopes.is_empty() {
            let old = std::mem::take(&mut block.stmts);
            let mut remaining = old.into_iter().enumerate().peekable();
            while let Some((index, stmt)) = remaining.next() {
                if let Some(&end) = scopes.get(&index) {
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
        }
        true
    }
}

fn collect_candidates(
    block: &HirBlock,
    facts: &ProtoPromotionFacts,
    read: &BTreeSet<TempId>,
    writes: &BTreeMap<TempId, usize>,
    debug_hints: &[Option<String>],
    cursor: &mut usize,
    candidates: &mut BTreeMap<usize, NilCandidate>,
) {
    for (index, stmt) in block.stmts.iter().enumerate() {
        if let Some(temps) = original_nil_write(stmt, facts, read, writes) {
            let existing = temps
                .iter()
                .all(|temp| debug_hints.get(temp.index()).is_none_or(Option::is_none))
                .then(|| block.stmts.get(index + 1))
                .flatten()
                .and_then(|next| {
                    crate::hir::simplify::carried_locals::adjacent_nil_initializer_bindings(
                        temps, next, facts,
                    )
                });
            candidates.insert(
                *cursor,
                NilCandidate {
                    temps: temps.to_vec(),
                    existing,
                },
            );
        }
        *cursor += 1;
        crate::hir::visit::for_each_nested_block(stmt, &mut |child| {
            collect_candidates(child, facts, read, writes, debug_hints, cursor, candidates);
        });
    }
}

fn original_nil_write<'a>(
    stmt: &HirStmt,
    facts: &'a ProtoPromotionFacts,
    read: &BTreeSet<TempId>,
    writes: &BTreeMap<TempId, usize>,
) -> Option<&'a [TempId]> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let HirLValue::Temp(first) = assign.targets.first()? else {
        return None;
    };
    let temps = facts.nil_write_temps(*first)?;
    if assign.values.tail.is_some()
        || assign.targets.len() != temps.len()
        || assign.values.fixed.len() != temps.len()
        || !assign
            .values
            .fixed
            .iter()
            .all(|value| matches!(value, HirExpr::Nil))
    {
        return None;
    }
    let base = facts.trusted_temp_home_slot(*first)?.slot();
    for (offset, (&temp, target)) in temps.iter().zip(&assign.targets).enumerate() {
        let home = facts.trusted_temp_home_slot(temp)?;
        let definition_homes = facts.complete_temp_definition_write_homes(temp);
        if *target != HirLValue::Temp(temp)
            || read.contains(&temp)
            || writes.get(&temp) != Some(&1)
            || home.slot() != base + offset
            || definition_homes.len() != 1
            || !definition_homes.contains(&home)
        {
            // 候选拒绝[ProofIncomplete]：不能漏掉原批次成员、捕获、合并身份或隐藏 MOVE 写。
            return None;
        }
    }
    Some(temps)
}

fn materialize(
    block: &mut HirBlock,
    replacements: &BTreeMap<usize, NilMaterialization>,
    cursor: &mut usize,
) {
    let old = std::mem::take(&mut block.stmts);
    for mut stmt in old {
        let replacement = replacements.get(cursor);
        if let Some(NilMaterialization::Declare(locals)) = replacement {
            let HirStmt::Assign(assign) = &stmt else {
                unreachable!("original nil write must remain an assignment");
            };
            stmt = HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: locals.clone(),
                values: assign.values.clone(),
                initializer_merge_transaction: None,
            }));
        }
        *cursor += 1;
        for_each_nested_block_mut(&mut stmt, &mut |child| {
            materialize(child, replacements, cursor)
        });
        if !matches!(replacement, Some(NilMaterialization::Existing)) {
            block.stmts.push(stmt);
        }
    }
}
