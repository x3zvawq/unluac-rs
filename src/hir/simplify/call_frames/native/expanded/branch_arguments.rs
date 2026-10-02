//! 将完整布尔参数分支投影为未发布的短路表达式。
//! 复用当前语句树和源码帧坐标；读写只索引一次，原预写必须由同批外层 CALL 消费。

use super::value_uses::ValueUses;
use super::*;

pub(super) fn prepare(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
) -> Option<(HirProto, Vec<(usize, usize)>)> {
    let uses = ValueUses::new(proto);
    let points = &uses.points;
    let tree = &uses.tree;
    let count = uses.count;
    let original_nil = facts
        .nil_write_groups()
        .flatten()
        .filter_map(|temp| facts.promoted_local_for_temp(*temp))
        .collect::<BTreeSet<_>>();
    let mut replacements = BTreeMap::new();
    let mut removed = vec![false; count];
    let mut obligations = Vec::new();
    let mut pending = vec![tree.root_block()];
    while let Some(block) = pending.pop() {
        let ids = tree.block(block);
        let statements = ids
            .iter()
            .map(|id| points[id.index()].1)
            .collect::<Vec<_>>();
        let positions = ids
            .iter()
            .map(|id| points[id.index()].0)
            .collect::<Vec<_>>();
        let mut definitions = BTreeMap::<LocalId, Vec<usize>>::new();
        for (index, &id) in ids.iter().enumerate() {
            pending.extend(tree.stmt(id).children.iter().copied());
            // 仅当前块上的无条件定义结束旧版本；单臂写入不能截断后继读取。
            if let Some((local, _)) = scalar_local(statements[index]) {
                definitions.entry(local).or_default().push(index);
            }
        }
        let mut writes = BTreeMap::new();
        for (index, stmt) in statements.iter().enumerate() {
            if let Some((local, _)) = scalar_local(stmt) {
                writes.insert(local, index);
            }
            let HirStmt::If(branch) = stmt else {
                continue;
            };
            let candidate = (|| {
                // FASTCALL fallback 的 callee 查找可夹在合流与 CALL 之间，仍留在
                // 原位置供 FrameBuilder 在参数之后消费；不越过其它语句找调用。
                let call_index = index
                    + 1
                    + usize::from(
                        statements
                            .get(index + 1)
                            .is_some_and(|stmt| scalar_local(stmt).is_some()),
                    );
                let HirStmt::CallStmt(sink) = statements.get(call_index)? else {
                    return None;
                };
                let (argument, target, prewrite) = sink
                    .call
                    .args
                    .fixed
                    .iter()
                    .enumerate()
                    .find_map(|(argument, expr)| {
                        let HirExpr::LocalRef(target) = expr else {
                            return None;
                        };
                        Some((
                            argument,
                            *target,
                            facts.boolean_argument_prewrite(&sink.call, argument)?,
                        ))
                    })?;
                let initial_local = facts.promoted_local_for_temp(prewrite.initial)?;
                let initial = *writes.get(&initial_local)?;
                let (value, branch_writes) = branch_argument_value(branch, target, initial_local)?;
                // 同一 Local 可承接多个原值版本；这里只统计预写至下一次覆盖之间的
                // 读取，不能借更早/更晚版本的消费者拒绝本次唯一参数。索引在上方一次建立。
                let end = definitions
                    .get(&target)
                    .and_then(|sites| {
                        sites
                            .get(sites.partition_point(|&site| site <= call_index))
                            .copied()
                    })
                    .map(|end| positions[end] + 1)
                    .unwrap_or(count);
                let begin = if target == initial_local {
                    initial
                } else {
                    index
                };
                // 覆盖语句的 RHS 仍读取旧版本，计数必须包括该语句头。
                let reads = uses.reads(target, positions[begin], end);
                if prewrite.initial_value
                    || !prewrite.reference_uncaptured
                    || facts.trusted_local_home_slot(initial_local) != Some(prewrite.home)
                    || facts.trusted_local_home_slot(target) != Some(prewrite.home)
                    || !matches!(
                        scalar_local(statements[initial]),
                        Some((_, HirExpr::Boolean(false)))
                    )
                    || reads != 1
                    || proto.local_debug_hints[target.index()].is_some()
                    || proto.local_debug_scopes[target.index()].is_some()
                    || proto.inline_dispositions.local(target).must_preserve()
                    || proto.local_debug_hints[initial_local.index()].is_some()
                    || proto.local_debug_scopes[initial_local.index()].is_some()
                    || proto
                        .inline_dispositions
                        .local(initial_local)
                        .must_preserve()
                {
                    // 候选拒绝[LayerBoundary]：当前投影只含无捕获、无公开身份的 false 预写；
                    // 保留 binding 必须由其身份 owner 证明。
                    return None;
                }
                let empty = if target != initial_local {
                    let empty = index.checked_sub(1)?;
                    // 独立 phi 的空声明仅承接本树结果；原 LOADNIL、后继复用或其它读
                    // 都不能随树一起退休。初值本身仍由原预写 local 在帧入口提供。
                    if facts.promoted_local_for_temp(prewrite.result) != Some(target)
                        || original_nil.contains(&target)
                        || !matches!(statements[empty], HirStmt::LocalDecl(decl)
                        if decl.bindings == [target] && decl.values.is_empty()
                            && decl.initializer_merge_transaction.is_none())
                        || uses.writes(target) != branch_writes + 1
                    {
                        return None;
                    }
                    Some(empty)
                } else {
                    None
                };
                // CALL 原参数 phi 已配对 initial；当前 HIR 的目标写和唯一读保持该
                // 数据流。carrier 合并后旧 phi 的首次提升 LocalId 不再是当前 binding。
                let mut call = sink.clone();
                call.call.args.fixed[argument] = value;
                Some((initial, call_index, call, empty))
            })();
            // 非候选控制树仍可能改写旧 local；不能跨树借用之前的常量定义。
            writes.clear();
            if let Some((initial, call_index, call, empty)) = candidate {
                replacements.insert(positions[call_index], call);
                for node in tree.stmt(ids[index]).range.clone() {
                    removed[points[node].0] = true;
                }
                if let Some(empty) = empty {
                    removed[positions[empty]] = true;
                }
                obligations.push((positions[initial], positions[call_index]));
            }
        }
    }
    if replacements.is_empty() {
        return None;
    }
    let mut draft = proto.clone();
    prefix::coordinates::visit_mut(&mut draft.body, &mut 0, &mut |index, _, stmt| {
        if let Some(call) = replacements.remove(&index) {
            *stmt = HirStmt::CallStmt(call);
        }
        Some(())
    })?;
    prefix::coordinates::compact(&mut draft.body, &removed, &mut 0);
    let mut retired = 0;
    let coordinates = removed
        .iter()
        .enumerate()
        .map(|(index, &removed)| {
            let mapped = index - retired;
            retired += usize::from(removed);
            mapped
        })
        .collect::<Vec<_>>();
    for (initial, call) in &mut obligations {
        *initial = coordinates[*initial];
        *call = coordinates[*call];
    }
    Some((draft, obligations))
}

/// 每个比较保留一次，假臂必须写 false 或读取已配对的 false 预写；不使用
/// 路径值域删掉任何检查。条件真臂中的准备只能来自原树，不能从外层吸入。
fn branch_argument_value(
    branch: &crate::hir::common::HirIf,
    target: LocalId,
    initial: LocalId,
) -> Option<(HirExpr, usize)> {
    use crate::hir::common::{HirBinaryOpKind, HirLogicalExpr};
    let HirExpr::Binary(binary) = &branch.cond else {
        return None;
    };
    if branch.preserves_empty_test
        || !matches!(
            binary.op,
            HirBinaryOpKind::Eq
                | HirBinaryOpKind::Lt
                | HirBinaryOpKind::Le
                | HirBinaryOpKind::Gt
                | HirBinaryOpKind::Ge
        )
    {
        return None;
    }
    let false_writes = match &branch.else_block {
        None if target == initial => 0,
        Some(block) => {
            let [stmt @ HirStmt::Assign(_)] = block.stmts.as_slice() else {
                return None;
            };
            let (written, value) = scalar_local(stmt)?;
            if written != target
                || !(matches!(value, HirExpr::Boolean(false))
                    || *value == HirExpr::LocalRef(initial))
            {
                return None;
            }
            1
        }
        _ => return None,
    };
    let (rhs, writes) = match branch.then_block.stmts.as_slice() {
        [HirStmt::If(nested)] => branch_argument_value(nested, target, initial)?,
        [stmt @ HirStmt::Assign(_)] => {
            let (written, value) = scalar_local(stmt)?;
            if written != target {
                return None;
            }
            (value.clone(), 1)
        }
        _ => return None,
    };
    Some((
        HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
            preserves_boolean_prewrite: false,
            lhs: branch.cond.clone(),
            rhs,
        })),
        writes + false_writes,
    ))
}
