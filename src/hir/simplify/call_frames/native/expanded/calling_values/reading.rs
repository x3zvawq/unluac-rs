//! 配对一次捕获计数更新及随后的字面量或表读取。
//! 合流值与无读取的互斥写入分别消费 Promotion 事实，调用者再连接参数和返回包。

use super::*;
use crate::transformer::InstrRef;

#[derive(Debug, PartialEq, Eq)]
pub(super) enum Value {
    Used {
        local: LocalId,
        temp: TempId,
    },
    Unused {
        bindings: [HirBinding; 2],
        temps: [TempId; 2],
    },
}

#[derive(Debug, PartialEq, Eq)]
pub(super) struct Read {
    pub source: crate::hir::HirSourceSite,
    pub begin: InstrRef,
    pub end: InstrRef,
    pub end_pc: u32,
    pub value: Value,
    pub home: HomeSlotKey,
    pub counter: LocalId,
    pub index: LocalId,
    pub table: LocalId,
    pub inputs: [HomeSlotKey; 3],
    pub increment: i64,
    pub key: i64,
    pub hit: Literal,
}

enum Destination {
    Merged(LocalId),
    Separate([HirBinding; 2]),
}

fn arm(block: &HirBlock) -> Option<(HirBinding, &HirExpr)> {
    let [stmt] = block.stmts.as_slice() else {
        return None;
    };
    pairs::scalar_write(stmt)
        .then(|| scalar_binding(stmt))
        .flatten()
}

fn binding_matches(facts: &ProtoPromotionFacts, binding: HirBinding, temp: TempId) -> bool {
    match binding {
        HirBinding::Temp(actual) => actual == temp,
        HirBinding::Local(local) => facts.promoted_local_for_temp(temp) == Some(local),
        _ => false,
    }
}

pub(super) fn match_read(
    facts: &ProtoPromotionFacts,
    update: &HirStmt,
    choice: &HirStmt,
) -> Option<Read> {
    if !matches!(update, HirStmt::Assign(_)) || !pairs::scalar_write(update) {
        return None;
    }
    let (counter, HirExpr::Binary(add)) = scalar_local(update)? else {
        return None;
    };
    let (test, hit, lookup, destination) = if let HirStmt::If(branch) = choice {
        let mut condition = &branch.cond;
        let mut inverted = false;
        while let HirExpr::Unary(unary) = condition {
            if unary.op != crate::hir::HirUnaryOpKind::Not || unary.source_site.is_some() {
                return None;
            }
            inverted = !inverted;
            condition = &unary.expr;
        }
        let HirExpr::Binary(test) = condition else {
            return None;
        };
        if branch.predicate_source != test.source_site {
            return None;
        }
        let left = arm(&branch.then_block)?;
        let right = arm(branch.else_block.as_ref()?)?;
        let (hit, lookup) = if inverted {
            (right, left)
        } else {
            (left, right)
        };
        let HirExpr::TableAccess(access) = lookup.1 else {
            return None;
        };
        (
            test.as_ref(),
            hit.1,
            access.as_ref(),
            Destination::Separate([hit.0, lookup.0]),
        )
    } else {
        if !pairs::scalar_write(choice) {
            return None;
        }
        let (item, HirExpr::LogicalOr(choice)) = scalar_local(choice)? else {
            return None;
        };
        let HirExpr::LogicalAnd(selected) = &choice.lhs else {
            return None;
        };
        let HirExpr::Binary(test) = &selected.lhs else {
            return None;
        };
        let HirExpr::TableAccess(lookup) = &choice.rhs else {
            return None;
        };
        (
            test.as_ref(),
            &selected.rhs,
            lookup.as_ref(),
            Destination::Merged(item),
        )
    };
    let HirExpr::LocalRef(index) = test.lhs else {
        return None;
    };
    let HirExpr::LocalRef(table) = lookup.base else {
        return None;
    };
    let HirOperationSources::Single(lookup_site) = lookup.sources else {
        return None;
    };
    let source = add.source_site?;
    let predicate = test.source_site?;
    let frame = facts.branch_value_frame_at(predicate)?;
    let hit = Literal::from_expr(hit)?;
    let increment = crate::hir::luau_inlining::small_integer(&add.rhs)?;
    let key = crate::hir::luau_inlining::small_integer(&test.rhs)?;
    let (truthy, falsy) = facts.original_branch_routes(predicate)?;
    let counter_home = facts.trusted_local_home_slot(counter)?;
    let index_home = facts.trusted_local_home_slot(index)?;
    let table_home = facts.trusted_local_home_slot(table)?;
    let add_layout = facts.native_binary_layout(add)?;
    let test_layout = facts.native_binary_layout(test)?;
    let lookup_layout = facts.native_table_read_layout(lookup)?;
    // 候选拒绝[ProofIncomplete:ReadFrame]：计数更新、原比较和两臂读取必须是
    // 同一完整分支窗口，当前输入绑定与原操作数 home 也须逐项一致。
    if add.op != HirBinaryOpKind::Add
        || add.lhs != HirExpr::LocalRef(counter)
        || test.op != HirBinaryOpKind::Eq
        || lookup.key != HirExpr::LocalRef(index)
        || matches!(hit, Literal::Nil | Literal::Boolean(false))
        || frame.predicates != [predicate.instr]
        || frame.begin > source.instr
        || predicate.instr.index() != source.instr.index() + 1
        || truthy.index() != predicate.instr.index() + 1
        || falsy != lookup_site.instr
        || lookup_site.instr.index() != predicate.instr.index() + 3
        || frame.end.index() != predicate.instr.index() + 4
        || add_layout.lhs != Some(counter_home)
        || add_layout.rhs.is_some()
        || facts.operation_result_home(source) != Some(counter_home)
        || test_layout.lhs != Some(index_home)
        || test_layout.rhs.is_some()
        || lookup_layout.base != table_home
        || lookup_layout.key != Some(index_home)
    {
        return None;
    }
    let (value, home) = match destination {
        Destination::Merged(item) => {
            let [value] = frame.results.as_slice() else {
                return None;
            };
            if frame.unread.is_some()
                || value.incoming.len() != 2
                || !value.incoming.iter().any(|incoming| {
                    incoming.source == Some(truthy)
                        && incoming.literal.as_ref() == Some(&hit)
                        && incoming.terminal_write
                })
                || !value.incoming.iter().any(|incoming| {
                    incoming.source == Some(falsy)
                        && incoming.terminal_write
                        && facts.operation_result_temp(lookup_site) == Some(incoming.value)
                })
                || facts.promoted_local_for_temp(value.value) != Some(item)
            {
                return None;
            }
            (
                Value::Used {
                    local: item,
                    temp: value.value,
                },
                value.home,
            )
        }
        Destination::Separate(bindings) => {
            let value = frame.unread.as_ref()?;
            let left = value.sources.iter().position(|&site| site == truthy)?;
            let right = value.sources.iter().position(|&site| site == falsy)?;
            let temps = [value.writes[left], value.writes[right]];
            // 候选拒绝[ProofIncomplete:UnreadBranch]：两笔原写保持各自身份，
            // 不把当前同槽声明或临时变量当成不存在的合流值。
            if !frame.results.is_empty()
                || value.literals[left].as_ref() != Some(&hit)
                || facts.operation_result_temp(lookup_site) != Some(temps[1])
                || !bindings
                    .iter()
                    .zip(temps)
                    .all(|(&binding, temp)| binding_matches(facts, binding, temp))
            {
                return None;
            }
            (Value::Unused { bindings, temps }, value.home)
        }
    };
    Some(Read {
        source,
        begin: frame.begin,
        end: frame.end,
        end_pc: frame.end_pc?,
        value,
        home,
        counter,
        index,
        table,
        inputs: [counter_home, index_home, table_home],
        increment,
        key,
        hit,
    })
}
