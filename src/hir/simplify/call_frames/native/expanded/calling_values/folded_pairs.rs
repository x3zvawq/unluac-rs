//! 配对选择参数为 false 时仍执行的读取及固定双返回。
//! 比较被编译器折叠后，原真值谓词、true 叶写和 false/nil COPY 仍须完整保留。

use super::*;
use crate::transformer::InstrRef;

pub(super) fn candidate(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    window: &[&HirStmt],
    start: usize,
    sink: usize,
    original_nil: &BTreeSet<LocalId>,
) -> Option<pairs::Candidate> {
    let (update, choice, empty, result, tail) = match window {
        [update, choice, result, tail] => (*update, *choice, None, *result, *tail),
        [update, choice, empty, result, tail] => (*update, *choice, Some(*empty), *result, *tail),
        _ => return None,
    };
    let read = reading::match_read(facts, update, choice)?;
    let reading::Value::Used {
        local: read_item,
        temp: read_value,
    } = read.value
    else {
        return None;
    };
    let (first, HirExpr::LogicalAnd(and)) = scalar_local(result)? else {
        return None;
    };
    let HirExpr::LocalRef(flag) = and.lhs else {
        return None;
    };
    let (second, HirExpr::LocalRef(item)) = scalar_local(tail)? else {
        return None;
    };
    let source = |instr| crate::hir::HirSourceSite {
        proto: proto.id,
        instr,
    };
    let frame = facts.branch_value_frame_at(source(read.end))?;
    let [value] = frame.results.as_slice() else {
        return None;
    };
    let (input, flag_home) = facts.original_truthy_input(source(read.end))?;
    let (truthy, falsy) = facts.original_branch_routes(source(read.end))?;
    let copied = facts.value_result_copy_at(source(frame.end))?;
    if !pairs::scalar_write(result)
        || !pairs::scalar_write(tail)
        || and.rhs != HirExpr::Boolean(true)
        || *item != read_item
        || frame.predicates != [read.end]
        || frame.begin != read.end
        || truthy.index() != read.end.index() + 1
        || falsy.index() != read.end.index() + 3
        || frame.end.index() != read.end.index() + 4
        || facts.promoted_local_for_temp(input) != Some(flag)
        || facts.trusted_local_home_slot(flag) != Some(flag_home)
        || facts.promoted_local_for_temp(value.value) != Some(first)
        || value.incoming.len() != 2
        || !value.incoming.iter().any(|incoming| {
            incoming.source == Some(truthy)
                && incoming.literal == Some(Literal::Boolean(true))
                && incoming.terminal_write
        })
        || !value.incoming.iter().any(|incoming| {
            incoming.source == Some(falsy)
                && incoming.copy == Some((HirBinding::Temp(input), flag_home))
                && incoming.terminal_write
        })
        || copied.source != Some(read_value)
        || copied.source_home != read.home
        || facts.promoted_local_for_temp(copied.target) != Some(second)
        || read.home.slot() != value.home.slot() + 2
        || copied.target_home.slot() != value.home.slot() + 1
        || flag_home.slot() >= value.home.slot()
        || read
            .inputs
            .iter()
            .any(|home| home.slot() >= value.home.slot())
    {
        return None;
    }
    if let Some(empty) = empty {
        let HirStmt::LocalDecl(decl) = empty else {
            return None;
        };
        if decl.bindings != [first]
            || !decl.values.is_empty()
            || !pairs::scalar_write(empty)
            || !facts.is_phi_carrier_temp(value.value)
            || original_nil.contains(&first)
        {
            return None;
        }
    }
    Some(pairs::Candidate {
        start,
        sink,
        source: read.source,
        end: InstrRef(frame.end.index() + 1),
        item_pc: read.end_pc,
        base: value.home,
        results: [first, second],
        result_values: [value.value, copied.target],
        argument: None,
        flag,
        item: read_item,
        item_value: read_value,
        counter: read.counter,
        index: read.index,
        table: read.table,
        increment: read.increment,
        key: read.key,
        hit: read.hit,
        fallback: None,
    })
}
