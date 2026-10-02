//! 核对短路调用的最终函数参数解析与捕获读取体。
//! occurrence 连接实际闭包，源码声明和写入性质决定 Luau 是否重发原参数 COPY。

use super::*;
use crate::hir::{HirBinding, HirCaptureMode, HirExpr, HirModule, HirProto, LocalId};
use crate::hir::{HirLuauCallableArgument, HirLuauCallableSource, HirRequiredLuauInlining};

fn literal(actual: &AstExpr, expected: &HirExpr) -> bool {
    if let (Some(actual), Some(expected)) = (
        counter_repeat::integer(actual),
        crate::hir::luau_inlining::small_integer(expected),
    ) {
        return actual == expected;
    }
    match (actual, expected) {
        (AstExpr::Nil, HirExpr::Nil) => true,
        (AstExpr::Boolean(a), HirExpr::Boolean(b)) => a == b,
        (AstExpr::Integer(a), HirExpr::Integer(b)) => a == b,
        (AstExpr::Number(a), HirExpr::Number(b)) => a.to_bits() == b.to_bits(),
        (AstExpr::String(a), HirExpr::String(b)) => a == b,
        _ => false,
    }
}

pub(super) fn body(func: &AstFunctionExpr, proto: &HirProto) -> bool {
    if func.function != proto.id
        || func.params != proto.params
        || func.is_vararg
        || func.named_vararg.is_some()
        || !func.captured_bindings.is_empty()
        || !func.captured_params.is_empty()
        || !func.capture_write_names.is_empty()
    {
        return false;
    }
    if let Some(template) = crate::hir::luau_inlining::observed_value_template(proto) {
        return observed_values::body(func, &template);
    }
    if let Some(template) = crate::hir::luau_inlining::calling_shared_value(proto) {
        let [AstStmt::LocalDecl(decl), AstStmt::Return(ret)] = func.body.stmts.as_slice() else {
            return false;
        };
        let ([binding], [AstExpr::Call(call)]) = (decl.bindings.as_slice(), decl.values.as_slice())
        else {
            return false;
        };
        let [AstExpr::LogicalAnd(final_)] = ret.values.as_slice() else {
            return false;
        };
        // Readability 可以重关联连续的 and；按原求值顺序核对三个叶子，
        // 不要求 HIR 的括号方向，也不接受被删去或新增的比较。
        let (enabled, comparison, check) = match (&final_.lhs, &final_.rhs) {
            (AstExpr::LogicalAnd(left), right) => (&left.lhs, &left.rhs, right),
            (left, AstExpr::LogicalAnd(right)) => (left, &right.lhs, &right.rhs),
            _ => return false,
        };
        let AstExpr::Binary(compare) = comparison else {
            return false;
        };
        let AstExpr::Binary(check) = check else {
            return false;
        };
        let AstExpr::LogicalOr(or) = &compare.rhs else {
            return false;
        };
        let AstExpr::LogicalAnd(pick) = &or.lhs else {
            return false;
        };
        let param = |index| AstExpr::Var(AstNameRef::Param(func.params[index]));
        let item = AstExpr::Var(AstNameRef::Local(template.item));
        return binding.id == AstBindingRef::Local(template.item)
            && call.callee == param(2)
            && call.method_key.is_none()
            && call.required_luau_inlining.is_none()
            && call.args == [AstExpr::String(template.tag.clone())]
            && *enabled == param(0)
            && compare.op == AstBinaryOpKind::Eq
            && compare.lhs == param(1)
            && pick.lhs == item
            && literal(&pick.rhs, template.hit)
            && literal(&or.rhs, template.fallback)
            && check.op == AstBinaryOpKind::Eq
            && check.lhs == item
            && check.rhs == param(1);
    }
    let pair = crate::hir::luau_inlining::calling_read_pair(proto);
    let Some(fallback) = pair
        .map(|(_, fallback)| fallback)
        .or_else(|| crate::hir::luau_inlining::calling_value_fallback(proto))
    else {
        return false;
    };
    if let Some((item, _)) = pair {
        let [AstStmt::LocalDecl(decl), AstStmt::Return(ret)] = func.body.stmts.as_slice() else {
            return false;
        };
        let ([binding], [AstExpr::Call(call)]) = (decl.bindings.as_slice(), decl.values.as_slice())
        else {
            return false;
        };
        let [AstExpr::LogicalAnd(and), second] = ret.values.as_slice() else {
            return false;
        };
        let AstExpr::Binary(compare) = &and.rhs else {
            return false;
        };
        let AstExpr::LogicalOr(or) = &compare.rhs else {
            return false;
        };
        let AstExpr::LogicalAnd(pick) = &or.lhs else {
            return false;
        };
        let param = |index| AstExpr::Var(AstNameRef::Param(func.params[index]));
        return binding.id == AstBindingRef::Local(item)
            && call.callee == param(2)
            && call.args.is_empty()
            && call.method_key.is_none()
            && call.required_luau_inlining.is_none()
            && and.lhs == param(0)
            && compare.op == AstBinaryOpKind::Eq
            && compare.lhs == param(1)
            && pick.lhs == param(3)
            && pick.rhs == AstExpr::Var(AstNameRef::Local(item))
            && *second == pick.rhs
            && literal(&or.rhs, fallback);
    }
    let [AstStmt::Return(ret)] = func.body.stmts.as_slice() else {
        return false;
    };
    let [AstExpr::LogicalAnd(and)] = ret.values.as_slice() else {
        return false;
    };
    let AstExpr::Binary(compare) = &and.rhs else {
        return false;
    };
    let AstExpr::LogicalOr(or) = &compare.rhs else {
        return false;
    };
    let AstExpr::Call(call) = &or.lhs else {
        return false;
    };
    let param = |index| AstExpr::Var(AstNameRef::Param(func.params[index]));
    and.lhs == param(0)
        && compare.op == AstBinaryOpKind::Eq
        && compare.lhs == param(1)
        && call.callee == param(2)
        && call.args.is_empty()
        && call.method_key.is_none()
        && call.required_luau_inlining.is_none()
        && literal(&or.rhs, fallback)
}

fn returned(block: &AstBlock) -> Option<&AstExpr> {
    let [AstStmt::Return(ret)] = block.stmts.as_slice() else {
        return None;
    };
    let [value] = ret.values.as_slice() else {
        return None;
    };
    Some(value)
}

fn reader(
    func: &AstFunctionExpr,
    dependency: &HirLuauCallableArgument,
    hir: &HirModule,
    written: &BTreeSet<LocalId>,
) -> bool {
    let Some(proto) = hir.protos.get(dependency.child.index()) else {
        return false;
    };
    let counted = crate::hir::luau_inlining::captured_read_template(proto);
    let traced = crate::hir::luau_inlining::traced_read_template(proto);
    let checked = crate::hir::luau_inlining::checked_read_template(proto);
    let Some(counter) = counted
        .as_ref()
        .map(|template| template.counter)
        .or_else(|| traced.as_ref().map(|template| template.trace))
        .or_else(|| checked.as_ref().map(|template| template.counter))
    else {
        return false;
    };
    if func.function != dependency.child
        || func.params != proto.params
        || func.is_vararg
        || func.named_vararg.is_some()
        || !func.captured_params.is_empty()
        || dependency.captures.len() != if checked.is_some() { 1 } else { 3 }
        || dependency
            .source
            .declared()
            .is_some_and(|local| written.contains(&local))
    {
        return false;
    }
    let mut captures = BTreeSet::new();
    let mut writes = BTreeSet::new();
    for (index, capture) in dependency.captures.iter().enumerate() {
        let HirBinding::Local(local) = capture.binding else {
            return false;
        };
        let counter = index == counter.index();
        if capture.mode
            != if counter {
                HirCaptureMode::ByReference
            } else {
                HirCaptureMode::ByValue
            }
            || !counter && written.contains(&local)
        {
            return false;
        }
        captures.insert(AstBindingRef::Local(local));
        if counter {
            writes.insert(AstNameRef::Local(local));
        }
    }
    if func.captured_bindings != captures || func.capture_write_names != writes {
        return false;
    }
    if let HirLuauCallableSource::Expression { site, creation } = dependency.source
        && (func.source_site != Some(site) || func.creation != Some(creation))
    {
        return false;
    }
    if let Some(template) = checked {
        return checked_reads::body(func, &template);
    }
    if let Some(template) = traced {
        return observed_values::reader(func, &template);
    }
    let Some(template) = counted else {
        return false;
    };
    let (update, branch, tail) = match func.body.stmts.as_slice() {
        [AstStmt::Assign(update), AstStmt::If(branch)] => (update, branch, None),
        [
            AstStmt::Assign(update),
            AstStmt::If(branch),
            AstStmt::Return(tail),
        ] => (update, branch, Some(tail)),
        _ => return false,
    };
    let upvalue = |id| AstExpr::Var(AstNameRef::Upvalue(id));
    let [AstExpr::Binary(add)] = update.values.as_slice() else {
        return false;
    };
    if update.targets != [AstLValue::Name(AstNameRef::Upvalue(template.counter))]
        || add.op != AstBinaryOpKind::Add
        || add.lhs != upvalue(template.counter)
        || counter_repeat::integer(&add.rhs) != Some(template.increment)
    {
        return false;
    }
    let mut condition = &branch.cond;
    let mut inverted = false;
    while let AstExpr::Unary(unary) = condition {
        if unary.op != AstUnaryOpKind::Not || unary.original_operation {
            return false;
        }
        inverted = !inverted;
        condition = &unary.expr;
    }
    let AstExpr::Binary(compare) = condition else {
        return false;
    };
    match compare.op {
        AstBinaryOpKind::Eq => {}
        _ => return false,
    }
    if compare.lhs != upvalue(template.index)
        || counter_repeat::integer(&compare.rhs) != Some(template.key)
    {
        return false;
    }
    let Some(left) = returned(&branch.then_block) else {
        return false;
    };
    let right = match (&branch.else_block, tail) {
        (Some(block), None) => returned(block),
        (None, Some(ret)) => match ret.values.as_slice() {
            [value] => Some(value),
            _ => None,
        },
        _ => None,
    };
    let Some(right) = right else { return false };
    let (hit, lookup) = if inverted {
        (right, left)
    } else {
        (left, right)
    };
    literal(hit, &template.hit)
        && matches!(lookup, AstExpr::IndexAccess(access)
        if access.base == upvalue(template.table) && access.index == upvalue(template.index))
}

pub(super) struct Dependencies<'a> {
    hir: &'a HirModule,
    occurrences: BTreeMap<crate::hir::HirSourceSite, &'a HirLuauCallableArgument>,
    readers: BTreeMap<LocalId, &'a HirLuauCallableArgument>,
    declared: BTreeSet<LocalId>,
    pairs: BTreeSet<crate::hir::HirSourceSite>,
    nil_guards: BTreeSet<crate::hir::HirSourceSite>,
    shared: BTreeSet<crate::hir::HirSourceSite>,
    observed: BTreeSet<crate::hir::HirSourceSite>,
}

impl<'a> Dependencies<'a> {
    pub fn new(requirements: &[&'a HirRequiredLuauInlining], hir: &'a HirModule) -> Option<Self> {
        let mut occurrences = BTreeMap::new();
        let mut readers: BTreeMap<LocalId, &'a HirLuauCallableArgument> = BTreeMap::new();
        let mut pairs = BTreeSet::new();
        let mut nil_guards = BTreeSet::new();
        let mut shared = BTreeSet::new();
        let mut observed = BTreeSet::new();
        let mut all_occurrences = BTreeSet::new();
        for requirement in requirements {
            let pair = matches!(
                requirement.body,
                HirLuauInliningBody::CallingReadPair { .. }
            );
            let is_shared = matches!(
                requirement.body,
                HirLuauInliningBody::CallingSharedValue { .. }
            );
            let calling = pair
                || is_shared
                || matches!(
                    requirement.body,
                    HirLuauInliningBody::CallingObservedValue { .. }
                )
                || matches!(requirement.body, HirLuauInliningBody::CallingValue { .. });
            let sites = requirement
                .occurrences
                .iter()
                .copied()
                .collect::<BTreeSet<_>>();
            if requirement
                .callable_arguments
                .keys()
                .any(|site| !sites.contains(site))
                || requirement
                    .nil_guards
                    .iter()
                    .any(|site| !sites.contains(site))
                || !calling
                    && (!requirement.callable_arguments.is_empty()
                        || !requirement.nil_guards.is_empty())
                || (pair
                    || is_shared
                    || matches!(
                        requirement.body,
                        HirLuauInliningBody::CallingObservedValue { .. }
                    ))
                    && !requirement.nil_guards.is_empty()
            {
                return None;
            }
            for site in &requirement.occurrences {
                if !all_occurrences.insert(*site) {
                    return None;
                }
                if !calling {
                    continue;
                }
                if is_shared {
                    shared.insert(*site);
                }
                if matches!(
                    requirement.body,
                    HirLuauInliningBody::CallingObservedValue { .. }
                ) {
                    observed.insert(*site);
                }
                let nil = requirement.nil_guards.contains(site);
                if nil {
                    nil_guards.insert(*site);
                }
                let Some(dependency) = requirement.callable_arguments.get(site) else {
                    if nil {
                        continue;
                    }
                    return None;
                };
                if pair {
                    pairs.insert(*site);
                }
                if dependency.parameter != 2
                    || !pair && dependency.pair_constant.is_some()
                    || occurrences.insert(*site, dependency).is_some()
                {
                    return None;
                }
                match dependency.source {
                    HirLuauCallableSource::Declared(local) => {
                        if readers.insert(local, dependency).is_some_and(|old| {
                            old.child != dependency.child || old.captures != dependency.captures
                        }) {
                            return None;
                        }
                    }
                    HirLuauCallableSource::Expression { site, .. } => {
                        if !is_shared || nil || site.proto != requirement.owner {
                            return None;
                        }
                    }
                }
            }
        }
        Some(Self {
            hir,
            occurrences,
            readers,
            declared: BTreeSet::new(),
            pairs,
            nil_guards,
            shared,
            observed,
        })
    }

    pub fn contains(&self, local: LocalId) -> bool {
        self.readers.contains_key(&local)
    }

    pub fn declaration(
        &mut self,
        local: LocalId,
        func: &AstFunctionExpr,
        hir: &HirModule,
        written: &BTreeSet<LocalId>,
    ) -> bool {
        self.readers
            .get(&local)
            .is_some_and(|dependency| reader(func, dependency, hir, written))
            && self.declared.insert(local)
    }

    pub fn arguments(&self, call: &AstCallExpr, written: &BTreeSet<LocalId>) -> bool {
        let Some(site) = call.required_luau_inlining else {
            return false;
        };
        if self.nil_guards.contains(&site) {
            return match (self.occurrences.get(&site), call.args.as_slice()) {
                (
                    None,
                    [
                        AstExpr::Nil,
                        AstExpr::Var(AstNameRef::Local(value)),
                        AstExpr::Nil,
                    ],
                ) => written.contains(value),
                (
                    Some(dependency),
                    [
                        AstExpr::Nil,
                        AstExpr::Var(AstNameRef::Local(value)),
                        AstExpr::Var(AstNameRef::Local(reader)),
                    ],
                ) => {
                    Some(*reader) == dependency.source.declared()
                        && self.declared.contains(reader)
                        && written.contains(value)
                        && !written.contains(reader)
                }
                _ => false,
            };
        }
        let Some(dependency) = self.occurrences.get(&site) else {
            return false;
        };
        if matches!(dependency.source, HirLuauCallableSource::Expression { .. }) {
            let Some(AstExpr::FunctionExpr(func)) = call.args.get(dependency.parameter) else {
                return false;
            };
            return self.shared.contains(&site)
                && checked_reads::inputs(call, written)
                && reader(func, dependency, self.hir, written);
        }
        let Some(declared) = dependency.source.declared() else {
            return false;
        };
        if self.observed.contains(&site) {
            return self.declared.contains(&declared)
                && observed_values::arguments(call, declared, written);
        }
        if self.shared.contains(&site) && matches!(call.args.first(), Some(AstExpr::Nil)) {
            return matches!(call.args.as_slice(), [AstExpr::Nil, AstExpr::Var(AstNameRef::Local(value)), AstExpr::Var(AstNameRef::Local(reader))]
                if *reader == declared && self.declared.contains(reader)
                    && written.contains(value) && !written.contains(reader));
        }
        let arguments = if self.pairs.contains(&call.required_luau_inlining.unwrap()) {
            if let Some(constant) = dependency.pair_constant {
                return matches!(call.args.as_slice(), [AstExpr::Var(AstNameRef::Local(flag)), value, AstExpr::Var(AstNameRef::Local(reader)), AstExpr::Boolean(false)]
                    if counter_repeat::integer(value) == Some(constant)
                        && *reader == declared && self.declared.contains(reader)
                        && !written.contains(flag) && !written.contains(reader));
            }
            let [flag, value, reader, AstExpr::Boolean(true)] = call.args.as_slice() else {
                return false;
            };
            [flag, value, reader]
        } else {
            let [flag, value, reader] = call.args.as_slice() else {
                return false;
            };
            [flag, value, reader]
        };
        matches!(arguments, [AstExpr::Var(AstNameRef::Local(flag)), AstExpr::Var(AstNameRef::Local(value)), AstExpr::Var(AstNameRef::Local(reader))]
            if *reader == declared && self.declared.contains(reader)
                && !written.contains(flag) && written.contains(value) && !written.contains(reader))
    }

    pub fn complete(&self) -> bool {
        self.declared.len() == self.readers.len()
    }

    pub fn inline_argument(&self, call: &AstCallExpr, index: usize) -> bool {
        call.required_luau_inlining.and_then(|site| self.occurrences.get(&site))
            .is_some_and(|dependency| dependency.parameter == index
                && matches!(dependency.source, HirLuauCallableSource::Expression { site, creation }
                    if matches!(call.args.get(index), Some(AstExpr::FunctionExpr(func)) if func.source_site == Some(site) && func.creation == Some(creation))))
    }
}
