//! 配对初始化 Boolean、逐次字段观察与共同返回的展开体。
//! 原程序负责输入和控制边；当前 HIR 另核对每次读取的顺序及真假结果，不以纯值约简删去观察。

use super::*;
use crate::hir::common::{HirBinding, HirOperationSources, HirUnaryOpKind, ParamId};
use crate::hir::promotion::value_programs::seeded_predicates as original;
use crate::hir::promotion::value_programs::{Literal, Operation, Predicate};

#[derive(Clone)]
pub(super) struct Body {
    pub original: original::Body,
    result: LocalId,
    fields: BTreeMap<crate::transformer::InstrRef, HirExpr>,
    pub parameter_name: Option<String>,
    pub result_name: Option<String>,
}

/// 原返回 COPY 属于完整展开帧；不能在识别函数体之前将它抹进后继调用参数。
pub(in crate::hir::simplify) fn preserve_outputs(
    module: &mut crate::hir::HirModule,
    promotion: &[ProtoPromotionFacts],
) -> bool {
    struct Templates<'a> {
        promotion: &'a [ProtoPromotionFacts],
        entries: BTreeMap<&'a Vec<Operation>, Option<crate::hir::HirSourceSite>>,
    }
    impl<'hir> crate::hir::visit::HirVisitor<'hir> for Templates<'_> {
        fn visit_closure(&mut self, closure: &'hir crate::hir::HirClosureExpr) {
            if !closure.captures.is_empty()
                || !matches!(
                    closure.creation,
                    Some(crate::hir::HirClosureCreation::MayReuse { .. })
                )
            {
                return;
            }
            let Some(source) = closure.source_site else {
                return;
            };
            let Some(body) = self
                .promotion
                .get(closure.proto.index())
                .and_then(ProtoPromotionFacts::seeded_predicate_body)
            else {
                return;
            };
            self.entries
                .entry(&body.program.shape)
                .and_modify(|entry| *entry = None)
                .or_insert(Some(source));
        }
    }
    let mut changed = false;
    for proto in &mut module.protos {
        let Some(facts) = promotion.get(proto.id.index()) else {
            continue;
        };
        let mut templates = Templates {
            promotion,
            entries: BTreeMap::new(),
        };
        crate::hir::visit::visit_stmts(&proto.body.stmts, &mut templates);
        for frame in facts.seeded_predicate_frames() {
            if !templates
                .entries
                .get(&frame.body.program.shape)
                .copied()
                .flatten()
                .is_some_and(|source| {
                    source.proto == proto.id && source.instr < frame.region.source
                })
            {
                continue;
            }
            changed |= proto.inline_dispositions.preserve_temp(
                frame.output,
                crate::hir::HirInlineRetentionReason::PhysicalFramePrefix,
            );
            changed |= proto.physical_root_temps.insert(frame.output);
        }
    }
    changed
}

/// 0/1 为 Boolean 终点；其它节点保留原读取指令身份与两条后继。
/// 通用纯值 decision diagram 会删除同后继节点，这里必须保留潜在 __index 观察。
#[derive(Default)]
struct Observations {
    nodes: BTreeMap<(usize, usize, usize), usize>,
}

impl Observations {
    fn read(&mut self, site: usize, yes: usize, no: usize) -> usize {
        let next = self.nodes.len() + 2;
        *self.nodes.entry((site, yes, no)).or_insert(next)
    }

    fn program(&mut self, body: &original::Body) -> Option<usize> {
        // 原程序只有前向边；每个位置分别计算当前 Boolean 的两种状态，各处理一次。
        let count = body.program.shape.len();
        let mut values = vec![[0, 1]; count + 1];
        for index in (0..count).rev() {
            values[index] = match &body.program.shape[index] {
                Operation::Load(Literal::Boolean(value)) => {
                    [values[index + 1][usize::from(*value)]; 2]
                }
                Operation::Jump(target) => *values.get(*target)?,
                Operation::Branch { .. } => values[index + 1],
                Operation::Field(_) => {
                    let Operation::Branch {
                        predicate: Predicate::Truthy,
                        negated,
                        truthy,
                        falsy,
                        ..
                    } = body.program.shape.get(index + 1)?
                    else {
                        return None;
                    };
                    let (yes, no) = if *negated {
                        (*falsy, *truthy)
                    } else {
                        (*truthy, *falsy)
                    };
                    [
                        self.read(index, values.get(yes)?[0], values.get(no)?[0]),
                        self.read(index, values.get(yes)?[1], values.get(no)?[1]),
                    ]
                }
                _ => return None,
            };
        }
        Some(values[0][usize::from(body.initial)])
    }
}

struct Current<'a> {
    facts: &'a ProtoPromotionFacts,
    body: &'a original::Body,
    source: crate::transformer::InstrRef,
    parameter: HirBinding,
    result: HirBinding,
    cached: Option<(HirBinding, &'a HirExpr)>,
    budget: usize,
    graph: Observations,
}

impl Current<'_> {
    fn condition(&mut self, value: &HirExpr, yes: usize, no: usize) -> Option<usize> {
        // 候选拒绝[ResourceLimit]：共享有界节点预算，不能为一个原程序遍历任意膨胀的当前表达式。
        self.budget = self.budget.checked_sub(1)?;
        match value {
            HirExpr::Unary(unary)
                if unary.op == HirUnaryOpKind::Not && unary.source_site.is_none() =>
            {
                self.condition(&unary.expr, no, yes)
            }
            HirExpr::LogicalAnd(logical) => {
                let rhs = self.condition(&logical.rhs, yes, no)?;
                self.condition(&logical.lhs, rhs, no)
            }
            HirExpr::LogicalOr(logical) => {
                let rhs = self.condition(&logical.rhs, yes, no)?;
                self.condition(&logical.lhs, yes, rhs)
            }
            HirExpr::TableAccess(access) => {
                let HirOperationSources::Single(source) = access.sources else {
                    return None;
                };
                let site = source.instr.index().checked_sub(self.source.index())?;
                let Operation::Field(key) = self.body.program.shape.get(site)? else {
                    return None;
                };
                let layout = self.facts.native_table_read_layout(access)?;
                if access.key != HirExpr::String(key.clone())
                    || HirBinding::from_expr(&access.base) != Some(self.parameter)
                    || layout.base != HomeSlotKey::new(self.body.parameter.index(), 0)
                    || layout.key.is_some()
                    || self.facts.table_read_result_home(access)
                        != Some(HomeSlotKey::new(self.body.scratch.index(), 0))
                    || !self.facts.operation_result_reference_unaliased(source)
                {
                    return None;
                }
                Some(self.graph.read(site, yes, no))
            }
            value
                if self
                    .cached
                    .is_some_and(|(binding, _)| HirBinding::from_expr(value) == Some(binding)) =>
            {
                let (_, value) = self.cached?;
                self.condition(value, yes, no)
            }
            _ => None,
        }
    }

    fn block(
        &mut self,
        stmts: &[HirStmt],
        mut continuation: [usize; 2],
        returns: bool,
    ) -> Option<[usize; 2]> {
        for stmt in stmts.iter().rev() {
            // 候选拒绝[ResourceLimit]：两种 Boolean 状态共用一次块遍历及同一预算。
            self.budget = self.budget.checked_sub(1)?;
            if let Some((binding, HirExpr::Boolean(value))) = scalar_binding(stmt) {
                if binding != self.result {
                    return None;
                }
                continuation = [continuation[usize::from(*value)]; 2];
                continue;
            }
            match stmt {
                HirStmt::If(branch) => {
                    let yes = self.block(&branch.then_block.stmts, continuation, returns)?;
                    let no = if let Some(block) = &branch.else_block {
                        self.block(&block.stmts, continuation, returns)?
                    } else {
                        continuation
                    };
                    continuation = [
                        self.condition(&branch.cond, yes[0], no[0])?,
                        self.condition(&branch.cond, yes[1], no[1])?,
                    ];
                }
                HirStmt::Return(ret) if returns && ret.values.tail.is_none() => {
                    let [value] = ret.values.fixed.as_slice() else {
                        return None;
                    };
                    continuation = match value {
                        HirExpr::Boolean(value) => [usize::from(*value); 2],
                        value if HirBinding::from_expr(value) == Some(self.result) => [0, 1],
                        _ => return None,
                    };
                }
                _ => return None,
            }
        }
        Some(continuation)
    }
}

pub(super) fn body(proto: &HirProto, facts: &ProtoPromotionFacts) -> Option<Body> {
    let original = facts.seeded_predicate_body()?;
    if proto.failure.is_some()
        || proto.params.len() != 1
        || proto.signature.is_vararg
        || !proto.upvalues.is_empty()
        || !proto.children.is_empty()
        || !matches!(proto.body.stmts.last(), Some(HirStmt::Return(ret))
            if ret.values.tail.is_none() && ret.values.fixed.len() == 1)
    {
        return None;
    }
    let (result, value) = scalar_binding(proto.body.stmts.first()?)?;
    if *value != HirExpr::Boolean(original.initial)
        || match result {
            HirBinding::Local(local) => facts.trusted_local_home_slot(local),
            _ => None,
        } != Some(HomeSlotKey::new(original.result.index(), 0))
    {
        return None;
    }
    let mut current = Current {
        facts,
        body: original,
        source: crate::transformer::InstrRef(0),
        parameter: HirBinding::Param(ParamId(0)),
        result,
        cached: None,
        budget: 512,
        graph: Observations::default(),
    };
    let expected = current.graph.program(original)?;
    if current.block(&proto.body.stmts, [0, 1], true)?[usize::from(original.initial)] != expected {
        return None;
    }
    let HirBinding::Local(result) = result else {
        return None;
    };
    struct Fields {
        values: BTreeMap<crate::transformer::InstrRef, HirExpr>,
        valid: bool,
    }
    impl crate::hir::visit::HirVisitor<'_> for Fields {
        fn visit_expr(&mut self, value: &HirExpr) {
            if let HirExpr::TableAccess(access) = value
                && let HirOperationSources::Single(source) = access.sources
            {
                if let Some(previous) = self.values.get(&source.instr) {
                    self.valid &= previous == value;
                } else {
                    self.values.insert(source.instr, value.clone());
                }
            }
        }
    }
    let mut fields = Fields {
        values: BTreeMap::new(),
        valid: true,
    };
    crate::hir::visit::visit_stmts(&proto.body.stmts, &mut fields);
    if !fields.valid {
        return None;
    }
    Some(Body {
        fields: fields.values,
        original: original.clone(),
        result,
        parameter_name: proto.param_debug_hints[0].clone(),
        result_name: proto.local_debug_hints[result.index()].clone(),
    })
}

struct Candidate<'a> {
    frame: &'a original::Frame,
    callee: &'a Callee,
    input: LocalId,
    seed: HirBinding,
    branch: &'a crate::hir::HirIf,
    cached: Option<(HirBinding, &'a HirExpr)>,
    result: LocalId,
    start: usize,
    sink: usize,
}

fn first_field(expr: &HirExpr) -> Option<crate::hir::HirSourceSite> {
    match expr {
        HirExpr::Unary(unary) if unary.source_site.is_none() => first_field(&unary.expr),
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => first_field(&logical.lhs),
        HirExpr::TableAccess(access) => match access.sources {
            HirOperationSources::Single(source) => Some(source),
            _ => None,
        },
        _ => None,
    }
}

fn blocks<'a>(
    block: &'a HirBlock,
    cursor: &mut usize,
    output: &mut Vec<(&'a HirBlock, Vec<usize>)>,
) {
    let mut positions = Vec::with_capacity(block.stmts.len());
    for stmt in &block.stmts {
        positions.push(*cursor);
        *cursor += 1;
        crate::hir::visit::for_each_nested_block(stmt, &mut |child| blocks(child, cursor, output));
        if matches!(stmt, HirStmt::Repeat(_)) {
            *cursor += 1;
        }
    }
    output.push((block, positions));
}

fn candidates<'a>(
    proto: &'a HirProto,
    facts: &'a ProtoPromotionFacts,
    callees: &'a Callees,
    bodies: &[Option<Body>],
) -> Vec<Candidate<'a>> {
    let mut templates = BTreeMap::new();
    for callee in callees.values() {
        if let HirLuauInliningBody::SeededPredicate { template } = callee.body
            && let Some(body) = &bodies[template]
        {
            templates
                .entry(&body.original.program.shape)
                .and_modify(|entry| *entry = None)
                .or_insert(Some(callee));
        }
    }
    let frames = facts
        .seeded_predicate_frames()
        .filter_map(|frame| {
            templates
                .get(&frame.body.program.shape)
                .copied()
                .flatten()?;
            let first = frame
                .body
                .program
                .shape
                .iter()
                .position(|op| matches!(op, Operation::Field(_)))?;
            Some((
                crate::transformer::InstrRef(frame.region.source.index() + first),
                frame,
            ))
        })
        .collect::<BTreeMap<_, _>>();
    let mut locations = Vec::new();
    blocks(&proto.body, &mut 0, &mut locations);
    let mut output = Vec::new();
    let uses = value_uses::ValueUses::new(proto);
    for (block, positions) in locations {
        for index in 0..block.stmts.len() {
            let candidate = (|| {
                let (seed, HirExpr::Boolean(initial)) = scalar_binding(&block.stmts[index])? else {
                    return None;
                };
                let (branch_index, cached) = match block.stmts.get(index + 1)? {
                    HirStmt::If(_) => (index + 1, None),
                    stmt => {
                        let (binding, value @ HirExpr::TableAccess(_)) = scalar_binding(stmt)?
                        else {
                            return None;
                        };
                        (index + 2, Some((binding, value)))
                    }
                };
                let HirStmt::If(branch) = block.stmts.get(branch_index)? else {
                    return None;
                };
                let first = first_field(cached.map_or(&branch.cond, |(_, value)| value))?;
                let frame = *frames.get(&first.instr)?;
                let callee = (*templates.get(&frame.body.program.shape)?)?;
                let expected = bodies[callee.child.index()].as_ref()?;
                let mapping = expected
                    .original
                    .program
                    .register_mapping(&frame.body.program)?;
                if first.proto != proto.id
                    || callee.creation.instr >= frame.region.source
                    || *initial != frame.body.initial
                    || mapping.get(&expected.original.parameter) != Some(&frame.body.parameter)
                    || mapping.get(&expected.original.result) != Some(&frame.body.result)
                    || mapping.get(&expected.original.scratch) != Some(&frame.body.scratch)
                    || match seed {
                        HirBinding::Local(local) => {
                            facts.promoted_local_for_temp(frame.seed) != Some(local)
                                || facts.promoted_local_for_temp(frame.region.result) != Some(local)
                        }
                        HirBinding::Temp(temp) => temp != frame.seed,
                        _ => true,
                    }
                {
                    return None;
                }
                let sink = branch_index + 1;
                let last @ HirStmt::LocalDecl(_) = block.stmts.get(sink)? else {
                    return None;
                };
                let (result, value) = scalar_local(last)?;
                let input = facts.promoted_local_for_temp(frame.input)?;
                if HirBinding::from_expr(value) != Some(seed)
                    || facts.promoted_local_for_temp(frame.output) != Some(result)
                    || facts.trusted_local_home_slot(result)
                        != Some(HomeSlotKey::new(frame.output_home.index(), 0))
                    || facts.trusted_local_home_slot(input)
                        != Some(HomeSlotKey::new(frame.body.parameter.index(), 0))
                {
                    return None;
                }
                // 候选拒绝[ProofIncomplete:ValueLifetime]：草稿退休的内部状态不能仍被区间外读取。
                // 原槽可有早先的表/闭包版本；这里只检查本次初始化之后的后缀。
                if uses.binding_reads(seed, positions[sink] + 1, uses.count) != 0
                    || cached.is_some_and(|(binding, _)| {
                        uses.binding_reads(binding, positions[sink] + 1, uses.count) != 0
                    })
                {
                    return None;
                }
                let mut current = Current {
                    facts,
                    body: &frame.body,
                    source: frame.region.source,
                    parameter: HirBinding::Local(input),
                    result: seed,
                    cached,
                    budget: 512,
                    graph: Observations::default(),
                };
                let expected = current.graph.program(&frame.body)?;
                if current.block(&block.stmts[branch_index..sink], [0, 1], false)?
                    [usize::from(*initial)]
                    != expected
                {
                    return None;
                }
                Some(Candidate {
                    frame,
                    callee,
                    input,
                    seed,
                    branch,
                    cached,
                    result,
                    start: positions[index],
                    sink: positions[sink],
                })
            })();
            output.extend(candidate);
        }
    }
    output
}

pub(super) fn debug_arguments(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    callees: &Callees,
    bodies: &[Option<Body>],
) -> Option<(HirProto, Vec<(crate::hir::HirSourceSite, LocalId)>)> {
    let mut draft = None;
    let mut obligations = Vec::new();
    for candidate in candidates(proto, facts, callees, bodies) {
        let body = bodies[candidate.callee.child.index()].as_ref()?;
        let frame = candidate.frame;
        let seed = match candidate.seed {
            HirBinding::Local(local) => Some(local),
            _ => None,
        };
        for (local, temp, name, parameter) in [
            (
                Some(candidate.input),
                frame.input,
                &body.parameter_name,
                true,
            ),
            (seed, frame.seed, &body.result_name, false),
        ] {
            let Some(local) = local else {
                continue;
            };
            // 复用的低槽实参属于 caller，不能把它的 debug 身份当作内联参数投影。
            if parameter && frame.body.parameter.index() < frame.output_home.index() {
                continue;
            }
            if proto.local_debug_hints[local.index()].is_none()
                && proto.local_debug_scopes[local.index()].is_none()
            {
                continue;
            }
            let scope = proto
                .debug_scopes
                .get(proto.local_debug_scopes[local.index()]?)?
                .as_ref()?;
            let initialized_at = if parameter {
                crate::transformer::InstrRef(frame.region.source.index().checked_sub(1)?)
            } else {
                frame.region.source
            };
            if name.is_none()
                || &proto.local_debug_hints[local.index()] != name
                || scope.end_instr
                    != Some(crate::transformer::InstrRef(frame.region.end.index() + 1))
                || scope.initializer_end_instr != Some(initialized_at)
                || scope.initializer_temp.or(scope.initializer_phi) != Some(temp)
            {
                return None;
            }
            let draft = draft.get_or_insert_with(|| proto.clone());
            draft.local_debug_hints[local.index()] = None;
            draft.local_debug_scopes[local.index()] = None;
            draft.temp_debug_locals[temp.index()] = None;
            draft.temp_debug_scopes[temp.index()] = None;
            obligations.push((
                crate::hir::HirSourceSite {
                    proto: proto.id,
                    instr: frame.region.source,
                },
                candidate.callee.local,
            ));
        }
    }
    draft.map(|proto| (proto, obligations))
}

struct Invocation {
    frame: original::Frame,
    callee: LocalId,
    input: LocalId,
    result: LocalId,
}

pub(in crate::hir::simplify::call_frames) struct Prepared {
    pub(super) proto: HirProto,
    invocations: BTreeMap<crate::hir::HirSourceSite, Invocation>,
    pub(super) bodies: BTreeMap<crate::hir::HirProtoRef, HirStmt>,
}

pub(super) fn prepare(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    callees: &Callees,
    bodies: &[Option<Body>],
) -> Option<Prepared> {
    let mut removed = BTreeSet::new();
    let mut replacements = BTreeMap::new();
    let mut invocations = BTreeMap::new();
    let mut canonical = BTreeMap::new();
    for candidate in candidates(proto, facts, callees, bodies) {
        // 候选拒绝[PolicyBoundary:DebugIdentity]：身份投影必须先由原初始化和完整区间证明。
        if matches!(candidate.seed, HirBinding::Local(local)
            if proto.local_debug_hints[local.index()].is_some() || proto.local_debug_scopes[local.index()].is_some())
        {
            continue;
        }
        let body = bodies[candidate.callee.child.index()].as_ref()?;
        let branch = canonical_body(&candidate, body)?;
        canonical.entry(candidate.callee.child).or_insert(branch);
        let frame = candidate.frame;
        let source = crate::hir::HirSourceSite {
            proto: proto.id,
            instr: frame.region.source,
        };
        let call = factories::factory_call(
            candidate.callee.local,
            Some(source),
            vec![HirExpr::LocalRef(candidate.input)].into(),
        );
        removed.extend(candidate.start..candidate.sink);
        replacements.insert(candidate.sink, call);
        invocations.insert(
            source,
            Invocation {
                frame: frame.clone(),
                callee: candidate.callee.local,
                input: candidate.input,
                result: candidate.result,
            },
        );
    }
    if invocations.is_empty() {
        return None;
    }
    fn rewrite(
        block: &mut HirBlock,
        cursor: &mut usize,
        removed: &BTreeSet<usize>,
        replacements: &BTreeMap<usize, HirExpr>,
    ) {
        block.stmts.retain_mut(|stmt| {
            let index = *cursor;
            *cursor += 1;
            crate::hir::simplify::walk::for_each_nested_block_mut(stmt, &mut |child| {
                rewrite(child, cursor, removed, replacements)
            });
            if matches!(stmt, HirStmt::Repeat(_)) {
                *cursor += 1;
            }
            if let Some(value) = replacements.get(&index) {
                let HirStmt::LocalDecl(decl) = stmt else {
                    unreachable!("validated result COPY declaration")
                };
                decl.values = vec![value.clone()].into();
            }
            !removed.contains(&index)
        });
    }
    let mut draft = proto.clone();
    rewrite(&mut draft.body, &mut 0, &removed, &replacements);
    Some(Prepared {
        proto: draft,
        invocations,
        bodies: canonical,
    })
}

impl Prepared {
    pub(super) fn certified(&self, sites: &BTreeSet<(crate::hir::HirSourceSite, LocalId)>) -> bool {
        self.invocations
            .iter()
            .all(|(source, invocation)| sites.contains(&(*source, invocation.callee)))
    }

    pub(in crate::hir::simplify::call_frames) fn result(
        &self,
        call: &HirCallExpr,
    ) -> Option<TempId> {
        let invocation = self.invocations.get(&call.required_luau_inlining?)?;
        (call.source_site.is_none()
            && call.callee == HirExpr::LocalRef(invocation.callee)
            && !call.is_method()
            && call.fastcall.is_none()
            && call.args.tail.is_none()
            && call.args.fixed == [HirExpr::LocalRef(invocation.input)])
        .then_some(invocation.frame.output)
    }

    pub(super) fn result_home(&self, source: crate::hir::HirSourceSite) -> Option<usize> {
        Some(self.invocations.get(&source)?.frame.output_home.index())
    }

    pub(super) fn plans(
        &self,
        context: NativeFrameContext<'_>,
        facts: &ProtoPromotionFacts,
        native: &[Plan],
    ) -> Vec<Plan> {
        let mut consumed = BTreeSet::new();
        for plan in native {
            for value in plan
                .values
                .fixed
                .iter()
                .chain(plan.values.tail.iter().map(|tail| tail.as_expr()))
            {
                crate::hir::visit::any_expr(value, &mut |value| {
                    if let HirExpr::Call(call) = value
                        && let Some(source) = call.required_luau_inlining
                    {
                        consumed.insert(source);
                    }
                    false
                });
            }
        }
        let mut locations = Vec::new();
        blocks(&context.proto.body, &mut 0, &mut locations);
        let mut plans = Vec::new();
        let callees = context
            .expanded_callees
            .into_iter()
            .flat_map(|callees| callees.values())
            .map(|callee| (callee.local, callee))
            .collect::<BTreeMap<_, _>>();
        for (block, positions) in locations {
            let mut start = 0;
            for (index, stmt) in block.stmts.iter().enumerate() {
                let candidate = (|| {
                    let (local, HirExpr::Call(call)) = scalar_local(stmt)? else {
                        return None;
                    };
                    let source = call.required_luau_inlining?;
                    // 外层原参数帧已完整消费本调用时，不用零宽独立声明覆盖它。
                    if consumed.contains(&source) {
                        return None;
                    }
                    let invocation = self.invocations.get(&source)?;
                    if local != invocation.result {
                        return None;
                    }
                    let base = HomeSlotKey::new(invocation.frame.output_home.index(), 0);
                    let run = block.stmts[start..index].iter().collect::<Vec<_>>();
                    let mut builder =
                        frame_builder(context, &run, facts, DecompileDialect::Luau, base.slot())?;
                    let call = builder.expanded_seeded_predicate(
                        call,
                        run.len(),
                        base.slot(),
                        Some(invocation.frame.output),
                    )?;
                    let first = builder.first_event.map_or(index, |first| start + first);
                    if builder.first_event.is_some() && builder.next_event != run.len() {
                        return None;
                    }
                    let callee = *callees.get(&invocation.callee)?;
                    let mut plan = factories::invocation(
                        callee,
                        source,
                        base,
                        local,
                        positions[first],
                        positions[index],
                    );
                    plan.values = vec![HirExpr::Call(Box::new(call))].into();
                    Some(plan)
                })();
                plans.extend(candidate);
                if matches!(scalar_local(stmt), Some((_, HirExpr::Call(call))) if call.required_luau_inlining.is_some_and(|source| self.invocations.contains_key(&source)))
                    || scalar_binding(stmt).is_none() && constructor_write(stmt).is_none()
                {
                    start = index + 1;
                }
            }
        }
        plans
    }
}

impl FrameBuilder<'_> {
    pub(in crate::hir::simplify::call_frames) fn expanded_seeded_predicate(
        &mut self,
        call: &HirCallExpr,
        before: usize,
        slot: usize,
        producer: Option<TempId>,
    ) -> Option<HirCallExpr> {
        let context = self.native?;
        let invocation = context
            .seeded_predicates?
            .invocations
            .get(&call.required_luau_inlining?)?;
        let frame = &invocation.frame;
        let home = HomeSlotKey::new(frame.output_home.index(), 0);
        // 候选拒绝[ProofIncomplete:CallFrame]：草稿只代替已证明的原程序；外层仍须消费同一输出和原实参帧。
        if call.source_site.is_some()
            || call.is_method()
            || call.fastcall.is_some()
            || call.callee != HirExpr::LocalRef(invocation.callee)
            || call.args.tail.is_some()
            || call.args.fixed != [HirExpr::LocalRef(invocation.input)]
            || slot != home.slot()
            || producer.is_some_and(|producer| producer != frame.output)
            || context.closed.contains(&home)
            || context.barred.contains(&home)
            || frame.body.parameter.index() >= slot && frame.body.parameter.index() != slot + 1
        {
            return None;
        }
        let events = (self.first_event, self.next_event);
        let argument = self.expr(
            &call.args.fixed[0],
            before,
            slot + 1,
            None,
            false,
            true,
            Some(frame.input),
        );
        let Some(argument) = argument else {
            (self.first_event, self.next_event) = events;
            return None;
        };
        let mut rebuilt = call.clone();
        rebuilt.args.fixed[0] = argument;
        Some(rebuilt)
    }
}

/// caller 的共同出口树已经由同一原程序及观察图证明。按原指令偏移把字段来源投回
/// child，避免把 VM 跳转折叠出来的提前 RETURN 当成源码返回，改变再内联时的结果写槽。
fn canonical_body(candidate: &Candidate<'_>, body: &Body) -> Option<HirStmt> {
    fn expression(value: &HirExpr, candidate: &Candidate<'_>, body: &Body) -> Option<HirExpr> {
        if candidate
            .cached
            .is_some_and(|(binding, _)| HirBinding::from_expr(value) == Some(binding))
        {
            return expression(candidate.cached?.1, candidate, body);
        }
        Some(match value {
            HirExpr::TableAccess(access) => {
                let HirOperationSources::Single(source) = access.sources else {
                    return None;
                };
                let site = crate::transformer::InstrRef(
                    source
                        .instr
                        .index()
                        .checked_sub(candidate.frame.region.source.index())?,
                );
                // 原程序映射选择 child 自己的读取节点；不能把 caller 实参的无元表事实、
                // method protocol 或其它所属 proto 的元数据转交给未知形参。
                body.fields.get(&site)?.clone()
            }
            HirExpr::Unary(unary) => {
                let mut unary = unary.as_ref().clone();
                unary.expr = expression(&unary.expr, candidate, body)?;
                HirExpr::Unary(Box::new(unary))
            }
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                let mut logical = logical.as_ref().clone();
                logical.lhs = expression(&logical.lhs, candidate, body)?;
                logical.rhs = expression(&logical.rhs, candidate, body)?;
                if matches!(value, HirExpr::LogicalAnd(_)) {
                    HirExpr::LogicalAnd(Box::new(logical))
                } else {
                    HirExpr::LogicalOr(Box::new(logical))
                }
            }
            _ => return None,
        })
    }
    fn branch(
        value: &crate::hir::HirIf,
        candidate: &Candidate<'_>,
        body: &Body,
    ) -> Option<crate::hir::HirIf> {
        let mut value = value.clone();
        value.cond = expression(&value.cond, candidate, body)?;
        value.predicate_source = if let Some(source) = value.predicate_source {
            Some(crate::hir::HirSourceSite {
                proto: candidate.callee.child,
                instr: crate::transformer::InstrRef(
                    source
                        .instr
                        .index()
                        .checked_sub(candidate.frame.region.source.index())?,
                ),
            })
        } else {
            None
        };
        value.then_block = block(&value.then_block, candidate, body)?;
        value.else_block = if let Some(other) = &value.else_block {
            Some(block(other, candidate, body)?)
        } else {
            None
        };
        Some(value)
    }
    fn block(value: &HirBlock, candidate: &Candidate<'_>, body: &Body) -> Option<HirBlock> {
        let mut stmts = Vec::with_capacity(value.stmts.len());
        for stmt in &value.stmts {
            if let Some((binding, HirExpr::Boolean(value))) = scalar_binding(stmt) {
                if binding != candidate.seed {
                    return None;
                }
                stmts.push(HirStmt::Assign(Box::new(crate::hir::HirAssign {
                    luau_function_declaration: false,
                    luau_compound_global: false,
                    upvalue_write_source: None,
                    is_phi_transfer: false,
                    parallel_nil_frame: None,
                    targets: vec![HirLValue::Local(body.result)],
                    values: vec![HirExpr::Boolean(*value)].into(),
                    initializer_merge_transaction: None,
                    generic_for_initializer_producer: None,
                    root_release: None,
                    method_rewrite_transaction: None,
                })));
            } else if let HirStmt::If(value) = stmt {
                stmts.push(HirStmt::If(Box::new(branch(value, candidate, body)?)));
            } else {
                return None;
            }
        }
        Some(HirBlock { stmts })
    }
    Some(HirStmt::If(Box::new(branch(
        candidate.branch,
        candidate,
        body,
    )?)))
}

pub(super) fn publish(body: &Body, branch: HirStmt, proto: &mut HirProto) {
    let first = proto
        .body
        .stmts
        .first()
        .expect("certified Boolean initializer")
        .clone();
    let mut last = proto
        .body
        .stmts
        .last()
        .expect("certified fixed return")
        .clone();
    let HirStmt::Return(ret) = &mut last else {
        unreachable!("certified fixed return")
    };
    ret.values = vec![HirExpr::LocalRef(body.result)].into();
    proto.body.stmts = vec![first, branch, last];
    proto
        .inline_dispositions
        .preserve_local(body.result, HirInlineRetentionReason::PhysicalFramePrefix);
}
