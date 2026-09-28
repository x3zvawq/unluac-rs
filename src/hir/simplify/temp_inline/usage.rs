//! 收集 temp-inline 所需的定义、读取和谓词边界摘要。
//!
//! 消费当前 HIR 与共享 visitor，保留 debug 和 capture 身份，供内联 owner 审查。

use super::*;

pub(super) enum TempUseSummary {
    Empty,
    One(TempId, usize),
    Many(Vec<(TempId, usize)>),
}

impl TempUseSummary {
    pub(super) fn count(&self, temp: TempId) -> usize {
        match self {
            Self::Empty => 0,
            Self::One(other, count) => usize::from(*other == temp) * *count,
            Self::Many(entries) => entries
                .iter()
                .find_map(|(other, count)| (*other == temp).then_some(*count))
                .unwrap_or(0),
        }
    }

    pub(super) fn add_to_totals(&self, totals: &mut [usize]) {
        self.for_each(|temp, count| totals[temp.index()] += count);
    }

    pub(super) fn subtract_from_totals(&self, totals: &mut [usize]) {
        self.for_each(|temp, count| {
            totals[temp.index()] = totals[temp.index()]
                .checked_sub(count)
                .expect("rewrite should not remove more temp uses than remain live");
        });
    }

    pub(super) fn for_each(&self, mut visitor: impl FnMut(TempId, usize)) {
        match self {
            Self::Empty => {}
            Self::One(temp, count) => visitor(*temp, *count),
            Self::Many(entries) => {
                for &(temp, count) in entries {
                    visitor(temp, count);
                }
            }
        }
    }
}

pub(super) struct TempUseScratch {
    definition_counts: Vec<usize>,
    temp_debug_hints: Vec<bool>,
    boolean_value_predicates: Vec<bool>,
    counts: Vec<usize>,
    touched: Vec<TempId>,
}

impl TempUseScratch {
    pub(super) fn new(proto: &HirProto) -> Self {
        let temp_count = proto.temp_count;
        let mut temp_debug_hints = vec![false; temp_count];
        for (index, hint) in proto.temp_debug_locals.iter().enumerate().take(temp_count) {
            temp_debug_hints[index] = hint.is_some();
        }
        struct Definitions {
            counts: Vec<usize>,
            boolean_values: Vec<bool>,
            literal_booleans: Vec<bool>,
            predicates: Vec<bool>,
            copies: Vec<Vec<TempId>>,
            predicate_occurrences: BTreeSet<usize>,
        }
        impl Definitions {
            fn predicate(&mut self, expr: &HirExpr) {
                self.predicate_occurrences
                    .insert(std::ptr::from_ref(expr).addr());
            }
        }
        impl HirVisitor<'_> for Definitions {
            fn visit_stmt(&mut self, stmt: &HirStmt) {
                if let Some((temp, value)) = stmt.scalar_temp_assignment() {
                    if let HirExpr::TempRef(source) = value {
                        self.copies[temp.index()].push(*source);
                    } else if crate::hir::simplify::expr_facts::expr_is_boolean_valued(value) {
                        if matches!(value, HirExpr::Boolean(_)) {
                            self.literal_booleans[temp.index()] =
                                matches!(value, HirExpr::Boolean(true));
                        } else {
                            self.boolean_values[temp.index()] = true;
                        }
                    }
                }
                match stmt {
                    HirStmt::If(branch) => self.predicate(&branch.cond),
                    HirStmt::While(loop_) => self.predicate(&loop_.cond),
                    HirStmt::Repeat(loop_) => self.predicate(&loop_.cond),
                    _ => {}
                }
            }

            fn visit_expr(&mut self, expr: &HirExpr) {
                let predicate = self
                    .predicate_occurrences
                    .remove(&std::ptr::from_ref(expr).addr());
                match expr {
                    HirExpr::TempRef(temp) if predicate => self.predicates[temp.index()] = true,
                    HirExpr::Unary(unary) if predicate => self.predicate(&unary.expr),
                    HirExpr::Binary(binary) if predicate => {
                        // `flag == true` 也能被编译成条件跳转；原 Boolean store 仍有覆盖含义。
                        self.predicate(&binary.lhs);
                        self.predicate(&binary.rhs);
                    }
                    HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                        self.predicate(&logical.lhs);
                        if predicate {
                            self.predicate(&logical.rhs);
                        }
                    }
                    _ => {}
                }
                if let HirExpr::Decision(decision) = expr {
                    for node in &decision.nodes {
                        if !matches!(node.truthy, crate::hir::HirDecisionTarget::CurrentValue)
                            && !matches!(node.falsy, crate::hir::HirDecisionTarget::CurrentValue)
                        {
                            self.predicate(&node.test);
                        }
                    }
                }
            }

            fn visit_lvalue(&mut self, target: &HirLValue) {
                if let HirLValue::Temp(temp) = target {
                    self.counts[temp.index()] += 1;
                }
            }
        }
        let mut definitions = Definitions {
            counts: vec![0; temp_count],
            boolean_values: vec![false; temp_count],
            literal_booleans: vec![false; temp_count],
            predicates: vec![false; temp_count],
            copies: vec![Vec::new(); temp_count],
            predicate_occurrences: BTreeSet::new(),
        };
        visit_stmts(&proto.body.stmts, &mut definitions);
        let mut pending = definitions
            .predicates
            .iter()
            .enumerate()
            .filter_map(|(index, value)| value.then_some(TempId(index)))
            .collect::<Vec<_>>();
        let mut literal_predicates = definitions.predicates.clone();
        let mut literal_pending = pending.clone();
        // true 直接进入谓词会被目标编译器当成无条件路径，丢掉原 LOAD/TEST；
        // false 谓词仍会重发 LOAD/TEST，不在这里额外物化其 scratch 声明。
        // 直接 LOAD/TEST 及唯一 COPY 链持有原声明前缀；多定义的 phi 叶 Boolean
        // 则是比较物化协议，必须留给 Decision/完整帧消费，不能逐叶冻结。
        while let Some(source) = literal_pending.pop() {
            if definitions.counts[source.index()] != 1 {
                continue;
            }
            for &copy in &definitions.copies[source.index()] {
                if !literal_predicates[copy.index()] {
                    literal_predicates[copy.index()] = true;
                    literal_pending.push(copy);
                }
            }
        }
        while let Some(source) = pending.pop() {
            for &copy in &definitions.copies[source.index()] {
                if !definitions.predicates[copy.index()] {
                    definitions.predicates[copy.index()] = true;
                    pending.push(copy);
                }
            }
        }
        let boolean_value_predicates = definitions
            .boolean_values
            .into_iter()
            .zip(definitions.predicates)
            .zip(
                definitions
                    .literal_booleans
                    .into_iter()
                    .zip(literal_predicates),
            )
            .map(|((value, predicate), (literal, literal_predicate))| {
                value && predicate || literal && literal_predicate
            })
            .collect();
        Self {
            definition_counts: definitions.counts,
            temp_debug_hints,
            boolean_value_predicates,
            counts: vec![0; temp_count],
            touched: Vec::new(),
        }
    }

    pub(super) fn boolean_value_predicates(&self) -> impl Iterator<Item = TempId> + '_ {
        self.boolean_value_predicates
            .iter()
            .enumerate()
            .filter_map(|(index, preserve)| preserve.then_some(TempId(index)))
    }

    pub(super) fn has_unique_definition(&self, temp: TempId) -> bool {
        self.definition_counts.get(temp.index()) == Some(&1)
    }

    pub(super) fn has_definition(&self, temp: TempId) -> bool {
        self.definition_counts
            .get(temp.index())
            .is_some_and(|count| *count != 0)
    }

    pub(super) fn temp_count(&self) -> usize {
        self.counts.len()
    }

    pub(super) fn has_debug_local_hint(&self, temp: TempId) -> bool {
        self.temp_debug_hints
            .get(temp.index())
            .copied()
            .unwrap_or(false)
    }

    fn note_temp(&mut self, temp: TempId) {
        let slot = &mut self.counts[temp.index()];
        if *slot == 0 {
            self.touched.push(temp);
        }
        *slot += 1;
    }

    fn finish_summary(&mut self) -> TempUseSummary {
        match self.touched.len() {
            0 => TempUseSummary::Empty,
            1 => {
                let temp = self
                    .touched
                    .pop()
                    .expect("single touched temp branch must contain exactly one item");
                let count = std::mem::take(&mut self.counts[temp.index()]);
                TempUseSummary::One(temp, count)
            }
            _ => {
                let mut entries = Vec::with_capacity(self.touched.len());
                for temp in self.touched.drain(..) {
                    let count = std::mem::take(&mut self.counts[temp.index()]);
                    entries.push((temp, count));
                }
                TempUseSummary::Many(entries)
            }
        }
    }
}

impl HirVisitor<'_> for TempUseScratch {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let HirExpr::TempRef(temp) = expr {
            self.note_temp(*temp);
        }
    }
}

pub(super) fn collect_stmt_temp_uses(
    stmt: &HirStmt,
    scratch: &mut TempUseScratch,
) -> TempUseSummary {
    visit_stmts(std::slice::from_ref(stmt), scratch);
    scratch.finish_summary()
}

pub(super) fn collect_expr_temp_uses_summary(
    expr: &HirExpr,
    scratch: &mut TempUseScratch,
) -> TempUseSummary {
    visit_expr(expr, scratch);
    scratch.finish_summary()
}
