//! 这个子模块负责 temp-inline pass 的定义与使用计数摘要。
//!
//! 它依赖 HIR 当前 stmt 序列，只记录 temp 的定义数量、debug 身份与语句树中的读取次数，
//! 子节点顺序由共享 HIR visitor 提供；读取摘要保留 temp 首次出现顺序，索引容量直接
//! 消费 bindings 发布的编号域。capture 两种模式都计入父级绑定引用，不进入子 proto。
//! 不会在这里改写任何节点。例如 `t0 = a.b` 的读取计数为一时，inline owner 可继续审查
//! 该定义的求值顺序与生命周期，不能仅凭计数删除它。
//! 同次遍历保留 Boolean 值进入谓词的边界：`v=not not f(); if v` 的原值存储
//! 不等于 `if f()`；copy 依赖逆向传播到原 producer，不用最后一个 copy 替代旧槽覆盖。

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
                    } else if !matches!(value, HirExpr::Boolean(_))
                        && crate::hir::simplify::expr_facts::expr_is_boolean_valued(value)
                    {
                        self.boolean_values[temp.index()] = true;
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
            .map(|(value, predicate)| value && predicate)
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
