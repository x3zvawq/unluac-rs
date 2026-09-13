//! 这个子模块负责 decision synthesis 的抽象值域和等价性验证上下文。
//!
//! 它依赖前面已经规范化的 HIR decision 表达式，用 canonical multi-valued decision
//! diagram 表达候选在完整抽象环境中的值，不会物化环境笛卡尔积，也不会在这里决定哪种
//! 源码形状更可读。当前 synthesis grammar 只观察 truthiness、与 primitive literal 的稳定
//! equality 和最终返回身份；域包含全部 literal equality class 及两个 fresh truthy symbol，
//! 足以给任意不同的非 literal 结果构造区分赋值。若将来接纳 dynamic-dynamic equality 或
//! ordering，必须先扩展该 small-model 证明。
//!
//! 例如：`temp == nil` 会成为以 `temp` 为变量的共享多值分支；整数与浮点数的判等按 Lua
//! 数值语义计算，而 terminal 仍保留两种结果身份。Decision 的 `CurrentValue` 始终绑定当前
//! node 已求出的 test diagram，不会重求值或跨节点复用。
//! 原子键同时供验证域收集、求值和形状成本使用；例如 `a and 1LL or 2LL` 中的
//! LuaJIT 常量不能在值验证时合法、在成本模型中却没有对应身份。

use std::collections::{BTreeMap, BTreeSet};

use crate::LuaString;
use crate::hir::common::{
    HirBinaryOpKind, HirDecisionExpr, HirDecisionNodeRef, HirDecisionTarget, HirExpr, LocalId,
    ParamId, TempId, UpvalueId,
};
use crate::hir::expr_safety::HirExprSafety;

use super::EXTRA_TRUTHY_SYMBOLS;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(super) enum RefKey {
    Param(ParamId),
    Local(LocalId),
    Upvalue(UpvalueId),
    Temp(TempId),
    VarArg,
}

impl RefKey {
    fn from_expr(expr: &HirExpr) -> Option<Self> {
        match expr {
            HirExpr::ParamRef(value) => Some(Self::Param(*value)),
            HirExpr::LocalRef(value) => Some(Self::Local(*value)),
            HirExpr::UpvalueRef(value) => Some(Self::Upvalue(*value)),
            HirExpr::TempRef(value) => Some(Self::Temp(*value)),
            HirExpr::VarArg => Some(Self::VarArg),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(super) enum AbstractValue {
    Nil,
    False,
    True,
    Integer(i64),
    Number(u64),
    String(LuaString),
    Int64(i64),
    UInt64(u64),
    Vector([u32; 4]),
    Complex { real_bits: u64, imag_bits: u64 },
    TruthySymbol(u8),
}

impl AbstractValue {
    fn from_literal(expr: &HirExpr) -> Option<Self> {
        match expr {
            HirExpr::Nil => Some(Self::Nil),
            HirExpr::Boolean(false) => Some(Self::False),
            HirExpr::Boolean(true) => Some(Self::True),
            HirExpr::Integer(value) => Some(Self::Integer(*value)),
            HirExpr::Number(value) => Some(Self::Number(value.to_bits())),
            HirExpr::String(value) => Some(Self::String(value.clone())),
            HirExpr::Int64(value) => Some(Self::Int64(*value)),
            HirExpr::UInt64(value) => Some(Self::UInt64(*value)),
            HirExpr::Vector(value) => Some(Self::Vector(value.components)),
            HirExpr::Complex { real, imag } => Some(Self::Complex {
                real_bits: real.to_bits(),
                imag_bits: imag.to_bits(),
            }),
            _ => None,
        }
    }
}

/// 综合域与成本模型共用原子身份，后者不再维护一份可能漏掉方言值的字面量清单。
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(super) enum AtomKey {
    Value(AbstractValue),
    Ref(RefKey),
}

impl AtomKey {
    pub(super) fn from_expr(expr: &HirExpr) -> Option<Self> {
        RefKey::from_expr(expr)
            .map(Self::Ref)
            .or_else(|| AbstractValue::from_literal(expr).map(Self::Value))
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub(super) struct DiagramId(usize);

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
enum DiagramNode {
    Terminal(AbstractValue),
    Branch {
        variable: usize,
        edges: Vec<DiagramId>,
    },
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
enum DiagramBinaryOp {
    Eq,
    Lt,
    Le,
    LogicalAnd,
    LogicalOr,
}

/// 在共享的有限抽象值域上构造 canonical multi-valued decision diagram。
///
/// 每个 `RefKey` 只对应一层有序分支；所有终端、同构分支和 apply 结果都会复用。这样验证
/// 覆盖的仍是完整笛卡尔积，但不会先物化 `domain.len() ^ refs.len()` 个环境。两个表达式在
/// 同一 arena 中得到相同根节点，当且仅当它们在每个抽象环境中返回相同值。
pub(super) struct SymbolicVerifier {
    ref_positions: BTreeMap<RefKey, usize>,
    domain_terminals: Vec<DiagramId>,
    nodes: Vec<DiagramNode>,
    interned: BTreeMap<DiagramNode, DiagramId>,
    not_cache: BTreeMap<DiagramId, DiagramId>,
    binary_cache: BTreeMap<(DiagramBinaryOp, DiagramId, DiagramId), Option<DiagramId>>,
    select_cache: BTreeMap<(DiagramId, DiagramId, DiagramId), DiagramId>,
    safety: HirExprSafety,
}

impl SymbolicVerifier {
    pub(super) fn new(
        refs: Vec<RefKey>,
        domain: Vec<AbstractValue>,
        safety: HirExprSafety,
    ) -> Self {
        let ref_positions = refs
            .into_iter()
            .enumerate()
            .map(|(index, key)| (key, index))
            .collect();
        let mut verifier = Self {
            ref_positions,
            domain_terminals: Vec::new(),
            nodes: Vec::new(),
            interned: BTreeMap::new(),
            not_cache: BTreeMap::new(),
            binary_cache: BTreeMap::new(),
            select_cache: BTreeMap::new(),
            safety,
        };
        verifier.domain_terminals = domain
            .into_iter()
            .map(|value| verifier.intern_terminal(value))
            .collect();
        verifier
    }

    pub(super) fn eval_expr(&mut self, expr: &HirExpr) -> Option<DiagramId> {
        if let Some(atom) = AtomKey::from_expr(expr) {
            return match atom {
                AtomKey::Value(value) => Some(self.intern_terminal(value)),
                AtomKey::Ref(key) => self.ref_value(key),
            };
        }
        match expr {
            HirExpr::Unary(unary) if unary.op == crate::hir::common::HirUnaryOpKind::Not => {
                let value = self.eval_expr(&unary.expr)?;
                Some(self.apply_not(value))
            }
            HirExpr::Binary(binary)
                if matches!(
                    binary.op,
                    HirBinaryOpKind::Eq | HirBinaryOpKind::Lt | HirBinaryOpKind::Le
                ) =>
            {
                let lhs = self.eval_expr(&binary.lhs)?;
                let rhs = self.eval_expr(&binary.rhs)?;
                let op = match binary.op {
                    HirBinaryOpKind::Eq => DiagramBinaryOp::Eq,
                    HirBinaryOpKind::Lt => DiagramBinaryOp::Lt,
                    HirBinaryOpKind::Le => DiagramBinaryOp::Le,
                    _ => unreachable!(),
                };
                self.apply_binary(op, lhs, rhs)
            }
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                let lhs = self.eval_expr(&logical.lhs)?;
                let rhs = self.eval_expr(&logical.rhs)?;
                let op = if matches!(expr, HirExpr::LogicalAnd(_)) {
                    DiagramBinaryOp::LogicalAnd
                } else {
                    DiagramBinaryOp::LogicalOr
                };
                self.apply_binary(op, lhs, rhs)
            }
            _ => None,
        }
    }

    pub(super) fn select(
        &mut self,
        condition: DiagramId,
        truthy: DiagramId,
        falsy: DiagramId,
    ) -> DiagramId {
        if truthy == falsy {
            return truthy;
        }
        if let DiagramNode::Terminal(value) = &self.nodes[condition.0] {
            return if super::cost::is_truthy(value) {
                truthy
            } else {
                falsy
            };
        }
        if let Some(cached) = self.select_cache.get(&(condition, truthy, falsy)) {
            return *cached;
        }

        let variable = [condition, truthy, falsy]
            .into_iter()
            .filter_map(|node| self.top_variable(node))
            .min()
            .expect("non-terminal select must have a branch variable");
        let edges = (0..self.domain_terminals.len())
            .map(|edge| {
                let condition = self.cofactor(condition, variable, edge);
                let truthy = self.cofactor(truthy, variable, edge);
                let falsy = self.cofactor(falsy, variable, edge);
                self.select(condition, truthy, falsy)
            })
            .collect();
        let result = self.intern_branch(variable, edges);
        self.select_cache.insert((condition, truthy, falsy), result);
        result
    }

    fn ref_value(&mut self, key: RefKey) -> Option<DiagramId> {
        let variable = *self.ref_positions.get(&key)?;
        Some(self.intern_branch(variable, self.domain_terminals.clone()))
    }

    fn apply_not(&mut self, node: DiagramId) -> DiagramId {
        if let Some(cached) = self.not_cache.get(&node) {
            return *cached;
        }
        let result = match self.nodes[node.0].clone() {
            DiagramNode::Terminal(value) => {
                self.intern_terminal(if super::cost::is_truthy(&value) {
                    AbstractValue::False
                } else {
                    AbstractValue::True
                })
            }
            DiagramNode::Branch { variable, edges } => {
                let edges = edges.into_iter().map(|edge| self.apply_not(edge)).collect();
                self.intern_branch(variable, edges)
            }
        };
        self.not_cache.insert(node, result);
        result
    }

    fn apply_binary(
        &mut self,
        op: DiagramBinaryOp,
        lhs: DiagramId,
        rhs: DiagramId,
    ) -> Option<DiagramId> {
        if let Some(cached) = self.binary_cache.get(&(op, lhs, rhs)) {
            return *cached;
        }
        let result = match (&self.nodes[lhs.0], &self.nodes[rhs.0]) {
            (DiagramNode::Terminal(lhs), DiagramNode::Terminal(rhs)) => {
                let value = match op {
                    DiagramBinaryOp::Eq => {
                        if abstract_value_eq(lhs, rhs, self.safety)? {
                            AbstractValue::True
                        } else {
                            AbstractValue::False
                        }
                    }
                    DiagramBinaryOp::Lt | DiagramBinaryOp::Le => {
                        let ordering = abstract_value_partial_cmp(lhs, rhs, self.safety)?;
                        let value = match op {
                            DiagramBinaryOp::Lt => ordering == std::cmp::Ordering::Less,
                            DiagramBinaryOp::Le => ordering != std::cmp::Ordering::Greater,
                            _ => unreachable!(),
                        };
                        if value {
                            AbstractValue::True
                        } else {
                            AbstractValue::False
                        }
                    }
                    DiagramBinaryOp::LogicalAnd => {
                        if super::cost::is_truthy(lhs) {
                            rhs.clone()
                        } else {
                            lhs.clone()
                        }
                    }
                    DiagramBinaryOp::LogicalOr => {
                        if super::cost::is_truthy(lhs) {
                            lhs.clone()
                        } else {
                            rhs.clone()
                        }
                    }
                };
                Some(self.intern_terminal(value))
            }
            _ => {
                let variable = [lhs, rhs]
                    .into_iter()
                    .filter_map(|node| self.top_variable(node))
                    .min()
                    .expect("non-terminal binary apply must have a branch variable");
                let mut edges = Vec::with_capacity(self.domain_terminals.len());
                for edge in 0..self.domain_terminals.len() {
                    let lhs = self.cofactor(lhs, variable, edge);
                    let rhs = self.cofactor(rhs, variable, edge);
                    edges.push(self.apply_binary(op, lhs, rhs)?);
                }
                Some(self.intern_branch(variable, edges))
            }
        };
        self.binary_cache.insert((op, lhs, rhs), result);
        result
    }

    fn intern_terminal(&mut self, value: AbstractValue) -> DiagramId {
        self.intern_node(DiagramNode::Terminal(value))
    }

    fn intern_branch(&mut self, variable: usize, edges: Vec<DiagramId>) -> DiagramId {
        let Some(first) = edges.first().copied() else {
            unreachable!("symbolic domain always contains base values")
        };
        if edges.iter().all(|edge| *edge == first) {
            return first;
        }
        debug_assert!(edges.iter().all(|edge| {
            self.top_variable(*edge)
                .is_none_or(|child| child > variable)
        }));
        self.intern_node(DiagramNode::Branch { variable, edges })
    }

    fn intern_node(&mut self, node: DiagramNode) -> DiagramId {
        if let Some(existing) = self.interned.get(&node) {
            return *existing;
        }
        let id = DiagramId(self.nodes.len());
        self.nodes.push(node.clone());
        self.interned.insert(node, id);
        id
    }

    fn top_variable(&self, node: DiagramId) -> Option<usize> {
        match &self.nodes[node.0] {
            DiagramNode::Terminal(_) => None,
            DiagramNode::Branch { variable, .. } => Some(*variable),
        }
    }

    fn cofactor(&self, node: DiagramId, variable: usize, edge: usize) -> DiagramId {
        match &self.nodes[node.0] {
            DiagramNode::Branch {
                variable: node_variable,
                edges,
            } if *node_variable == variable => edges[edge],
            _ => node,
        }
    }
}

/// 模拟 Lua 对两个抽象值的 `<` / `<=` 比较语义。
///
/// Lua 只允许两个数字或两个字符串之间的比较（不考虑元方法）。
/// `TruthySymbol` 是综合域里的标记值，按索引给出确定序以保证验证可判定。
/// 其余类型组合（如 Nil 与数字）在运行时会抛出错误，此处返回 `None`。
fn abstract_value_partial_cmp(
    lhs: &AbstractValue,
    rhs: &AbstractValue,
    safety: HirExprSafety,
) -> Option<std::cmp::Ordering> {
    match (lhs, rhs) {
        (AbstractValue::Integer(a), AbstractValue::Integer(b)) => Some(a.cmp(b)),
        (AbstractValue::Number(a), AbstractValue::Number(b)) => {
            f64::from_bits(*a).partial_cmp(&f64::from_bits(*b))
        }
        (AbstractValue::Integer(a), AbstractValue::Number(b)) => safety
            .values()
            .mixed_integer_number_ordering(*a, f64::from_bits(*b)),
        (AbstractValue::Number(a), AbstractValue::Integer(b)) => safety
            .values()
            .mixed_integer_number_ordering(*b, f64::from_bits(*a))
            .map(|o| o.reverse()),
        (AbstractValue::String(a), AbstractValue::String(b)) => {
            // 候选拒绝[SemanticBarrier:Locale]：PUC Lua 的字符串顺序依赖运行时 `LC_COLLATE`，抽象域不能用固定字节序验证候选（regress_392）。
            safety
                .values()
                .literal_string_order_is_binary()
                .then(|| a.cmp(b))
        }
        (AbstractValue::Int64(a), AbstractValue::Int64(b)) => Some(a.cmp(b)),
        (AbstractValue::UInt64(a), AbstractValue::UInt64(b)) => Some(a.cmp(b)),
        // 模型边界：TruthySymbol 的全序不是 Lua 语义；当前 repeatable 安全门会拒绝两个非字面量的顺序比较。
        (AbstractValue::TruthySymbol(a), AbstractValue::TruthySymbol(b)) => Some(a.cmp(b)),
        _ => None,
    }
}

/// 模拟 Lua `==` 对抽象值的原始判等语义。
///
/// 结果值等价性仍需区分 Integer/Number，因为 Lua 5.3+ 的 `math.type` 能观察表示；只有
/// `==` 运算本身会在整数与浮点数之间做精确数值比较。浮点同类比较直接使用 IEEE 754
/// `==`，从而让正负零相等、NaN 与任何值（包括自身）都不相等。
fn abstract_value_eq(
    lhs: &AbstractValue,
    rhs: &AbstractValue,
    safety: HirExprSafety,
) -> Option<bool> {
    match (lhs, rhs) {
        (AbstractValue::Number(lhs), AbstractValue::Number(rhs)) => {
            Some(f64::from_bits(*lhs) == f64::from_bits(*rhs))
        }
        (AbstractValue::Integer(integer), AbstractValue::Number(number))
        | (AbstractValue::Number(number), AbstractValue::Integer(integer)) => safety
            .values()
            .mixed_integer_number_equal(*integer, f64::from_bits(*number)),
        _ => Some(lhs == rhs),
    }
}

pub(super) struct SynthesisContext<'a> {
    pub(super) decision: &'a HirDecisionExpr,
    verifier: SymbolicVerifier,
    node_values: BTreeMap<HirDecisionNodeRef, DiagramId>,
}

impl<'a> SynthesisContext<'a> {
    pub(super) fn new(
        decision: &'a HirDecisionExpr,
        refs: Vec<RefKey>,
        safety: HirExprSafety,
    ) -> Self {
        let domain = build_domain(decision, safety);
        Self {
            decision,
            verifier: SymbolicVerifier::new(refs, domain, safety),
            node_values: BTreeMap::new(),
        }
    }

    pub(super) fn eval_node(&mut self, node_ref: HirDecisionNodeRef) -> Option<DiagramId> {
        if let Some(cached) = self.node_values.get(&node_ref) {
            return Some(*cached);
        }
        let node = self.decision.nodes.get(node_ref.index())?;
        let test_expr = node.test.clone();
        let truthy_target = node.truthy.clone();
        let falsy_target = node.falsy.clone();
        let test = self.verifier.eval_expr(&test_expr)?;
        let truthy = self.eval_target(&truthy_target, test)?;
        let falsy = self.eval_target(&falsy_target, test)?;
        let value = self.verifier.select(test, truthy, falsy);
        self.node_values.insert(node_ref, value);
        Some(value)
    }

    fn eval_target(&mut self, target: &HirDecisionTarget, current: DiagramId) -> Option<DiagramId> {
        match target {
            HirDecisionTarget::Node(next_ref) => self.eval_node(*next_ref),
            HirDecisionTarget::CurrentValue => Some(current),
            HirDecisionTarget::Expr(expr) => self.verifier.eval_expr(expr),
        }
    }

    pub(super) fn candidate_matches_node(
        &mut self,
        node_ref: HirDecisionNodeRef,
        candidate: &HirExpr,
    ) -> bool {
        let Some(expected) = self.eval_node(node_ref) else {
            return false;
        };
        self.verifier.eval_expr(candidate) == Some(expected)
    }
}

pub(super) fn collect_refs_from_decision(decision: &HirDecisionExpr) -> Vec<RefKey> {
    let mut refs = BTreeSet::new();
    for node in &decision.nodes {
        collect_refs_from_expr(&node.test, &mut refs);
        collect_refs_from_target(&node.truthy, &mut refs);
        collect_refs_from_target(&node.falsy, &mut refs);
    }
    refs.into_iter().collect()
}

pub(super) fn collect_refs_from_expr(expr: &HirExpr, refs: &mut BTreeSet<RefKey>) {
    if let Some(key) = RefKey::from_expr(expr) {
        refs.insert(key);
        return;
    }
    match expr {
        HirExpr::Unary(unary) => collect_refs_from_expr(&unary.expr, refs),
        HirExpr::Binary(binary) => {
            collect_refs_from_expr(&binary.lhs, refs);
            collect_refs_from_expr(&binary.rhs, refs);
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            collect_refs_from_expr(&logical.lhs, refs);
            collect_refs_from_expr(&logical.rhs, refs);
        }
        _ => {}
    }
}

pub(super) fn collect_literals_from_expr(expr: &HirExpr, literals: &mut BTreeSet<AbstractValue>) {
    if let Some(value) = AbstractValue::from_literal(expr) {
        // nil/Boolean 已固定包含在验证域中，不随表达式重复加入。
        if !matches!(
            value,
            AbstractValue::Nil | AbstractValue::False | AbstractValue::True
        ) {
            literals.insert(value);
        }
        return;
    }
    match expr {
        HirExpr::Unary(unary) => collect_literals_from_expr(&unary.expr, literals),
        HirExpr::Binary(binary) => {
            collect_literals_from_expr(&binary.lhs, literals);
            collect_literals_from_expr(&binary.rhs, literals);
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            collect_literals_from_expr(&logical.lhs, literals);
            collect_literals_from_expr(&logical.rhs, literals);
        }
        _ => {}
    }
}

fn collect_refs_from_target(target: &HirDecisionTarget, refs: &mut BTreeSet<RefKey>) {
    if let HirDecisionTarget::Expr(expr) = target {
        collect_refs_from_expr(expr, refs);
    }
}

fn build_domain(decision: &HirDecisionExpr, safety: HirExprSafety) -> Vec<AbstractValue> {
    let mut literals = BTreeSet::new();
    for node in &decision.nodes {
        collect_literals_from_expr(&node.test, &mut literals);
        collect_literals_from_target(&node.truthy, &mut literals);
        collect_literals_from_target(&node.falsy, &mut literals);
    }
    build_validation_domain(&literals, safety)
}

/// 为当前 synthesis grammar 构造完备的代表域。
///
/// 动态值只会参与 truthiness、与原始字面量的稳定 equality，以及作为最终原值返回；两个
/// fresh truthy symbol 足以区分任意两个非字面量结果。数值字面量则必须补齐所有 `==`
/// 相等但结果身份不同的表示，特别是 Integer/Number 双表示与正负零。
pub(super) fn build_validation_domain(
    literals: &BTreeSet<AbstractValue>,
    safety: HirExprSafety,
) -> Vec<AbstractValue> {
    let mut domain = BTreeSet::from([
        AbstractValue::Nil,
        AbstractValue::False,
        AbstractValue::True,
    ]);
    domain.extend(literals.iter().cloned());

    for literal in literals {
        match literal {
            AbstractValue::Integer(integer)
                if safety.values().distinguishes_integer_number_values() =>
            {
                let number = *integer as f64;
                if safety.values().mixed_integer_number_equal(*integer, number) == Some(true) {
                    domain.insert(AbstractValue::Number(number.to_bits()));
                }
                if *integer == 0 {
                    domain.insert(AbstractValue::Number(0.0f64.to_bits()));
                    domain.insert(AbstractValue::Number((-0.0f64).to_bits()));
                }
            }
            AbstractValue::Number(bits) => {
                let number = f64::from_bits(*bits);
                if number == 0.0 {
                    domain.insert(AbstractValue::Number(0.0f64.to_bits()));
                    domain.insert(AbstractValue::Number((-0.0f64).to_bits()));
                }
                if safety.values().distinguishes_integer_number_values()
                    && let Some(integer) = exact_integer_representation(number, safety)
                {
                    domain.insert(AbstractValue::Integer(integer));
                }
            }
            _ => {}
        }
    }

    domain.extend((0..EXTRA_TRUTHY_SYMBOLS).map(|index| AbstractValue::TruthySymbol(index as u8)));
    domain.into_iter().collect()
}

fn exact_integer_representation(number: f64, safety: HirExprSafety) -> Option<i64> {
    const I64_UPPER_EXCLUSIVE: f64 = 9_223_372_036_854_775_808.0;
    if !number.is_finite()
        || number.fract() != 0.0
        || number < i64::MIN as f64
        || number >= I64_UPPER_EXCLUSIVE
    {
        return None;
    }
    // 边界和整数性已在上面证明；最终 equality 复核同时排除 binary64 无法精确承载的整数。
    let integer = number as i64;
    (safety.values().mixed_integer_number_equal(integer, number) == Some(true)).then_some(integer)
}

fn collect_literals_from_target(
    target: &HirDecisionTarget,
    literals: &mut BTreeSet<AbstractValue>,
) {
    if let HirDecisionTarget::Expr(expr) = target {
        collect_literals_from_expr(expr, literals);
    }
}
