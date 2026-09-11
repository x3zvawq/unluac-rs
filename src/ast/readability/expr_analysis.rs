//! AST readability 里的共享表达式分析工具。
//!
//! 这些 helper 故意只回答“readability 是否值得继续收”的问题：
//! - 表达式复杂度
//! - 是否属于保守安全子集
//! - 跨过回调事件时名字快照是否仍稳定
//! - 是否是 copy-like / lookup-like / 机械纯值表达式
//! - 是否是能安全收回调用参数位的简单表构造
//!
//! 它们不试图替代更前层的语义分析，只给 AST readability 提供统一边界，
//! 避免各个 pass 再各写一套相似但略有偏差的判断。

use std::collections::BTreeSet;

use super::super::common::{
    AstBinaryOpKind, AstExpr, AstNameRef, AstTableField, AstTableKey, AstTargetDialect,
    AstUnaryOpKind,
};
use crate::ast::visit::{ExprNode, expr_nodes};
use crate::decompile::DecompileDialect;
use crate::value_semantics::results::LuaValueFacts;
use crate::value_semantics::{LuaComparison, LuaLiteral, LuaValueSemantics};

/// 把当前 AST 的原始字面量交给共享 Lua 值域；不从 HIR 借用改写许可。
pub(super) fn primitive_literal_comparison_value(
    op: AstBinaryOpKind,
    lhs: &AstExpr,
    rhs: &AstExpr,
    target: AstTargetDialect,
) -> Option<bool> {
    let op = match op {
        AstBinaryOpKind::Eq => LuaComparison::Eq,
        AstBinaryOpKind::Lt => LuaComparison::Lt,
        AstBinaryOpKind::Le => LuaComparison::Le,
        _ => return None,
    };
    LuaValueSemantics::for_dialect(target.version).compare(
        op,
        primitive_literal(lhs)?,
        primitive_literal(rhs)?,
    )
}

fn primitive_literal(expr: &AstExpr) -> Option<LuaLiteral<'_>> {
    match expr {
        AstExpr::Nil => Some(LuaLiteral::Nil),
        AstExpr::Boolean(value) => Some(LuaLiteral::Boolean(*value)),
        AstExpr::Integer(value) => Some(LuaLiteral::Integer(*value)),
        AstExpr::Number(value) => Some(LuaLiteral::Number(*value)),
        AstExpr::String(value) => Some(LuaLiteral::String(value)),
        _ => None,
    }
}

/// 表达式是否保证只产生布尔值。
pub(super) fn expr_is_boolean_valued(expr: &AstExpr) -> bool {
    value_facts(expr).is_boolean()
}

/// AST 只投影当前候选源码；正常结果规则与 HIR 共用，不沿用改写前的值快照。
fn value_facts(expr: &AstExpr) -> LuaValueFacts {
    match expr {
        AstExpr::Nil => LuaValueFacts::NIL,
        AstExpr::Boolean(value) => LuaValueFacts::boolean(*value),
        AstExpr::Integer(_) | AstExpr::Number(_) => LuaValueFacts::NUMERIC,
        AstExpr::String(_) => LuaValueFacts::STRING,
        // typed 常量节点保留原 proto 的锚点；结果惰性不授权复制 cdata 身份或构造求值。
        AstExpr::Int64(_) | AstExpr::UInt64(_) | AstExpr::Vector(_) | AstExpr::Complex { .. } => {
            LuaValueFacts::ANCHORED
        }
        AstExpr::FunctionExpr(_) | AstExpr::TableConstructor(_) => LuaValueFacts::RESOURCE,
        AstExpr::Unary(unary) => {
            let operand = value_facts(&unary.expr);
            match unary.op {
                AstUnaryOpKind::Not => operand.logical_not(),
                AstUnaryOpKind::Neg => operand.negated(),
                AstUnaryOpKind::Length => operand.string_length(),
                _ => LuaValueFacts::UNKNOWN,
            }
        }
        AstExpr::Binary(binary) => match binary.op {
            AstBinaryOpKind::Eq | AstBinaryOpKind::Lt | AstBinaryOpKind::Le => {
                LuaValueFacts::BOOLEAN
            }
            AstBinaryOpKind::Add
            | AstBinaryOpKind::Sub
            | AstBinaryOpKind::Mul
            | AstBinaryOpKind::Div
            | AstBinaryOpKind::FloorDiv
            | AstBinaryOpKind::Mod
            | AstBinaryOpKind::Pow => {
                value_facts(&binary.lhs).arithmetic(|| value_facts(&binary.rhs))
            }
            _ => LuaValueFacts::UNKNOWN,
        },
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => value_facts(&logical.lhs)
            .logical(matches!(expr, AstExpr::LogicalAnd(_)), || {
                value_facts(&logical.rhs)
            }),
        AstExpr::SingleValue(inner) => value_facts(inner),
        _ => LuaValueFacts::UNKNOWN,
    }
}

pub(super) fn expr_complexity(expr: &AstExpr) -> usize {
    expr_nodes(expr)
        .map(|node| match node {
            ExprNode::Expr(AstExpr::TableConstructor(table)) => {
                // 裸 record key 不属于表达式子节点，但仍占原有的一个展示成本单位。
                1 + table.fields.iter().filter(|field| {
                    matches!(field, AstTableField::Record(record) if matches!(record.key, AstTableKey::Name(_)))
                }).count()
            }
            ExprNode::Expr(_) => 1,
            // 只计直属语句数，不进入 child body 统计其表达式或 capture。
            ExprNode::Function(function) => function.body.stmts.len(),
        })
        .sum()
}

pub(super) fn is_context_safe_expr(expr: &AstExpr) -> bool {
    expr_nodes(expr).all(|node| matches!(node, ExprNode::Expr(expr) if is_context_safe_node(expr)))
}

fn is_context_safe_node(expr: &AstExpr) -> bool {
    match expr {
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_) => true,
        // 这些 AST 节点表示原 proto 的常量加载；generator 为重建常量选择的
        // cdata/vector constructor 不是原 VM 求值事件，不能反向阻止删除死加载。
        AstExpr::Int64(_) | AstExpr::UInt64(_) | AstExpr::Vector(_) | AstExpr::Complex { .. } => {
            true
        }
        AstExpr::Var(
            AstNameRef::Param(_)
            | AstNameRef::Local(_)
            | AstNameRef::SyntheticLocal(_)
            | AstNameRef::Temp(_)
            | AstNameRef::Upvalue(_)
            | AstNameRef::Environment,
        ) => true,
        AstExpr::Unary(unary) => matches!(unary.op, AstUnaryOpKind::Not),
        AstExpr::SingleValue(_) | AstExpr::LogicalAnd(_) | AstExpr::LogicalOr(_) => true,
        AstExpr::Var(AstNameRef::Global(_))
        | AstExpr::FieldAccess(_)
        | AstExpr::IndexAccess(_)
        | AstExpr::Binary(_)
        | AstExpr::Call(_)
        | AstExpr::MethodCall(_)
        | AstExpr::VarArg
        | AstExpr::TableConstructor(_)
        | AstExpr::FunctionExpr(_)
        | AstExpr::Error(_) => false,
    }
}

/// 表达式是否可以跨过可能触发回调的运行时事件而保持同一个值。
///
/// `is_context_safe_expr` 只证明表达式自身没有运行时协议；这里还要求它读取的名字不会被
/// 当前函数里的可写 capture 改变。Upvalue 的其它共享 owner 不在当前 AST 中，无法证明
/// 分配触发的 `__gc` 回调不会改写它，因此不属于稳定快照。
pub(super) fn is_stable_context_expr(
    mut expr: &AstExpr,
    mutable_snapshots: &BTreeSet<AstNameRef>,
) -> bool {
    // 根部 vararg 仍是单值语境；此例外不能放行嵌在 logical/not 内的 vararg。
    while let AstExpr::SingleValue(inner) = expr {
        expr = inner;
    }
    if matches!(expr, AstExpr::VarArg) {
        return true;
    }
    expr_nodes(expr).all(|node| {
        let ExprNode::Expr(expr) = node else {
            return false;
        };
        is_context_safe_node(expr)
            && match expr {
                AstExpr::Var(name) => {
                    !matches!(
                        name,
                        AstNameRef::Upvalue(_) | AstNameRef::Environment | AstNameRef::Global(_)
                    ) && !mutable_snapshots.contains(name)
                }
                _ => true,
            }
    })
}

pub(super) fn expr_observes_eval_order(expr: &AstExpr) -> bool {
    match expr {
        AstExpr::Var(AstNameRef::Global(_))
        | AstExpr::FieldAccess(_)
        | AstExpr::IndexAccess(_)
        | AstExpr::Call(_)
        | AstExpr::MethodCall(_) => true,
        AstExpr::Unary(_) | AstExpr::Binary(_) | AstExpr::LogicalAnd(_) | AstExpr::LogicalOr(_) => {
            true
        }
        AstExpr::TableConstructor(_) | AstExpr::FunctionExpr(_) => true,
        AstExpr::SingleValue(expr) => expr_observes_eval_order(expr),
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Vector(_)
        | AstExpr::Complex { .. }
        | AstExpr::Var(
            AstNameRef::Param(_)
            | AstNameRef::Local(_)
            | AstNameRef::SyntheticLocal(_)
            | AstNameRef::Temp(_)
            | AstNameRef::Upvalue(_)
            | AstNameRef::Environment,
        )
        | AstExpr::VarArg
        | AstExpr::Error(_) => false,
    }
}

/// 表达式结果是否是必须保留读取时点的值快照。
pub(super) fn expr_requires_ordered_snapshot(
    expr: &AstExpr,
    mutable_snapshots: &BTreeSet<AstNameRef>,
) -> bool {
    expr_observes_eval_order(expr)
        || matches!(expr, AstExpr::Var(AstNameRef::Upvalue(_)))
        || matches!(expr, AstExpr::Var(name) if mutable_snapshots.contains(name))
        || matches!(
            expr,
            AstExpr::SingleValue(inner)
                if expr_requires_ordered_snapshot(inner, mutable_snapshots)
        )
}

pub(super) fn is_stable_inline_value(expr: &AstExpr) -> bool {
    match expr {
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Vector(_)
        | AstExpr::Complex { .. } => true,
        AstExpr::SingleValue(inner) => is_stable_inline_value(inner),
        AstExpr::Var(_)
        | AstExpr::FieldAccess(_)
        | AstExpr::IndexAccess(_)
        | AstExpr::Unary(_)
        | AstExpr::Binary(_)
        | AstExpr::LogicalAnd(_)
        | AstExpr::LogicalOr(_)
        | AstExpr::Call(_)
        | AstExpr::MethodCall(_)
        | AstExpr::VarArg
        | AstExpr::TableConstructor(_)
        | AstExpr::FunctionExpr(_)
        | AstExpr::Error(_) => false,
    }
}

/// 候选 Lua 表达式的结果是否不需要旧对象 root handoff。
///
/// 这个谓词只用于证明 AST stable-copy 改写自身：`not value` 仍会读取 `value`，但结果
/// 一定是 boolean。原 bytecode initializer 的 stack-root 类别必须消费 HIR profile，
/// 不能调用这里从 AST 形状反推。
pub(super) fn result_cannot_root_collectable(expr: &AstExpr) -> bool {
    value_facts(expr).is_gc_inert()
}

/// 由正常结果种类证明 truthiness；删除求值仍须单独检查事件。
pub(super) fn constant_truthiness(expr: &AstExpr) -> Option<bool> {
    value_facts(expr).truthiness()
}

pub(super) fn is_access_base_inline_expr(expr: &AstExpr) -> bool {
    is_atomic_access_base_expr(expr) || is_named_field_chain_expr(expr)
}

pub(super) fn is_raw_global_alias_expr(expr: &AstExpr) -> bool {
    matches!(expr, AstExpr::Var(AstNameRef::Global(_)))
}

pub(super) fn is_lookup_inline_expr(expr: &AstExpr) -> bool {
    match expr {
        AstExpr::FieldAccess(access) => {
            is_atomic_access_base_expr(&access.base) || is_lookup_inline_expr(&access.base)
        }
        AstExpr::IndexAccess(access) => {
            (is_atomic_access_base_expr(&access.base) || is_lookup_inline_expr(&access.base))
                && is_context_safe_expr(&access.index)
        }
        _ => false,
    }
}

pub(super) fn is_copy_like_expr(expr: &AstExpr) -> bool {
    match expr {
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Vector(_)
        | AstExpr::Complex { .. }
        | AstExpr::Var(_) => true,
        AstExpr::SingleValue(expr) => is_copy_like_expr(expr),
        AstExpr::FieldAccess(access) => is_copy_like_expr(&access.base),
        AstExpr::IndexAccess(access) => {
            is_copy_like_expr(&access.base) && is_copy_like_expr(&access.index)
        }
        AstExpr::Unary(_)
        | AstExpr::Binary(_)
        | AstExpr::LogicalAnd(_)
        | AstExpr::LogicalOr(_)
        | AstExpr::Call(_)
        | AstExpr::MethodCall(_)
        | AstExpr::VarArg
        | AstExpr::TableConstructor(_)
        | AstExpr::FunctionExpr(_)
        | AstExpr::Error(_) => false,
    }
}

/// 收集 stable-copy 可以重复读取的声明点快照依赖。
///
/// 这里只接受不会调用元方法、分配对象或读取外部可变状态的表达式。`not` 与短路逻辑只做
/// truthiness 测试并返回已有操作数；调用方还必须证明这里收集的每个名字在候选之后没有
/// direct write、也没有被 closure 捕获，才能把声明点求值安全地搬到使用点。
///
/// 该集合故意比 [`is_copy_like_expr`] 窄：Int64/UInt64/Vector/Complex 的物化可能创建
/// cdata/vector，非有限 number 会渲染成除法，算术/比较和除 `not` 外的一元运算都可能
/// 触发元方法。
pub(super) fn collect_stable_copy_snapshot_names(
    expr: &AstExpr,
    names: &mut BTreeSet<AstNameRef>,
    target: AstTargetDialect,
) -> bool {
    if is_eventless_primitive_expr_for_target(expr, target) {
        return true;
    }
    match expr {
        AstExpr::Var(
            name @ (AstNameRef::Param(_) | AstNameRef::Local(_) | AstNameRef::SyntheticLocal(_)),
        ) => {
            names.insert(name.clone());
            true
        }
        AstExpr::SingleValue(expr) => collect_stable_copy_snapshot_names(expr, names, target),
        AstExpr::Unary(unary) if unary.op == AstUnaryOpKind::Not => {
            collect_stable_copy_snapshot_names(&unary.expr, names, target)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            collect_stable_copy_snapshot_names(&logical.lhs, names, target)
                && collect_stable_copy_snapshot_names(&logical.rhs, names, target)
        }
        _ => false,
    }
}

pub(super) fn is_stable_copy_alias_expr(expr: &AstExpr) -> bool {
    collect_stable_copy_snapshot_names(
        expr,
        &mut BTreeSet::new(),
        AstTargetDialect::new(DecompileDialect::Auto),
    )
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EventlessLiteralKind {
    Nil,
    Boolean,
    Integer(ZeroKnowledge),
    Number(ZeroKnowledge),
    String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ZeroKnowledge {
    Zero,
    NonZero,
    Unknown,
}

impl EventlessLiteralKind {
    fn integer_pair_arithmetic_is_defined(
        lhs: Self,
        rhs: Self,
        integer_arithmetic_is_defined: bool,
    ) -> bool {
        integer_arithmetic_is_defined || !matches!((lhs, rhs), (Self::Integer(_), Self::Integer(_)))
    }

    fn numeric_result(lhs: Self, rhs: Self, integer_arithmetic_is_defined: bool) -> Option<Self> {
        match (lhs, rhs) {
            (Self::Integer(_), Self::Integer(_)) => {
                integer_arithmetic_is_defined.then_some(Self::Integer(ZeroKnowledge::Unknown))
            }
            (Self::Integer(_), Self::Number(_))
            | (Self::Number(_), Self::Integer(_))
            | (Self::Number(_), Self::Number(_)) => Some(Self::Number(ZeroKnowledge::Unknown)),
            _ => None,
        }
    }

    fn number_result(lhs: Self, rhs: Self, integer_arithmetic_is_defined: bool) -> Option<Self> {
        (lhs.is_numeric()
            && rhs.is_numeric()
            && Self::integer_pair_arithmetic_is_defined(lhs, rhs, integer_arithmetic_is_defined))
        .then_some(Self::Number(ZeroKnowledge::Unknown))
    }

    fn is_numeric(self) -> bool {
        matches!(self, Self::Integer(_) | Self::Number(_))
    }

    fn is_definitely_nonzero_numeric(self) -> bool {
        matches!(
            self,
            Self::Integer(ZeroKnowledge::NonZero) | Self::Number(ZeroKnowledge::NonZero)
        )
    }
}

/// 递归证明 primitive literal 运算树的求值不会 lookup、调用元方法或抛错。
///
/// 这里只保留求值所需的类型与“确定非零”事实，不计算结果；因此字符串排序采用何种
/// locale 不影响丢弃证明。Lua 5.1/5.2 chunk 可以声明自定义 integral-number 布局，
/// 但该布局事实尚未进入 AST target；目标无关调用和这两个目标都会拒绝 Integer 算术。
fn eventless_literal_kind(
    expr: &AstExpr,
    integer_arithmetic_is_defined: bool,
) -> Option<EventlessLiteralKind> {
    match expr {
        AstExpr::Nil => Some(EventlessLiteralKind::Nil),
        AstExpr::Boolean(_) => Some(EventlessLiteralKind::Boolean),
        AstExpr::Integer(value) => Some(EventlessLiteralKind::Integer(if *value == 0 {
            ZeroKnowledge::Zero
        } else {
            ZeroKnowledge::NonZero
        })),
        AstExpr::Number(value) => Some(EventlessLiteralKind::Number(if *value == 0.0 {
            ZeroKnowledge::Zero
        } else {
            ZeroKnowledge::NonZero
        })),
        AstExpr::String(_) => Some(EventlessLiteralKind::String),
        AstExpr::SingleValue(inner) => eventless_literal_kind(inner, integer_arithmetic_is_defined),
        AstExpr::Unary(unary) => {
            let operand = eventless_literal_kind(&unary.expr, integer_arithmetic_is_defined)?;
            match unary.op {
                AstUnaryOpKind::Not => Some(EventlessLiteralKind::Boolean),
                AstUnaryOpKind::Neg
                    if operand.is_numeric()
                        && (integer_arithmetic_is_defined
                            || !matches!(operand, EventlessLiteralKind::Integer(_))) =>
                {
                    Some(operand)
                }
                AstUnaryOpKind::BitNot if matches!(operand, EventlessLiteralKind::Integer(_)) => {
                    Some(EventlessLiteralKind::Integer(ZeroKnowledge::Unknown))
                }
                AstUnaryOpKind::Length if operand == EventlessLiteralKind::String => {
                    Some(EventlessLiteralKind::Integer(ZeroKnowledge::Unknown))
                }
                AstUnaryOpKind::Neg | AstUnaryOpKind::BitNot | AstUnaryOpKind::Length => None,
            }
        }
        AstExpr::Binary(binary) => {
            let lhs = eventless_literal_kind(&binary.lhs, integer_arithmetic_is_defined)?;
            let rhs = eventless_literal_kind(&binary.rhs, integer_arithmetic_is_defined)?;
            match binary.op {
                AstBinaryOpKind::Add | AstBinaryOpKind::Sub | AstBinaryOpKind::Mul => {
                    EventlessLiteralKind::numeric_result(lhs, rhs, integer_arithmetic_is_defined)
                }
                AstBinaryOpKind::Div if lhs.is_numeric() && rhs.is_definitely_nonzero_numeric() => {
                    EventlessLiteralKind::number_result(lhs, rhs, integer_arithmetic_is_defined)
                }
                AstBinaryOpKind::Pow => {
                    EventlessLiteralKind::number_result(lhs, rhs, integer_arithmetic_is_defined)
                }
                AstBinaryOpKind::FloorDiv | AstBinaryOpKind::Mod
                    if rhs.is_definitely_nonzero_numeric() =>
                {
                    EventlessLiteralKind::numeric_result(lhs, rhs, integer_arithmetic_is_defined)
                }
                AstBinaryOpKind::BitAnd
                | AstBinaryOpKind::BitOr
                | AstBinaryOpKind::BitXor
                | AstBinaryOpKind::Shl
                | AstBinaryOpKind::Shr
                    if matches!(lhs, EventlessLiteralKind::Integer(_))
                        && matches!(rhs, EventlessLiteralKind::Integer(_)) =>
                {
                    Some(EventlessLiteralKind::Integer(ZeroKnowledge::Unknown))
                }
                AstBinaryOpKind::Eq => Some(EventlessLiteralKind::Boolean),
                AstBinaryOpKind::Lt | AstBinaryOpKind::Le
                    if (lhs.is_numeric() && rhs.is_numeric())
                        || (lhs == EventlessLiteralKind::String
                            && rhs == EventlessLiteralKind::String) =>
                {
                    Some(EventlessLiteralKind::Boolean)
                }
                AstBinaryOpKind::Div
                | AstBinaryOpKind::FloorDiv
                | AstBinaryOpKind::Mod
                | AstBinaryOpKind::BitAnd
                | AstBinaryOpKind::BitOr
                | AstBinaryOpKind::BitXor
                | AstBinaryOpKind::Shl
                | AstBinaryOpKind::Shr
                | AstBinaryOpKind::Concat
                | AstBinaryOpKind::Lt
                | AstBinaryOpKind::Le => None,
            }
        }
        AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Vector(_)
        | AstExpr::Complex { .. }
        | AstExpr::Var(_)
        | AstExpr::FieldAccess(_)
        | AstExpr::IndexAccess(_)
        | AstExpr::LogicalAnd(_)
        | AstExpr::LogicalOr(_)
        | AstExpr::Call(_)
        | AstExpr::MethodCall(_)
        | AstExpr::VarArg
        | AstExpr::TableConstructor(_)
        | AstExpr::FunctionExpr(_)
        | AstExpr::Error(_) => None,
    }
}

/// Primitive literal expression that can be re-evaluated without VM events and whose generated
/// source preserves that property for the selected target.
///
/// Non-finite numbers are excluded because the generator materializes them as arithmetic. The
/// dialect fact is needed for integer arithmetic: Lua 5.1/5.2 may use a custom integral-number
/// layout, while the newer PUC dialects, LuaJIT, and Luau have a defined model here.
pub(super) fn is_eventless_primitive_expr_for_target(
    expr: &AstExpr,
    target: AstTargetDialect,
) -> bool {
    fn has_stable_literal_materialization(
        expr: &AstExpr,
        integer_arithmetic_is_defined: bool,
    ) -> bool {
        match expr {
            AstExpr::Number(value) => value.is_finite(),
            AstExpr::SingleValue(inner) => {
                has_stable_literal_materialization(inner, integer_arithmetic_is_defined)
            }
            AstExpr::Unary(unary) => {
                has_stable_literal_materialization(&unary.expr, integer_arithmetic_is_defined)
            }
            AstExpr::Binary(binary) => {
                let locale_sensitive_string_order =
                    matches!(binary.op, AstBinaryOpKind::Lt | AstBinaryOpKind::Le)
                        && eventless_literal_kind(&binary.lhs, integer_arithmetic_is_defined)
                            == Some(EventlessLiteralKind::String)
                        && eventless_literal_kind(&binary.rhs, integer_arithmetic_is_defined)
                            == Some(EventlessLiteralKind::String);
                !locale_sensitive_string_order
                    && has_stable_literal_materialization(
                        &binary.lhs,
                        integer_arithmetic_is_defined,
                    )
                    && has_stable_literal_materialization(
                        &binary.rhs,
                        integer_arithmetic_is_defined,
                    )
            }
            AstExpr::Nil | AstExpr::Boolean(_) | AstExpr::Integer(_) | AstExpr::String(_) => true,
            AstExpr::Int64(_)
            | AstExpr::UInt64(_)
            | AstExpr::Vector(_)
            | AstExpr::Complex { .. }
            | AstExpr::Var(_)
            | AstExpr::FieldAccess(_)
            | AstExpr::IndexAccess(_)
            | AstExpr::LogicalAnd(_)
            | AstExpr::LogicalOr(_)
            | AstExpr::Call(_)
            | AstExpr::MethodCall(_)
            | AstExpr::VarArg
            | AstExpr::TableConstructor(_)
            | AstExpr::FunctionExpr(_)
            | AstExpr::Error(_) => false,
        }
    }

    let integer_arithmetic_is_defined = target_defines_integer_literal_arithmetic(target);
    has_stable_literal_materialization(expr, integer_arithmetic_is_defined)
        && eventless_literal_kind(expr, integer_arithmetic_is_defined).is_some()
}

fn stable_literal_equality(
    op: AstBinaryOpKind,
    lhs: &AstExpr,
    rhs: &AstExpr,
    dynamic_primitive_equality_is_eventless: bool,
) -> bool {
    dynamic_primitive_equality_is_eventless
        && op == AstBinaryOpKind::Eq
        && (is_metamethod_inert_literal(lhs) || is_metamethod_inert_literal(rhs))
}

fn is_metamethod_inert_literal(expr: &AstExpr) -> bool {
    matches!(
        expr,
        AstExpr::Nil
            | AstExpr::Boolean(_)
            | AstExpr::Integer(_)
            | AstExpr::Number(_)
            | AstExpr::String(_)
    )
}

fn target_defines_integer_literal_arithmetic(target: AstTargetDialect) -> bool {
    matches!(
        target.version,
        DecompileDialect::Lua53
            | DecompileDialect::Lua54
            | DecompileDialect::Lua55
            | DecompileDialect::Luajit
            | DecompileDialect::Luau
    )
}

fn target_defines_dynamic_primitive_equality(target: AstTargetDialect) -> bool {
    matches!(
        target.version,
        DecompileDialect::Lua51
            | DecompileDialect::Lua52
            | DecompileDialect::Lua53
            | DecompileDialect::Lua54
            | DecompileDialect::Lua55
            | DecompileDialect::Luau
    )
}

#[derive(Debug, Clone, Copy)]
struct DiscardSafetyFacts {
    integer_arithmetic_is_defined: bool,
    dynamic_primitive_equality_is_eventless: bool,
}

/// 表达式的整次求值能否在结果无人使用时删除。
///
/// `not` 只测试 truthiness，短路逻辑只选择已有操作数，裸 vararg 只读取当前调用帧；
/// primitive literal 运算树按类型、错误条件和目标整数语义递归证明。其它访问、调用和
/// 对象构造仍需由各自的事件/生命周期证明处理。目标无关调用会保守拒绝 Integer 算术
/// 以及 dynamic/primitive equality。
pub(super) fn is_discard_safe_expr(expr: &AstExpr) -> bool {
    is_discard_safe_expr_with_facts(
        expr,
        DiscardSafetyFacts {
            integer_arithmetic_is_defined: false,
            dynamic_primitive_equality_is_eventless: false,
        },
    )
}

pub(super) fn is_discard_safe_expr_for_target(expr: &AstExpr, target: AstTargetDialect) -> bool {
    is_discard_safe_expr_with_facts(
        expr,
        DiscardSafetyFacts {
            integer_arithmetic_is_defined: target_defines_integer_literal_arithmetic(target),
            // LuaJIT cdata metatypes may invoke `__eq` even when the other operand is nil,
            // boolean, number, or string. PUC/Luau use the standard primitive mismatch path;
            // unresolved Auto has no target proof and remains conservative.
            dynamic_primitive_equality_is_eventless: target_defines_dynamic_primitive_equality(
                target,
            ),
        },
    )
}

fn is_discard_safe_expr_with_facts(expr: &AstExpr, facts: DiscardSafetyFacts) -> bool {
    match expr {
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Vector(_)
        | AstExpr::Complex { .. } => true,
        AstExpr::Var(
            AstNameRef::Param(_)
            | AstNameRef::Local(_)
            | AstNameRef::SyntheticLocal(_)
            | AstNameRef::Temp(_)
            | AstNameRef::Upvalue(_)
            | AstNameRef::Environment,
        ) => true,
        AstExpr::VarArg => true,
        AstExpr::SingleValue(expr) => is_discard_safe_expr_with_facts(expr, facts),
        AstExpr::Unary(unary) if unary.op == AstUnaryOpKind::Not => {
            is_discard_safe_expr_with_facts(&unary.expr, facts)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            is_discard_safe_expr_with_facts(&logical.lhs, facts)
                && is_discard_safe_expr_with_facts(&logical.rhs, facts)
        }
        AstExpr::Binary(binary)
            if stable_literal_equality(
                binary.op,
                &binary.lhs,
                &binary.rhs,
                facts.dynamic_primitive_equality_is_eventless,
            ) =>
        {
            is_discard_safe_expr_with_facts(&binary.lhs, facts)
                && is_discard_safe_expr_with_facts(&binary.rhs, facts)
        }
        AstExpr::Unary(_) | AstExpr::Binary(_)
            if eventless_literal_kind(expr, facts.integer_arithmetic_is_defined).is_some() =>
        {
            true
        }
        AstExpr::Var(AstNameRef::Global(_))
        | AstExpr::FieldAccess(_)
        | AstExpr::IndexAccess(_)
        | AstExpr::Unary(_)
        | AstExpr::Binary(_)
        | AstExpr::Call(_)
        | AstExpr::MethodCall(_)
        | AstExpr::TableConstructor(_)
        | AstExpr::FunctionExpr(_)
        | AstExpr::Error(_) => false,
    }
}

pub(super) fn is_mechanical_run_inline_expr(expr: &AstExpr) -> bool {
    match expr {
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Vector(_)
        | AstExpr::Complex { .. }
        | AstExpr::Var(_) => true,
        AstExpr::SingleValue(expr) => is_mechanical_run_inline_expr(expr),
        AstExpr::FieldAccess(access) => is_mechanical_run_inline_expr(&access.base),
        AstExpr::IndexAccess(access) => {
            is_mechanical_run_inline_expr(&access.base)
                && is_mechanical_run_inline_expr(&access.index)
        }
        AstExpr::Unary(unary) => is_mechanical_run_inline_expr(&unary.expr),
        AstExpr::Binary(binary) => {
            is_mechanical_run_inline_expr(&binary.lhs) && is_mechanical_run_inline_expr(&binary.rhs)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            is_mechanical_run_inline_expr(&logical.lhs)
                && is_mechanical_run_inline_expr(&logical.rhs)
        }
        AstExpr::Call(_)
        | AstExpr::MethodCall(_)
        | AstExpr::VarArg
        | AstExpr::TableConstructor(_)
        | AstExpr::FunctionExpr(_)
        | AstExpr::Error(_) => false,
    }
}

/// 直接终态 return 能否消费该表达式而不展开额外返回值。
///
/// `local value = expr; return value` 的 local initializer 处于目标计数上下文，
/// 因此裸 `Call` / `MethodCall` / `VarArg` 在移到 return 后可能从单值变成多值；
/// `SingleValue` 则是 lowering 已经保留的单值边界。其它 AST 表达式在运算、访问、
/// 构造器或函数表达式位置都只产出一个值。`Error` 继续保留为 residual，避免把未知
/// 语义伪装成可读源码。
pub(super) fn is_direct_return_inline_expr(expr: &AstExpr) -> bool {
    !matches!(
        expr,
        AstExpr::Call(_) | AstExpr::MethodCall(_) | AstExpr::VarArg | AstExpr::Error(_)
    )
}

/// 返回终态拼接链的展示成本；诊断、非有限或过深的形状继续交给普通复杂度阈值。
///
/// 这不是新的语义证明：调用方仍须先通过 `is_direct_return_inline_expr` 和唯一
/// 相邻 return 的 use-site 规则。这里仅把一串有限的 `..` 段按段数计费，避免
/// `type(x)` 这类单个小段把机械的整串终态结果挡在默认阈值之外。每个叶段仍有
/// 独立复杂度上限，因而不会借此放行任意大的嵌套表达式。
pub(super) fn direct_return_concat_cost(expr: &AstExpr) -> Option<usize> {
    const MAX_PARTS: usize = 10;
    const MAX_PART_COMPLEXITY: usize = 3;

    fn collect_parts(expr: &AstExpr, parts: &mut usize) -> bool {
        match expr {
            AstExpr::Binary(binary) if binary.op == AstBinaryOpKind::Concat => {
                collect_parts(&binary.lhs, parts) && collect_parts(&binary.rhs, parts)
            }
            AstExpr::Error(_) => false,
            AstExpr::Number(value) if !value.is_finite() => false,
            _ if expr_complexity(expr) <= MAX_PART_COMPLEXITY
                && is_direct_return_budget_term_safe(expr) =>
            {
                *parts = parts.saturating_add(1);
                *parts <= MAX_PARTS
            }
            _ => false,
        }
    }

    let mut parts = 0;
    (matches!(expr, AstExpr::Binary(binary) if binary.op == AstBinaryOpKind::Concat)
        && collect_parts(expr, &mut parts)
        && parts >= 2)
        .then_some(parts)
}

/// 返回终态短路链的展示成本；其余表达式继续使用完整 AST 复杂度阈值。
///
/// `and`/`or` 的嵌套本身不会改变任何运行时事件；这里仅按有限叶子数计费，避免
/// HIR 已经证明为单次值合流的长短路壳被机械 local 隔开。叶子仍受独立复杂度上限
/// 约束，因此不会借这条展示规则放行任意大的调用、查表或构造器树。
pub(super) fn direct_return_logical_cost(expr: &AstExpr) -> Option<usize> {
    const MAX_TERMS: usize = 12;
    const MAX_TERM_COMPLEXITY: usize = 3;

    fn collect_terms(expr: &AstExpr, terms: &mut usize) -> bool {
        match expr {
            AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
                collect_terms(&logical.lhs, terms) && collect_terms(&logical.rhs, terms)
            }
            AstExpr::Error(_) => false,
            AstExpr::Number(value) if !value.is_finite() => false,
            _ if expr_complexity(expr) <= MAX_TERM_COMPLEXITY
                && is_direct_return_budget_term_safe(expr) =>
            {
                *terms = terms.saturating_add(1);
                *terms <= MAX_TERMS
            }
            _ => false,
        }
    }

    let mut terms = 0;
    (matches!(expr, AstExpr::LogicalAnd(_) | AstExpr::LogicalOr(_))
        && collect_terms(expr, &mut terms)
        && terms >= 2)
        .then_some(terms)
}

/// 展示预算的叶子不能偷偷携带诊断或由生成器改写成额外算术事件的非有限值。
///
/// 调用方已经先限制了整棵叶子的复杂度；这里因此只递归检查该小叶子内部，且拒绝
/// 函数体未知的 `FunctionExpr`。这不是求值安全证明，调用方仍须执行 DirectReturn
/// 的 binding、顺序、root 与多返回门槛。
fn is_direct_return_budget_term_safe(expr: &AstExpr) -> bool {
    match expr {
        AstExpr::Number(value) => value.is_finite(),
        AstExpr::Complex { real, imag } => real.is_finite() && imag.is_finite(),
        AstExpr::Vector(vector) => vector
            .components
            .iter()
            .all(|bits| f32::from_bits(*bits).is_finite()),
        AstExpr::FieldAccess(access) => is_direct_return_budget_term_safe(&access.base),
        AstExpr::IndexAccess(access) => {
            is_direct_return_budget_term_safe(&access.base)
                && is_direct_return_budget_term_safe(&access.index)
        }
        AstExpr::Unary(unary) => is_direct_return_budget_term_safe(&unary.expr),
        AstExpr::Binary(binary) => {
            is_direct_return_budget_term_safe(&binary.lhs)
                && is_direct_return_budget_term_safe(&binary.rhs)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            is_direct_return_budget_term_safe(&logical.lhs)
                && is_direct_return_budget_term_safe(&logical.rhs)
        }
        AstExpr::Call(call) => {
            is_direct_return_budget_term_safe(&call.callee)
                && call.args.iter().all(is_direct_return_budget_term_safe)
        }
        AstExpr::MethodCall(call) => {
            is_direct_return_budget_term_safe(&call.receiver)
                && call.args.iter().all(is_direct_return_budget_term_safe)
        }
        AstExpr::SingleValue(inner) => is_direct_return_budget_term_safe(inner),
        AstExpr::TableConstructor(table) => table.fields.iter().all(|field| match field {
            AstTableField::Array(value) => is_direct_return_budget_term_safe(value),
            AstTableField::Record(record) => {
                let key_safe = match &record.key {
                    AstTableKey::Name(_) => true,
                    AstTableKey::Expr(key) => is_direct_return_budget_term_safe(key),
                };
                key_safe && is_direct_return_budget_term_safe(&record.value)
            }
        }),
        AstExpr::FunctionExpr(_) | AstExpr::Error(_) => false,
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Var(_)
        | AstExpr::VarArg => true,
    }
}

/// 多值 `return` 中可安全收回的单值表达式。
///
/// 现有的 context-safe 子集已经覆盖不会观察运行时事件的表达式。额外放行的只有
/// “比较结果为布尔值”的表达式树，且比较操作数仍必须属于 context-safe 子集（或是
/// 已处于单值比较操作数语境的 vararg）；这样
/// 比较本身即使触发 Lua 的比较协议，也不会把对象结果从 local root 搬到别的求值点，
/// 并且不会产生多返回值。短路/`not` 只在整棵树仍保证布尔结果时递归接受。
pub(super) fn is_multi_return_inline_expr(expr: &AstExpr) -> bool {
    if is_context_safe_expr(expr) {
        return true;
    }
    if !expr_is_boolean_valued(expr) {
        return false;
    }
    match expr {
        AstExpr::Binary(binary)
            if matches!(
                binary.op,
                AstBinaryOpKind::Eq | AstBinaryOpKind::Lt | AstBinaryOpKind::Le
            ) =>
        {
            is_multi_return_comparison_operand(&binary.lhs)
                && is_multi_return_comparison_operand(&binary.rhs)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            is_multi_return_inline_expr(&logical.lhs) && is_multi_return_inline_expr(&logical.rhs)
        }
        AstExpr::Unary(unary) if unary.op == AstUnaryOpKind::Not => {
            is_multi_return_inline_expr(&unary.expr)
        }
        AstExpr::SingleValue(inner) => is_multi_return_inline_expr(inner),
        _ => false,
    }
}

fn is_multi_return_comparison_operand(expr: &AstExpr) -> bool {
    is_context_safe_expr(expr)
        || matches!(expr, AstExpr::VarArg)
        || matches!(expr, AstExpr::SingleValue(inner) if matches!(inner.as_ref(), AstExpr::VarArg))
}

pub(super) fn is_call_arg_constructor_inline_expr(expr: &AstExpr) -> bool {
    let AstExpr::TableConstructor(table) = expr else {
        return false;
    };
    table.fields.iter().all(|field| match field {
        AstTableField::Array(value) => is_call_arg_constructor_field_expr(value),
        AstTableField::Record(record) => {
            let key_is_safe = match &record.key {
                AstTableKey::Name(_) => true,
                AstTableKey::Expr(key) => is_context_safe_expr(key) || is_lookup_inline_expr(key),
            };
            key_is_safe && is_call_arg_constructor_field_expr(&record.value)
        }
    })
}

fn is_call_arg_constructor_field_expr(expr: &AstExpr) -> bool {
    is_context_safe_expr(expr)
        || is_lookup_inline_expr(expr)
        || is_call_arg_constructor_inline_expr(expr)
}

fn is_named_field_chain_expr(expr: &AstExpr) -> bool {
    let AstExpr::FieldAccess(access) = expr else {
        return false;
    };
    is_atomic_access_base_expr(&access.base) || is_named_field_chain_expr(&access.base)
}

fn is_atomic_access_base_expr(expr: &AstExpr) -> bool {
    matches!(
        expr,
        AstExpr::Nil
            | AstExpr::Boolean(_)
            | AstExpr::Integer(_)
            | AstExpr::Number(_)
            | AstExpr::String(_)
            | AstExpr::Int64(_)
            | AstExpr::UInt64(_)
            | AstExpr::Vector(_)
            | AstExpr::Complex { .. }
            | AstExpr::Var(_)
    )
}
