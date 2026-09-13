//! 索引式建表的运行时操作数约束。
//!
//! HIR lowering 已保留 Indexed/Template 分配事实；本模块判断候选常量替换是否把运行时
//! 字段变成编译器模板初始化。`local x=true; {a,x,c}` 必须保留运行时 x，否则
//! 模板序列化会裁掉尾部 nil 槽并改变数组容量。保留结论随原 binding 进入 AST，
//! 不让 AST 读取 TNEW/TDUP 或重新分析原始寄存器。
//! 构造区域吸收常量后也由本模块保持运行时读取：例如 `{a,1<2,c}` 折叠后生成
//! `local x=true; {a,x,c}`。只物化无事件的字面量叶子，不提前执行字段运算或调用。
//! 已有模板同样遵守原容量：`local x=true; {true,a,x}` 不能把 x 放入第 3 个模板槽。
//! 本层只投影字段位置；操作数约束和候选容量查询由共享 table 语义拥有。
//! 原始 hash 键集合随分配保留；`{true,[5]=x}` 中的运行时 x 不能成为新的稀疏模板项。

use super::common::{HirBinaryOpKind, HirExpr, HirStmt, HirTableField, HirUnaryOpKind, TempId};
use super::rewrite::replace_temp_in_expr;
use super::traverse::{
    traverse_hir_call_children, traverse_hir_decision_children, traverse_hir_expr_children,
    traverse_hir_table_constructor_children,
};
use super::visit::{HirVisitor, visit_stmts};
use crate::value_semantics::table::{
    TableFieldRef, TableRuntimeOperand, runtime_table_operand, table_constant_kind,
};

/// 原 Luau 容量由 lowering 发布；这里只投影最终裸字段名和 pack tail 的语法位置。
pub(in crate::hir) fn matches_luau_allocation(table: &super::common::HirTableConstructor) -> bool {
    let super::common::HirTableAllocation::Luau(allocation) = table.allocation else {
        return true;
    };
    let mut next_array = 0;
    let fields = table.fields.iter().map(|field| {
        if table.allocation.permits_named_record_keys()
            && let HirTableField::Record(record) = field
            && let HirExpr::String(key) = &record.key
            && let Some(name) = key.as_utf8()
            && crate::decompile::DecompileDialect::Luau.is_identifier_name(name)
        {
            return TableFieldRef::Named(name);
        }
        field_ref(field, &mut next_array)
    });
    let tail = table
        .trailing_multivalue
        .as_ref()
        .map(|tail| TableFieldRef::Array {
            index: 0,
            value: tail.as_expr(),
        });
    allocation.matches_luau(
        fields.chain(tail),
        table
            .trailing_multivalue
            .as_ref()
            .is_some_and(|tail| matches!(tail.as_expr(), HirExpr::VarArg)),
    )
}

/// builder 只投影本次拟晋升的连续整数 record，容量规则由共享模板语义计算。
pub(in crate::hir) fn candidate_template_array_capacity(
    table: &super::common::HirTableConstructor,
    count: usize,
) -> Option<u32> {
    let count = count + usize::from(table.trailing_multivalue.is_some());
    let mut next_array = 0;
    let fields = table.fields.iter().map(|field| {
        let projected = field_ref(field, &mut next_array);
        if let HirTableField::Record(record) = field
            && record.key == HirExpr::Integer(i64::from(next_array) + 1)
        {
            next_array += 1;
        }
        projected
    });
    crate::value_semantics::table::template_array_capacity(fields, count as u32)
}

#[derive(Default)]
pub(in crate::hir) struct RuntimeTableOperandRequirements {
    pub keys: bool,
    pub values: bool,
}

impl RuntimeTableOperandRequirements {
    pub fn any(&self) -> bool {
        self.keys || self.values
    }
}

/// 当前树还需物化的常量操作数；构造器合并与调用帧前缀共同消费分配约束。
pub(in crate::hir) fn runtime_table_operand_requirements(
    table: &super::common::HirTableConstructor,
) -> RuntimeTableOperandRequirements {
    #[derive(Default)]
    struct Probe(RuntimeTableOperandRequirements);
    impl Probe {
        fn table(&mut self, table: &super::common::HirTableConstructor) {
            let Some(constraint) = table.allocation.initialization_constraint() else {
                return;
            };
            let mut next_array = 0;
            for field in &table.fields {
                match runtime_table_operand(constraint, field_ref(field, &mut next_array)) {
                    Some(TableRuntimeOperand::Key) => self.0.keys = true,
                    Some(TableRuntimeOperand::Value) => self.0.values = true,
                    None => {}
                }
            }
        }
    }
    impl HirVisitor<'_> for Probe {
        fn visit_expr(&mut self, expr: &HirExpr) {
            if let HirExpr::TableConstructor(table) = expr {
                self.table(table);
            }
        }
    }
    let mut probe = Probe::default();
    probe.table(table);
    super::visit::visit_table_constructor(table, &mut probe);
    probe.0
}

/// 完整构造区域提交时只物化无事件的字面量叶子，运算与错误留在原字段位置。
/// 与只读需求查询消费相同的字段约束，调用方先证明新增声明的位置合法。
pub(in crate::hir) fn materialize_runtime_table_operands(
    table: &mut super::common::HirTableConstructor,
    next_local: &mut usize,
) -> Vec<HirStmt> {
    let mut operands = RuntimeTableOperands {
        next_local,
        values: Vec::new(),
    };
    operands.table(table);
    operands
        .values
        .into_iter()
        .map(|(value, local)| {
            HirStmt::LocalDecl(Box::new(super::common::HirLocalDecl {
                bindings: vec![local],
                values: super::common::HirValuePack::fixed(vec![value]),
                initializer_merge_transaction: None,
            }))
        })
        .collect()
}

struct RuntimeTableOperands<'a> {
    next_local: &'a mut usize,
    values: Vec<(HirExpr, super::common::LocalId)>,
}

impl RuntimeTableOperands<'_> {
    fn expr(&mut self, expr: &mut HirExpr) {
        traverse_hir_expr_children!(
            expr, iter = iter_mut, borrow = [&mut],
            expr(child) => { self.expr(child); },
            call(call) => { self.call(call); },
            decision(decision) => {
                traverse_hir_decision_children!(
                    decision, iter = iter_mut, borrow = [&mut],
                    expr(child) => { self.expr(child); },
                    condition(child) => { self.expr(child); }
                );
            },
            table_constructor(table) => { self.table(table); },
            capture(_capture) => {}
        );
    }

    fn call(&mut self, call: &mut super::common::HirCallExpr) {
        traverse_hir_call_children!(
            call, iter = iter_mut, borrow = [&mut],
            expr(child) => { self.expr(child); },
            tail_call(child) => { self.call(child); }
        );
    }

    fn table(&mut self, table: &mut super::common::HirTableConstructor) {
        traverse_hir_table_constructor_children!(
            table, iter = iter_mut, opt = as_mut, borrow = [&mut],
            expr(child) => { self.expr(child); },
            tail_call(child) => { self.call(child); }
        );
        let Some(constraint) = table.allocation.initialization_constraint() else {
            return;
        };
        let mut next_array = 0;
        for field in &mut table.fields {
            let operand = runtime_table_operand(constraint, field_ref(field, &mut next_array));
            let expr = match (operand, field) {
                (Some(TableRuntimeOperand::Value), HirTableField::Array(value)) => value,
                (Some(TableRuntimeOperand::Value), HirTableField::Record(record)) => {
                    &mut record.value
                }
                (Some(TableRuntimeOperand::Key), HirTableField::Record(record)) => &mut record.key,
                _ => continue,
            };
            materialize_constant_leaf(expr, self.next_local, &mut self.values);
        }
    }
}

fn field_ref<'a>(field: &'a HirTableField, next_array: &mut u32) -> TableFieldRef<'a, HirExpr> {
    match field {
        HirTableField::Array(value) => {
            *next_array += 1;
            TableFieldRef::Array {
                index: *next_array,
                value,
            }
        }
        HirTableField::Record(record) => TableFieldRef::Record {
            key: &record.key,
            value: &record.value,
        },
    }
}

fn materialize_constant_leaf(
    expr: &mut HirExpr,
    next_local: &mut usize,
    operands: &mut Vec<(HirExpr, super::common::LocalId)>,
) {
    match expr {
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_) => {
            let local = if let Some((_, local)) = operands.iter().find(|(value, _)| value == expr) {
                *local
            } else {
                let local = super::common::LocalId(*next_local);
                *next_local += 1;
                operands.push((expr.clone(), local));
                local
            };
            *expr = HirExpr::LocalRef(local);
        }
        HirExpr::Unary(unary) => materialize_constant_leaf(&mut unary.expr, next_local, operands),
        HirExpr::Binary(binary) => materialize_constant_leaf(&mut binary.lhs, next_local, operands),
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            materialize_constant_leaf(&mut logical.lhs, next_local, operands)
        }
        _ => unreachable!("constant syntax contains a literal leaf"),
    }
}

pub(in crate::hir) fn inline_changes_table_initialization(
    stmt: &HirStmt,
    temp: TempId,
    replacement: &HirExpr,
) -> bool {
    if table_constant_kind(replacement).is_none() {
        return false;
    }
    struct Probe<'a> {
        temp: TempId,
        replacement: &'a HirExpr,
        changed: bool,
    }
    impl HirVisitor<'_> for Probe<'_> {
        fn visit_expr(&mut self, expr: &HirExpr) {
            let HirExpr::TableConstructor(table) = expr else {
                return;
            };
            if self.changed {
                return;
            }
            let Some(constraint) = table.allocation.initialization_constraint() else {
                return;
            };
            let mut next_array = 0;
            for field in &table.fields {
                let mut candidate_array = next_array;
                if runtime_table_operand(constraint, field_ref(field, &mut next_array)).is_some() {
                    continue;
                }
                let mut candidate = field.clone();
                let changes = match &mut candidate {
                    HirTableField::Array(value) => {
                        replace_temp_in_expr(value, self.temp, self.replacement)
                    }
                    HirTableField::Record(record) => {
                        replace_temp_in_expr(&mut record.key, self.temp, self.replacement)
                            + replace_temp_in_expr(&mut record.value, self.temp, self.replacement)
                    }
                };
                self.changed |= changes != 0
                    && runtime_table_operand(
                        constraint,
                        field_ref(&candidate, &mut candidate_array),
                    )
                    .is_some();
            }
        }
    }
    let mut probe = Probe {
        temp,
        replacement,
        changed: false,
    };
    visit_stmts(std::slice::from_ref(stmt), &mut probe);
    probe.changed
}

impl crate::value_semantics::table::TableExpression for HirExpr {
    fn table_key(&self) -> Option<crate::value_semantics::table::TableTemplateKey> {
        use crate::value_semantics::table::TableTemplateKey as Key;
        match self {
            Self::Boolean(value) => Some(Key::Boolean(*value)),
            Self::Integer(value) => Some(Key::number(*value as f64)),
            Self::Number(value) => Some(Key::number(*value)),
            Self::String(value) => Some(Key::String(value.clone())),
            _ => None,
        }
    }

    fn table_integer_key(&self) -> Option<i64> {
        match self {
            Self::Integer(value) => Some(*value),
            Self::Number(value) => crate::value_semantics::table::integer_table_key(*value),
            _ => None,
        }
    }

    fn table_constant_expr(&self) -> crate::value_semantics::table::TableConstantExpr<'_, Self> {
        use crate::value_semantics::table::{TableConstant as Kind, TableConstantExpr as Expr};
        match self {
            Self::Nil => Expr::Literal(Kind::Nil),
            Self::Boolean(value) => Expr::Literal(Kind::Boolean(*value)),
            Self::Integer(_) | Self::Number(_) => Expr::Literal(Kind::Number),
            Self::String(_) => Expr::Literal(Kind::String),
            Self::Unary(unary) => match unary.op {
                HirUnaryOpKind::Neg => Expr::Neg(&unary.expr),
                HirUnaryOpKind::Not => Expr::Not(&unary.expr),
                _ => Expr::Dynamic,
            },
            Self::Binary(binary)
                if matches!(
                    binary.op,
                    HirBinaryOpKind::Add
                        | HirBinaryOpKind::Sub
                        | HirBinaryOpKind::Mul
                        | HirBinaryOpKind::Div
                        | HirBinaryOpKind::Mod
                        | HirBinaryOpKind::Pow
                ) =>
            {
                Expr::Numeric(&binary.lhs, &binary.rhs)
            }
            Self::LogicalAnd(logical) => Expr::And(&logical.lhs, &logical.rhs),
            Self::Binary(binary)
                if matches!(
                    binary.op,
                    HirBinaryOpKind::Eq
                        | HirBinaryOpKind::Lt
                        | HirBinaryOpKind::Le
                        | HirBinaryOpKind::Gt
                        | HirBinaryOpKind::Ge
                ) =>
            {
                Expr::Comparison(&binary.lhs, &binary.rhs)
            }
            Self::LogicalOr(logical) => Expr::Or(&logical.lhs, &logical.rhs),
            _ => Expr::Dynamic,
        }
    }
}
