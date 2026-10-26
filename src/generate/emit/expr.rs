//! 将最终 AST 表达式序列化为目标 Lua 的 Doc 片段。
//!
//! 消费 Naming、优先级规则与显式宿主配置，保留括号、值宽度和求值结构。

use crate::ast::pretty::preferred_negated_relational_render;
use crate::ast::{
    AstCallExpr, AstCallKind, AstExpr, AstFieldAccess, AstFunctionExpr, AstFunctionName,
    AstIndexAccess, AstLValue, AstLogicalExpr, AstMethodCallExpr, AstNamePath, AstNameRef,
    AstRecordField, AstTableConstructor, AstTableField, AstTableKey, AstUnaryOpKind,
};
use crate::decompile::DecompileDialect;
use crate::generate::LuauVectorSize;
use crate::generate::doc::Doc;
use crate::hir::HirProtoRef;

use super::super::common::TableStyle;
use crate::value_semantics::table::TableExpression;
use super::super::error::GenerateError;
use super::syntax::{
    binary_meta, format_complex_literal, format_integer, format_number, format_string_literal,
    format_unsigned_integer, format_vector_component, maybe_parenthesize, needs_parentheses,
};
use super::{
    Assoc, Emitter, ExprSide, PREC_AND, PREC_COMPARE, PREC_LITERAL, PREC_OR, PREC_PREFIX,
    PREC_UNARY,
};

fn numeric_literal(rendered: String) -> (Doc, u8, Assoc) {
    let precedence = if rendered.starts_with('-') {
        PREC_UNARY
    } else {
        PREC_LITERAL
    };
    (Doc::text(rendered), precedence, Assoc::Non)
}

#[derive(Clone, Copy)]
enum LogicalOperator {
    And,
    Or,
}

/// 对齐网格单元格的类别；一张表要进入网格布局，所有单元格必须同类。
/// 数字不区分整型/浮点，其余小字面量各自成类；任何其他表达式都没有资格。
#[derive(Clone, Copy, PartialEq, Eq)]
enum AlignedCellKind {
    Nil,
    Boolean,
    Number,
    String,
    Name,
}

impl AlignedCellKind {
    fn of(expr: &AstExpr) -> Option<Self> {
        match expr {
            AstExpr::Nil => Some(Self::Nil),
            AstExpr::Boolean(_) => Some(Self::Boolean),
            AstExpr::Integer(_) | AstExpr::Number(_) => Some(Self::Number),
            AstExpr::String(_) => Some(Self::String),
            AstExpr::Var(_) => Some(Self::Name),
            _ => None,
        }
    }
}

/// Flushes an alignment run: every field gets padding up to the widest key of
/// the run, after which the run is cleared.
fn flush_alignment_run(pads: &mut [usize], run: &mut Vec<(usize, usize)>, run_max: usize) {
    for &(index, width) in run.iter() {
        pads[index] = run_max - width;
    }
    run.clear();
}

/// `--table-drop-index-keys`：把显式写出的连续索引键 `[1]..[n]` 投影成位置字段。
/// 返回 `None` 表示该构造器没有可安全去掉的键（或键序列不连续/乱序/与位置字段混用），
/// 调用方应保留原字段。非整数键的记录字段原样保留，字段顺序不变，因此求值顺序
/// 与逐字段副作用完全一致；唯一的运行时差异是 `pairs` 顺序（哈希部分变成数组部分），
/// 这在 Lua 中本就不确定。
fn project_dropped_index_keys(fields: &[AstTableField]) -> Option<Vec<AstTableField>> {
    let mut projected = Vec::with_capacity(fields.len());
    let mut next_index = 1i64;
    let mut converted = 0usize;
    for field in fields {
        match field {
            // 位置字段与显式键混用时无法安全重排，直接放弃投影。
            AstTableField::Array(_) => return None,
            AstTableField::Record(record) => {
                let integer_key = match &record.key {
                    AstTableKey::Name(_) => None,
                    AstTableKey::Expr(expr) => expr.table_integer_key(),
                };
                match integer_key {
                    Some(index) if index == next_index => {
                        projected.push(AstTableField::Array(record.value.clone()));
                        next_index += 1;
                        converted += 1;
                    }
                    // 缺口、重复或乱序的索引键（如 `[1]` 后跟 `[3]`）语义上不是
                    // 纯数组，保留原样最稳妥。
                    Some(_) => return None,
                    None => projected.push(field.clone()),
                }
            }
        }
    }
    (converted > 0).then_some(projected)
}

impl LogicalOperator {
    const fn precedence(self) -> u8 {
        match self {
            Self::And => PREC_AND,
            Self::Or => PREC_OR,
        }
    }

    const fn text(self) -> &'static str {
        match self {
            Self::And => "and",
            Self::Or => "or",
        }
    }
}

impl<'a> Emitter<'a> {
    pub(super) fn emit_call_kind(
        &self,
        call: &AstCallKind,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        match call {
            AstCallKind::Call(call) => self.emit_call_expr(call, function),
            AstCallKind::MethodCall(call) => self.emit_method_call_expr(call, function),
        }
    }

    fn emit_call_expr(
        &self,
        call: &AstCallExpr,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        let callee = self.emit_expr(&call.callee, function, PREC_PREFIX, ExprSide::Left)?;
        let args = call
            .args
            .iter()
            .map(|arg| self.emit_expr(arg, function, 0, ExprSide::Standalone))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Doc::concat([callee, self.emit_parenthesized_list(args)]))
    }

    fn emit_method_call_expr(
        &self,
        call: &AstMethodCallExpr,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        if let Some(segments) = &call.interpolation {
            if self.target.version != DecompileDialect::Luau {
                return Err(GenerateError::UnsupportedFeature {
                    dialect: self.target.version,
                    feature: "string interpolation",
                });
            }
            if segments.len() != call.args.len() + 1 {
                return Err(GenerateError::UnprovenLuauInterpolation);
            }
            let mut parts = vec![Doc::text("`")];
            for (index, segment) in segments.iter().enumerate() {
                parts.push(Doc::text(super::syntax::format_interpolation_fragment(
                    segment,
                    self.options.readable_strings,
                )));
                if let Some(arg) = call.args.get(index) {
                    parts.push(Doc::text("{"));
                    if matches!(arg, AstExpr::TableConstructor(_)) {
                        // 相邻 {{ 被 Luau lexer 视为损坏的插值分隔符。
                        parts.push(Doc::text(" "));
                    }
                    parts.push(self.emit_expr(arg, function, 0, ExprSide::Standalone)?);
                    parts.push(Doc::text("}"));
                }
            }
            parts.push(Doc::text("`"));
            return Ok(Doc::concat(parts));
        }
        let receiver = self.emit_expr(&call.receiver, function, PREC_PREFIX, ExprSide::Left)?;
        let args = call
            .args
            .iter()
            .map(|arg| self.emit_expr(arg, function, 0, ExprSide::Standalone))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Doc::concat([
            receiver,
            Doc::text(format!(":{}", call.method)),
            self.emit_parenthesized_list(args),
        ]))
    }

    pub(super) fn emit_lvalue(
        &self,
        lvalue: &AstLValue,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        match lvalue {
            AstLValue::Name(name) => self.emit_name_ref(name, function),
            AstLValue::FieldAccess(access) => self.emit_field_access(access, function),
            AstLValue::IndexAccess(access) => self.emit_index_access(access, function),
        }
    }

    pub(super) fn emit_expr(
        &self,
        expr: &AstExpr,
        function: HirProtoRef,
        parent_prec: u8,
        side: ExprSide,
    ) -> Result<Doc, GenerateError> {
        let (doc, prec, assoc) = match expr {
            AstExpr::Nil => (Doc::text("nil"), PREC_LITERAL, Assoc::Non),
            AstExpr::Boolean(value) => (
                Doc::text(if *value { "true" } else { "false" }),
                PREC_LITERAL,
                Assoc::Non,
            ),
            AstExpr::Integer(value) => {
                numeric_literal(format_integer(*value, self.options.number_format))
            }
            AstExpr::CaptureInitializer(value) => {
                if self.target.version != crate::decompile::DecompileDialect::Luau {
                    return Err(GenerateError::UnsupportedFeature {
                        dialect: self.target.version,
                        feature: "Luau capture initializer",
                    });
                }
                // HIR 已证明 r0/r1 的初始化事务；不能先降成普通表达式树再折叠。
                if let crate::hir::HirCaptureInitializer::NegatedNumericString(number) = value {
                    let opposite = format_number(-number.to_f64(), false, false);
                    return Ok(Doc::text(format!("(-\"{opposite}\")")));
                }
                let literal = format_number(value.number().to_f64(), false, false);
                (
                    Doc::text(format!("((...) and ({literal}) or ({literal}))")),
                    PREC_LITERAL,
                    Assoc::Non,
                )
            }
            AstExpr::Number(value) => numeric_literal(format_number(
                *value,
                target_preserves_float_type(self.target.version),
                self.number_is_f32,
            )),
            AstExpr::String(value) => (
                Doc::text(format_string_literal(
                    value,
                    self.options.quote_style,
                    self.options.readable_strings,
                )),
                PREC_LITERAL,
                Assoc::Non,
            ),
            AstExpr::Int64(value) => numeric_literal(format!(
                "{}LL",
                format_integer(*value, self.options.number_format)
            )),
            AstExpr::UInt64(value) => numeric_literal(format!(
                "{}ULL",
                format_unsigned_integer(*value, self.options.number_format)
            )),
            AstExpr::Complex { real, imag } => {
                numeric_literal(format_complex_literal(*real, *imag)?)
            }
            AstExpr::Vector(vector) => {
                (self.emit_vector_literal(*vector)?, PREC_PREFIX, Assoc::Left)
            }
            AstExpr::Var(name) => (
                self.emit_name_ref(name, function)?,
                PREC_PREFIX,
                Assoc::Left,
            ),
            AstExpr::FieldAccess(access) => (
                self.emit_field_access(access, function)?,
                PREC_PREFIX,
                Assoc::Left,
            ),
            AstExpr::IndexAccess(access) => (
                self.emit_index_access(access, function)?,
                PREC_PREFIX,
                Assoc::Left,
            ),
            AstExpr::Unary(_) | AstExpr::Binary(_) => {
                return self.emit_operator_expr(expr, function, parent_prec, side);
            }
            AstExpr::LogicalAnd(logical) => {
                let doc = self.emit_logical_chain(logical, function, LogicalOperator::And)?;
                (doc, PREC_AND, Assoc::Full)
            }
            AstExpr::LogicalOr(logical) => {
                let doc = self.emit_logical_chain(logical, function, LogicalOperator::Or)?;
                (doc, PREC_OR, Assoc::Full)
            }
            AstExpr::Call(call) => (
                self.emit_call_expr(call, function)?,
                PREC_PREFIX,
                Assoc::Left,
            ),
            AstExpr::IfExpr(branch) => {
                if self.target.version != DecompileDialect::Luau {
                    return Err(GenerateError::UnsupportedFeature {
                        dialect: self.target.version,
                        feature: "Luau if expression",
                    });
                }
                (
                    Doc::concat([
                        Doc::text("(if "),
                        self.emit_expr(&branch.cond, function, 0, ExprSide::Standalone)?,
                        Doc::text(" then "),
                        self.emit_expr(&branch.then_expr, function, 0, ExprSide::Standalone)?,
                        Doc::text(" else "),
                        self.emit_expr(&branch.else_expr, function, 0, ExprSide::Standalone)?,
                        Doc::text(")"),
                    ]),
                    PREC_LITERAL,
                    Assoc::Non,
                )
            }
            AstExpr::MethodCall(call) => (
                self.emit_method_call_expr(call, function)?,
                if call.interpolation.is_some() {
                    PREC_LITERAL
                } else {
                    PREC_PREFIX
                },
                Assoc::Left,
            ),
            AstExpr::SingleValue(expr) => (
                Doc::concat([
                    Doc::text("("),
                    self.emit_expr(expr, function, 0, ExprSide::Standalone)?,
                    Doc::text(")"),
                ]),
                PREC_LITERAL,
                Assoc::Non,
            ),
            AstExpr::VarArg => (Doc::text("..."), PREC_LITERAL, Assoc::Non),
            AstExpr::TableConstructor(table) => (
                self.emit_table_constructor(table, function)?,
                PREC_LITERAL,
                Assoc::Non,
            ),
            AstExpr::FunctionExpr(func) => {
                (self.emit_function_expr(func)?, PREC_LITERAL, Assoc::Non)
            }
            AstExpr::Error(message) => (
                Doc::text(format!("nil --[[ [unluac error] {message} ]]")),
                PREC_LITERAL,
                Assoc::Non,
            ),
        };
        Ok(maybe_parenthesize(doc, prec, parent_prec, side, assoc))
    }

    /// 只展平 Doc 拼接，不改变运算树；括号仍逐节点消费原 precedence/side/assoc。
    /// 一条深算术链在这里和后续 renderer 中都不需要与链长成比例的调用栈。
    fn emit_operator_expr(
        &self,
        expr: &AstExpr,
        function: HirProtoRef,
        parent_prec: u8,
        side: ExprSide,
    ) -> Result<Doc, GenerateError> {
        enum Step<'ast> {
            Expr(&'ast AstExpr, u8, ExprSide),
            Text(&'static str),
            BinaryOperator(&'static str),
        }

        let mut pending = vec![Step::Expr(expr, parent_prec, side)];
        let mut parts = Vec::new();
        let mut segments = Vec::new();
        while let Some(step) = pending.pop() {
            let (expr, parent_prec, side) = match step {
                Step::Expr(expr, parent_prec, side) => (expr, parent_prec, side),
                Step::Text(text) => {
                    parts.push(Doc::text(text));
                    continue;
                }
                Step::BinaryOperator(op) => {
                    segments.push(Doc::concat(std::mem::take(&mut parts)));
                    parts.push(Doc::text(op));
                    parts.push(Doc::text(" "));
                    continue;
                }
            };
            let ((prec, assoc, op), lhs, rhs) = match expr {
                AstExpr::Binary(binary) => {
                    (binary_meta(binary.op), Some(&binary.lhs), Some(&binary.rhs))
                }
                AstExpr::Unary(unary) => {
                    if let Some(preferred) = preferred_negated_relational_render(unary) {
                        (
                            (PREC_COMPARE, Assoc::Non, preferred.op_text),
                            Some(preferred.lhs),
                            Some(preferred.rhs),
                        )
                    } else if unary.op == AstUnaryOpKind::Neg
                        && matches!(&unary.expr, AstExpr::Number(value) if *value == 0.0 && !value.is_sign_negative())
                    {
                        ((PREC_UNARY, Assoc::Right, "-0.0"), None, None)
                    } else {
                        let op = match unary.op {
                            AstUnaryOpKind::Not => "not ",
                            // 两个连续负号会被 Lua lexer 当作行注释。
                            AstUnaryOpKind::Neg if neg_operand_starts_with_minus(&unary.expr) => {
                                "- "
                            }
                            AstUnaryOpKind::Neg => "-",
                            AstUnaryOpKind::BitNot => "~",
                            AstUnaryOpKind::Length => "#",
                        };
                        ((PREC_UNARY, Assoc::Right, op), None, Some(&unary.expr))
                    }
                }
                _ => {
                    parts.push(self.emit_expr(expr, function, parent_prec, side)?);
                    continue;
                }
            };
            if needs_parentheses(prec, parent_prec, side, assoc) {
                parts.push(Doc::text("("));
                pending.push(Step::Text(")"));
            }
            if let Some(rhs) = rhs {
                pending.push(Step::Expr(rhs, prec, ExprSide::Right));
            }
            if let Some(lhs) = lhs {
                pending.push(Step::BinaryOperator(op));
                pending.push(Step::Expr(lhs, prec, ExprSide::Left));
            } else {
                parts.push(Doc::text(op));
            }
        }
        if segments.is_empty() {
            return Ok(Doc::concat(parts));
        }
        segments.push(Doc::concat(parts));
        Ok(Doc::group(Doc::indent(Doc::fill(
            segments,
            Doc::soft_line(),
        ))))
    }

    fn emit_logical_chain(
        &self,
        logical: &AstLogicalExpr,
        function: HirProtoRef,
        operator: LogicalOperator,
    ) -> Result<Doc, GenerateError> {
        let mut operands = Vec::new();
        collect_logical_operands(&logical.lhs, operator, &mut operands);
        collect_logical_operands(&logical.rhs, operator, &mut operands);

        let precedence = operator.precedence();
        let mut docs = operands.into_iter().enumerate().map(|(index, operand)| {
            let side = if index == 0 {
                ExprSide::Left
            } else {
                ExprSide::Right
            };
            self.emit_expr(operand, function, precedence, side)
        });
        let first = docs
            .next()
            .expect("a logical expression always has at least two operands")?;
        let continuations = docs
            .map(|doc| {
                doc.map(|doc| {
                    Doc::concat([
                        Doc::soft_line(),
                        Doc::text(operator.text()),
                        Doc::text(" "),
                        doc,
                    ])
                })
            })
            .collect::<Result<Vec<_>, _>>()?;

        Ok(Doc::group(Doc::concat([
            first,
            Doc::indent(Doc::concat(continuations)),
        ])))
    }

    fn emit_vector_literal(
        &self,
        vector: crate::parser::VectorLiteral,
    ) -> Result<Doc, GenerateError> {
        let constructor = self
            .options
            .luau_vector_constructor
            .as_ref()
            .ok_or(GenerateError::MissingLuauVectorConstructor)?;
        for name in constructor
            .library
            .iter()
            .chain(std::iter::once(&constructor.constructor))
        {
            if !DecompileDialect::Luau.is_identifier_name(name) {
                return Err(GenerateError::InvalidLuauVectorConstructor { name: name.clone() });
            }
        }

        let callee = constructor.library.as_ref().map_or_else(
            || constructor.constructor.clone(),
            |library| format!("{library}.{}", constructor.constructor),
        );
        let component_count = match constructor.size {
            LuauVectorSize::Three => 3,
            LuauVectorSize::Four => 4,
        };
        let args = vector.components[..component_count]
            .iter()
            .map(|bits| Doc::text(format_vector_component(*bits)))
            .collect();
        Ok(Doc::concat([
            Doc::text(callee),
            self.emit_parenthesized_list(args),
        ]))
    }

    pub(super) fn emit_name_ref(
        &self,
        name: &AstNameRef,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        Ok(Doc::text(self.names.resolve_name_ref(function, name)?))
    }

    fn emit_field_access(
        &self,
        access: &AstFieldAccess,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        let base = self.emit_expr(&access.base, function, PREC_PREFIX, ExprSide::Left)?;
        Ok(Doc::concat([base, Doc::text(format!(".{}", access.field))]))
    }

    fn emit_index_access(
        &self,
        access: &AstIndexAccess,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        let base = self.emit_expr(&access.base, function, PREC_PREFIX, ExprSide::Left)?;
        let index = self.emit_expr(&access.index, function, 0, ExprSide::Standalone)?;
        Ok(Doc::concat([base, Doc::text("["), index, Doc::text("]")]))
    }

    fn emit_table_constructor(
        &self,
        table: &AstTableConstructor,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        if table.fields.is_empty() {
            return Ok(Doc::text("{}"));
        }
        // `--table-drop-index-keys`：把连续的显式 `[1]..[n]` 键投影成位置字段。
        // 投影结果同时驱动网格资格判断，因此纯数字的显式键数组也能进入网格。
        let projected;
        let fields: &[AstTableField] = if self.options.table_drop_index_keys {
            projected = project_dropped_index_keys(&table.fields);
            projected.as_deref().unwrap_or(&table.fields)
        } else {
            &table.fields
        };
        let field_docs = fields
            .iter()
            .map(|field| self.emit_table_field(field, function))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(match self.options.table_style {
            TableStyle::Expanded => Doc::concat([
                Doc::text("{"),
                Doc::indent(Doc::concat([
                    Doc::line(),
                    Doc::join(field_docs, Doc::concat([Doc::text(","), Doc::line()])),
                ])),
                Doc::line(),
                Doc::text("}"),
            ]),
            TableStyle::Aligned => self.emit_aligned_table(fields, field_docs, function)?,
            TableStyle::Compact | TableStyle::Balanced => {
                let separator = Doc::concat([Doc::text(","), Doc::soft_line()]);
                Doc::group(Doc::concat([
                    Doc::text("{"),
                    Doc::indent(Doc::concat([
                        Doc::soft_line(),
                        Doc::fill(field_docs, separator),
                    ])),
                    Doc::soft_line(),
                    Doc::text("}"),
                ]))
            }
        })
    }

    /// Aligned 布局的级联决策：整体放得下就保持单行（复测按当前列判断）；
    /// 否则先尝试把内容平铺进下一行，再退回空格对齐网格（纯同类小字面量数组）
    /// 或逐行记录。网格行宽与字符串宽度上限由 `table_align_width` /
    /// `table_align_string_width` 控制。
    fn emit_aligned_table(
        &self,
        fields: &[AstTableField],
        field_docs: Vec<Doc>,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        let fields_flat = Doc::join(field_docs.iter().cloned(), Doc::text(", "));
        let content_width = fields_flat.flat_width();
        let flat = Doc::concat([Doc::text("{ "), fields_flat.clone(), Doc::text(" }")]);
        let broken = match self.aligned_grid_cells(fields, function) {
            Some(cells) => Doc::concat([
                Doc::text("{"),
                Doc::indent(Doc::concat([Doc::line(), Doc::grid(cells)])),
                Doc::line(),
                Doc::text("}"),
            ]),
            // 字典与非同类字段逐条输出；每条记录都带尾逗号，追加字段不会改写已有行。
            // 记录键按 `=` 对齐（`table_align_eq`），单行侧不参与对齐。
            None => {
                let pads = self.aligned_record_pads(fields, function);
                let needs_padding = pads.iter().any(|&pad| pad > 0);
                let lines = if needs_padding {
                    fields
                        .iter()
                        .zip(pads)
                        .map(|(field, pad)| self.emit_table_field_padded(field, pad, function))
                        .collect::<Result<Vec<_>, _>>()?
                } else {
                    field_docs
                };
                Doc::concat([
                    Doc::text("{"),
                    Doc::indent(Doc::concat([
                        Doc::line(),
                        Doc::join(
                            lines
                                .into_iter()
                                .map(|line| Doc::concat([line, Doc::text(",")])),
                            Doc::line(),
                        ),
                    ])),
                    Doc::line(),
                    Doc::text("}"),
                ])
            }
        };
        // 内容侧只带字段本身；花括号与换行由 renderer 在平铺进下一行时合成。
        Ok(Doc::cascade(flat, fields_flat, content_width, broken))
    }

    /// 收集对齐网格的单行单元格文本；返回 `None` 表示该表不具备网格布局资格：
    /// 出现记录字段、混入不同类别的小字面量、字符串超过宽度上限，或字段不是
    /// nil/布尔/数字/短字符串/普通名字之一。
    fn aligned_grid_cells(
        &self,
        fields: &[AstTableField],
        function: HirProtoRef,
    ) -> Option<Vec<String>> {
        let mut class = None;
        let mut cells = Vec::with_capacity(fields.len());
        for field in fields {
            let AstTableField::Array(expr) = field else {
                return None;
            };
            let kind = AlignedCellKind::of(expr)?;
            match class {
                Some(existing) if existing != kind => return None,
                _ => class = Some(kind),
            }
            let Doc::Text(text) = self
                .emit_expr(expr, function, 0, ExprSide::Standalone)
                .ok()?
            else {
                return None;
            };
            let text = text.into_owned();
            // 渲染结果含换行的字符串（长括号形式）会破坏单行网格，视作不合格。
            if text.contains('\n') || text.contains('\r') {
                return None;
            }
            if kind == AlignedCellKind::String
                && text.chars().count() > self.options.table_align_string_width
            {
                return None;
            }
            cells.push(text);
        }
        Some(cells)
    }

    fn emit_table_field(
        &self,
        field: &AstTableField,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        self.emit_table_field_padded(field, 0, function)
    }

    /// `pad` is the extra spaces inserted before ` = ` to align record keys;
    /// it is non-zero only in the per-line branch of the aligned style when
    /// `table_align_eq`.
    fn emit_table_field_padded(
        &self,
        field: &AstTableField,
        pad: usize,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        match field {
            AstTableField::Array(expr) => self.emit_expr(expr, function, 0, ExprSide::Standalone),
            AstTableField::Record(record) => self.emit_record_field(record, pad, function),
        }
    }

    fn emit_record_field(
        &self,
        record: &AstRecordField,
        pad: usize,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        let key = match &record.key {
            AstTableKey::Name(name) => Doc::text(name.clone()),
            AstTableKey::Expr(expr) => Doc::concat([
                Doc::text("["),
                self.emit_expr(expr, function, 0, ExprSide::Standalone)?,
                Doc::text("]"),
            ]),
        };
        let value = self.emit_expr(&record.value, function, 0, ExprSide::Standalone)?;
        if pad > 0 {
            Ok(Doc::concat([
                key,
                Doc::text(" ".repeat(pad)),
                Doc::text(" = "),
                value,
            ]))
        } else {
            Ok(Doc::concat([key, Doc::text(" = "), value]))
        }
    }

    /// Widths of record keys; `None` means the field cannot be aligned (an array
    /// field or an unmeasurable key, e.g. a key with a hard line break).
    fn record_key_width(
        &self,
        record: &AstRecordField,
        function: HirProtoRef,
    ) -> Option<usize> {
        match &record.key {
            AstTableKey::Name(name) => Some(name.chars().count()),
            AstTableKey::Expr(expr) => {
                let doc = self
                    .emit_expr(expr, function, 0, ExprSide::Standalone)
                    .ok()?;
                Some(doc.flat_width()? + 2)
            }
        }
    }

    /// Computes the padding before ` = ` for each field of the per-line branch:
    /// adjacent records are aligned to the widest key of the run while the total
    /// number of spaces between a key and `=` (padding plus the mandatory space)
    /// stays within `table_align_eq_max_spaces`. Arrays, unmeasurable keys and
    /// fields that exceed the threshold break the run.
    fn aligned_record_pads(&self, fields: &[AstTableField], function: HirProtoRef) -> Vec<usize> {
        let mut pads = vec![0; fields.len()];
        if !self.options.table_align_eq || self.options.table_align_eq_max_spaces == 0 {
            return pads;
        }
        let mut run: Vec<(usize, usize)> = Vec::new();
        let mut run_min = usize::MAX;
        let mut run_max = 0usize;
        for (index, field) in fields.iter().enumerate() {
            let width = match field {
                AstTableField::Record(record) => self.record_key_width(record, function),
                AstTableField::Array(_) => None,
            };
            let Some(width) = width else {
                flush_alignment_run(&mut pads, &mut run, run_max);
                run_min = usize::MAX;
                run_max = 0;
                continue;
            };
            let new_max = run_max.max(width);
            let new_min = run_min.min(width);
            if !run.is_empty()
                && new_max - new_min + 1 > self.options.table_align_eq_max_spaces
            {
                flush_alignment_run(&mut pads, &mut run, run_max);
                run_min = width;
                run_max = width;
            } else {
                run_min = new_min;
                run_max = new_max;
            }
            run.push((index, width));
        }
        flush_alignment_run(&mut pads, &mut run, run_max);
        pads
    }

    fn emit_function_expr(&self, func: &AstFunctionExpr) -> Result<Doc, GenerateError> {
        self.emit_function_with_header(func, Doc::text("function"))
    }

    pub(super) fn emit_function_name(
        &self,
        function_name: &AstFunctionName,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        match function_name {
            AstFunctionName::Plain(path) => self.emit_name_path(path, function),
            AstFunctionName::Method(path, method) => Ok(Doc::concat([
                self.emit_name_path(path, function)?,
                Doc::text(format!(":{method}")),
            ])),
        }
    }

    fn emit_name_path(
        &self,
        path: &AstNamePath,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        let mut parts = vec![self.emit_name_ref(&path.root, function)?];
        for field in &path.fields {
            parts.push(Doc::text(format!(".{field}")));
        }
        Ok(Doc::concat(parts))
    }

    pub(super) fn emit_function_with_header(
        &self,
        func: &AstFunctionExpr,
        header: Doc,
    ) -> Result<Doc, GenerateError> {
        let params = self.emit_decl_param_list(func, false)?;
        self.emit_function_with_header_and_params(func, header, params)
    }

    pub(super) fn emit_function_with_header_and_params(
        &self,
        func: &AstFunctionExpr,
        header: Doc,
        params: Doc,
    ) -> Result<Doc, GenerateError> {
        let body = self.emit_block(&func.body, func.function)?;
        let body = self.emit_indented_body(&func.body, body);
        let mut parts = vec![header, params];
        if let Some(comment) = self.emit_function_comment(func.function) {
            parts.extend([Doc::text(" "), comment]);
        }
        parts.push(body);
        parts.push(Doc::line());
        parts.push(Doc::text("end"));
        Ok(Doc::concat(parts))
    }

    pub(super) fn emit_decl_param_list(
        &self,
        func: &AstFunctionExpr,
        implicit_self: bool,
    ) -> Result<Doc, GenerateError> {
        let mut params = func
            .params
            .iter()
            .skip(usize::from(implicit_self))
            .map(|param| {
                self.names
                    .resolve_name_ref(func.function, &AstNameRef::Param(*param))
                    .map(Doc::text)
            })
            .collect::<Result<Vec<_>, _>>()?;
        if func.is_vararg {
            let vararg = if let Some(binding) = func.named_vararg {
                Doc::text(format!(
                    "...{}",
                    self.names.resolve_binding_ref(func.function, &binding)?
                ))
            } else {
                Doc::text("...")
            };
            params.push(vararg);
        }
        Ok(self.emit_parenthesized_list(params))
    }
}

/// Flattening here changes only Doc layout. Lua gives equal-precedence `and`/`or` chains full
/// associativity, so the emitted token order and short-circuit evaluation remain unchanged.
fn collect_logical_operands<'a>(
    expr: &'a AstExpr,
    operator: LogicalOperator,
    operands: &mut Vec<&'a AstExpr>,
) {
    let nested = match (operator, expr) {
        (LogicalOperator::And, AstExpr::LogicalAnd(logical))
        | (LogicalOperator::Or, AstExpr::LogicalOr(logical)) => Some(logical.as_ref()),
        _ => None,
    };
    if let Some(logical) = nested {
        collect_logical_operands(&logical.lhs, operator, operands);
        collect_logical_operands(&logical.rhs, operator, operands);
    } else {
        operands.push(expr);
    }
}

fn target_preserves_float_type(dialect: DecompileDialect) -> bool {
    matches!(
        dialect,
        DecompileDialect::Lua53 | DecompileDialect::Lua54 | DecompileDialect::Lua55
    )
}

fn neg_operand_starts_with_minus(expr: &AstExpr) -> bool {
    match expr {
        AstExpr::Integer(value) => value.is_negative(),
        AstExpr::Number(value) => value.is_sign_negative(),
        AstExpr::Int64(value) => value.is_negative(),
        AstExpr::Unary(unary) => unary.op == AstUnaryOpKind::Neg,
        _ => false,
    }
}
