//! 提供 AST 一元/二元操作符文本和括号清理；依赖 AST common 枚举，不负责表达式递归；例如把 LogicalAnd 映射为 and。

pub(super) fn format_unary_op(op: super::super::common::AstUnaryOpKind) -> &'static str {
    match op {
        super::super::common::AstUnaryOpKind::Not => "not",
        super::super::common::AstUnaryOpKind::Neg => "-",
        super::super::common::AstUnaryOpKind::BitNot => "~",
        super::super::common::AstUnaryOpKind::Length => "#",
    }
}

pub(super) fn format_binary_op(op: super::super::common::AstBinaryOpKind) -> &'static str {
    match op {
        super::super::common::AstBinaryOpKind::Add => "+",
        super::super::common::AstBinaryOpKind::Sub => "-",
        super::super::common::AstBinaryOpKind::Mul => "*",
        super::super::common::AstBinaryOpKind::Div => "/",
        super::super::common::AstBinaryOpKind::FloorDiv => "//",
        super::super::common::AstBinaryOpKind::Mod => "%",
        super::super::common::AstBinaryOpKind::Pow => "^",
        super::super::common::AstBinaryOpKind::BitAnd => "&",
        super::super::common::AstBinaryOpKind::BitOr => "|",
        super::super::common::AstBinaryOpKind::BitXor => "~",
        super::super::common::AstBinaryOpKind::Shl => "<<",
        super::super::common::AstBinaryOpKind::Shr => ">>",
        super::super::common::AstBinaryOpKind::Concat => "..",
        super::super::common::AstBinaryOpKind::Eq => "==",
        super::super::common::AstBinaryOpKind::Lt => "<",
        super::super::common::AstBinaryOpKind::Le => "<=",
    }
}

pub(super) fn strip_outer_parens(rendered: String) -> String {
    if !rendered.starts_with('(') || !rendered.ends_with(')') {
        return rendered;
    }

    let mut depth = 0usize;
    for (index, ch) in rendered.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth = depth.saturating_sub(1);
                if depth == 0 && index + ch.len_utf8() != rendered.len() {
                    return rendered;
                }
            }
            _ => {}
        }
    }

    rendered[1..(rendered.len() - 1)].to_owned()
}
