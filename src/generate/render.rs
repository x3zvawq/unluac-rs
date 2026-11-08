//! 将 Doc 布局渲染为最终源码字符串。
//!
//! 消费缩进和行宽选项，保持 emitter 已确定的语法结构。

use super::common::GenerateOptions;
use super::doc::{AlignedTable, AlignedTableField, Doc};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LayoutMode {
    Flat,
    Break,
}

/// 把 Doc 渲染成最终源码字符串。
pub fn render_doc(doc: &Doc, options: &GenerateOptions) -> String {
    let mut renderer = Renderer {
        output: String::new(),
        line: 0,
        column: 0,
        options,
    };
    renderer.render(doc, LayoutMode::Break, 0);
    if !renderer.output.ends_with('\n') {
        renderer.output.push('\n');
    }
    renderer.output
}

struct Renderer<'a> {
    output: String,
    line: usize,
    column: usize,
    options: &'a GenerateOptions,
}

impl Renderer<'_> {
    fn render(&mut self, doc: &Doc, mode: LayoutMode, indent: usize) {
        match doc {
            Doc::Text(text) => self.push_text(text),
            Doc::Line => self.push_line(indent),
            Doc::SoftLine => match mode {
                LayoutMode::Flat => self.push_text(" "),
                LayoutMode::Break => self.push_line(indent),
            },
            Doc::Concat(parts) => {
                for part in parts {
                    self.render(part, mode, indent);
                }
            }
            Doc::Fill { docs, separator } => self.render_fill(docs, separator, mode, indent),
            Doc::Indent(inner) => self.render(inner, mode, indent + self.options.indent_width),
            Doc::Group(inner) => {
                let child_mode = if mode == LayoutMode::Flat || self.fits_flat(inner) {
                    LayoutMode::Flat
                } else {
                    LayoutMode::Break
                };
                self.render(inner, child_mode, indent);
            }
            Doc::AlignedTable(table) => self.render_aligned_table(table, indent),
        }
    }

    fn fits_flat(&self, doc: &Doc) -> bool {
        flat_end(
            doc,
            self.column,
            self.options.max_line_length,
            self.options.resolved_table_align_width(),
        )
        .is_some()
    }

    fn render_aligned_table(&mut self, table: &AlignedTable, indent: usize) {
        let budget = self.options.resolved_table_align_width();
        if table
            .content_width
            .is_some_and(|width| self.column + width + 4 <= budget)
        {
            self.push_text("{ ");
            self.render_table_content(&table.fields, indent);
            self.push_text(" }");
            return;
        }
        let content_indent = indent + self.options.indent_width;
        self.push_text("{");
        self.push_line(content_indent);
        if table
            .content_width
            .is_some_and(|width| content_indent + width <= budget)
        {
            self.render_table_content(&table.fields, content_indent);
        } else if let Some(align_right) = table.grid_align {
            self.render_grid(&table.fields, align_right, content_indent);
        } else {
            for (index, field) in table.fields.iter().enumerate() {
                if index > 0 {
                    self.push_line(content_indent);
                }
                self.render_table_field(field, LayoutMode::Break, content_indent);
                self.push_text(",");
            }
        }
        self.push_line(indent);
        self.push_text("}");
    }

    fn render_table_content(&mut self, fields: &[AlignedTableField], indent: usize) {
        for (index, field) in fields.iter().enumerate() {
            if index > 0 {
                self.push_text(", ");
            }
            self.render_table_field(field, LayoutMode::Flat, indent);
        }
    }

    fn render_table_field(&mut self, field: &AlignedTableField, mode: LayoutMode, indent: usize) {
        if let Some(key) = &field.key {
            self.render(key, mode, indent);
            if mode == LayoutMode::Break {
                self.push_text(&" ".repeat(field.padding));
            }
            self.push_text(" = ");
        }
        self.render(&field.value, mode, indent);
    }

    fn render_grid(&mut self, fields: &[AlignedTableField], align_right: bool, indent: usize) {
        let cells = fields
            .iter()
            .map(|field| {
                let Doc::Text(text) = &field.value else {
                    unreachable!("grid eligibility requires Text fields");
                };
                (text.as_ref(), text.chars().count())
            })
            .collect::<Vec<_>>();
        let max_cell_width = cells
            .iter()
            .map(|(_, width)| *width)
            .max()
            .expect("nonempty table")
            .max(1);
        let stride = max_cell_width + 2;
        let row_budget = self
            .options
            .resolved_table_align_width()
            .saturating_sub(indent);
        let per_row_max = (row_budget.saturating_add(1) / stride).max(1);
        let rows = cells.len().div_ceil(per_row_max);
        let per_row = cells.len().div_ceil(rows);
        for (row_index, row) in cells.chunks(per_row).enumerate() {
            if row_index > 0 {
                self.push_line(indent);
            }
            for (column, (text, width)) in row.iter().enumerate() {
                if column > 0 {
                    self.push_text(" ");
                }
                if align_right {
                    self.push_text(&" ".repeat(max_cell_width - width));
                }
                self.push_text(text);
                self.push_text(",");
                if !align_right && column + 1 < row.len() {
                    self.push_text(&" ".repeat(max_cell_width - width));
                }
            }
        }
    }

    fn render_fill(&mut self, docs: &[Doc], separator: &Doc, mode: LayoutMode, indent: usize) {
        let Some((first, rest)) = docs.split_first() else {
            return;
        };
        let first_mode = if mode == LayoutMode::Flat || self.fits_flat(first) {
            LayoutMode::Flat
        } else {
            LayoutMode::Break
        };
        let item_start_line = self.line;
        self.render(first, first_mode, indent);
        let mut previous_item_was_multiline = self.line > item_start_line;
        for doc in rest {
            let item_mode = if mode == LayoutMode::Flat {
                LayoutMode::Flat
            } else if previous_item_was_multiline {
                LayoutMode::Break
            } else if self.fits_flat_pair(separator, doc) {
                LayoutMode::Flat
            } else {
                LayoutMode::Break
            };
            self.render(separator, item_mode, indent);
            let item_start_line = self.line;
            self.render(doc, item_mode, indent);
            previous_item_was_multiline = self.line > item_start_line;
        }
    }

    fn fits_flat_pair(&self, lhs: &Doc, rhs: &Doc) -> bool {
        let limit = self.options.max_line_length;
        let table_limit = self.options.resolved_table_align_width();
        flat_end(lhs, self.column, limit, table_limit)
            .and_then(|column| flat_end(rhs, column, limit, table_limit))
            .is_some()
    }

    fn push_text(&mut self, text: &str) {
        self.output.push_str(text);
        self.column += text.chars().count();
    }

    fn push_line(&mut self, indent: usize) {
        while self.output.ends_with(' ') {
            self.output.pop();
        }
        self.output.push('\n');
        self.line += 1;
        for _ in 0..indent {
            self.output.push(' ');
        }
        self.column = indent;
    }
}

/// 预算内的单行结束列；对齐表消费缓存，父 Group 的 Flat 决策也必须满足表宽约束。
fn flat_end(doc: &Doc, column: usize, limit: usize, table_limit: usize) -> Option<usize> {
    let advance = |width: usize, limit: usize| {
        let end = column.checked_add(width)?;
        (end <= limit).then_some(end)
    };
    match doc {
        Doc::Text(text) => text
            .chars()
            .try_fold(column, |column, _| (column < limit).then_some(column + 1)),
        Doc::Line => None,
        Doc::SoftLine => advance(1, limit),
        Doc::Concat(parts) => parts.iter().try_fold(column, |column, part| {
            flat_end(part, column, limit, table_limit)
        }),
        Doc::Fill { docs, separator } => {
            docs.iter()
                .enumerate()
                .try_fold(column, |column, (index, doc)| {
                    let column = if index == 0 {
                        column
                    } else {
                        flat_end(separator, column, limit, table_limit)?
                    };
                    flat_end(doc, column, limit, table_limit)
                })
        }
        Doc::Indent(inner) | Doc::Group(inner) => flat_end(inner, column, limit, table_limit),
        Doc::AlignedTable(table) => advance(table.content_width? + 4, limit.min(table_limit)),
    }
}
