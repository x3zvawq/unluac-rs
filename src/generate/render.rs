//! 将 Doc 布局渲染为最终源码字符串。
//!
//! 消费缩进和行宽选项，保持 emitter 已确定的语法结构。

use super::common::GenerateOptions;
use super::doc::Doc;

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
            Doc::Cascade {
                flat,
                content,
                content_width,
                broken,
            } => match mode {
                LayoutMode::Flat => self.render(flat, mode, indent),
                LayoutMode::Break => {
                    if self.fits_flat(flat) {
                        self.render(flat, LayoutMode::Flat, indent);
                    } else {
                        let content_indent = indent + self.options.indent_width;
                        let fits = self
                            .options
                            .max_line_length
                            .checked_sub(content_indent)
                            .is_some_and(|remaining| {
                                content_width.is_none_or(|width| width <= remaining)
                            });
                        if fits {
                            self.push_text("{");
                            self.push_line(content_indent);
                            self.render(content, LayoutMode::Flat, content_indent);
                            self.push_line(indent);
                            self.push_text("}");
                        } else {
                            self.render(broken, mode, indent);
                        }
                    }
                }
            },
            Doc::Grid { cells } => self.render_grid(cells, indent),
        }
    }

    fn fits_flat(&self, doc: &Doc) -> bool {
        self.options
            .max_line_length
            .checked_sub(self.column)
            .and_then(|remaining| remaining_after_flat(doc, remaining))
            .is_some()
    }

    /// 把单元格文本渲染成列对齐的表格：所有行共用统一的列宽（按最宽单元格计），
    /// 值按列起点垂直对齐。行预算是 `table_align_width` 减去行首缩进；行数取整列数，
    /// 并向均匀分布收敛，避免末行只剩一个孤立单元格。
    fn render_grid(&mut self, cells: &[String], indent: usize) {
        let Some(max_cell_width) = cells.iter().map(|cell| cell.chars().count()).max() else {
            return;
        };
        let max_cell_width = max_cell_width.max(1);
        let stride = max_cell_width + 2;
        let row_budget = self.options.table_align_width.saturating_sub(indent);
        // 整行宽度 k*(W+2)-1 ≤ budget（行尾逗号不加尾随填充）。
        let per_row_max = (row_budget.saturating_add(1) / stride).max(1);
        let count = cells.len();
        // 行数向上取整后再均分行内单元格，避免末行只剩一个孤立单元格。
        let full_rows = count.div_ceil(per_row_max).max(1);
        let per_row = count.div_ceil(full_rows).max(1);

        let mut cells = cells.iter();
        self.push_grid_row(&mut cells, per_row, max_cell_width);
        for _ in 1..full_rows {
            self.push_line(indent);
            self.push_grid_row(&mut cells, per_row, max_cell_width);
        }
    }

    /// 输出一行网格：单元格渲染为 `值,`，随后的填充空格让下一格落在下一列起点；
    /// 列对齐只相对本行首个单元格计算，与缩进无关。
    fn push_grid_row<'a, I>(&mut self, cells: &mut I, per_row: usize, max_cell_width: usize)
    where
        I: Iterator<Item = &'a String>,
    {
        let mut previous_width = 0usize;
        for (index, cell) in cells.by_ref().take(per_row).enumerate() {
            if index > 0 {
                let padding = max_cell_width + 1 - previous_width;
                self.push_text(&" ".repeat(padding));
            }
            previous_width = cell.chars().count();
            self.push_text(cell);
            self.push_text(",");
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
        self.options
            .max_line_length
            .checked_sub(self.column)
            .and_then(|remaining| remaining_after_flat(lhs, remaining))
            .and_then(|remaining| remaining_after_flat(rhs, remaining))
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

/// 只证明能否平铺；超出剩余字符预算后无需测量未访问的后缀。
fn remaining_after_flat(doc: &Doc, remaining: usize) -> Option<usize> {
    match doc {
        Doc::Text(text) => text
            .chars()
            .try_fold(remaining, |remaining, _| remaining.checked_sub(1)),
        Doc::Line => None,
        Doc::SoftLine => remaining.checked_sub(1),
        Doc::Concat(parts) => parts.iter().try_fold(remaining, |remaining, part| {
            remaining_after_flat(part, remaining)
        }),
        Doc::Fill { docs, separator } => {
            docs.iter()
                .enumerate()
                .try_fold(remaining, |remaining, (index, doc)| {
                    let remaining = if index == 0 {
                        remaining
                    } else {
                        remaining_after_flat(separator, remaining)?
                    };
                    remaining_after_flat(doc, remaining)
                })
        }
        Doc::Indent(inner) | Doc::Group(inner) => remaining_after_flat(inner, remaining),
        // Cascade 只按 flat 侧证明能否平铺；Grid 自带硬换行，不能作为单行内容。
        Doc::Cascade { flat, .. } => remaining_after_flat(flat, remaining),
        Doc::Grid { .. } => None,
    }
}
