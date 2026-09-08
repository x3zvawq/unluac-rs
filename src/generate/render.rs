//! Doc -> String 渲染器。
//!
//! 这里的实现刻意保持轻量：只做稳定换行和缩进，不引入复杂回溯。
//! 当前项目的布局需求主要集中在列表、表构造器和函数体块级结构，这套 renderer
//! 足以支撑第一版 Generate。

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
        }
    }

    fn fits_flat(&self, doc: &Doc) -> bool {
        self.options
            .max_line_length
            .checked_sub(self.column)
            .and_then(|remaining| remaining_after_flat(doc, remaining))
            .is_some()
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
    }
}
