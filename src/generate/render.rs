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
pub fn render_doc(doc: &Doc, options: GenerateOptions) -> String {
    let mut renderer = Renderer {
        output: String::new(),
        column: 0,
        options,
    };
    renderer.render(doc, LayoutMode::Break, 0);
    if !renderer.output.ends_with('\n') {
        renderer.output.push('\n');
    }
    renderer.output
}

struct Renderer {
    output: String,
    column: usize,
    options: GenerateOptions,
}

impl Renderer {
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
            Doc::Indent(inner) => self.render(inner, mode, indent + self.options.indent_width),
            Doc::Group(inner) => {
                let child_mode = if self.fits_flat(inner) {
                    LayoutMode::Flat
                } else {
                    LayoutMode::Break
                };
                self.render(inner, child_mode, indent);
            }
        }
    }

    fn fits_flat(&self, doc: &Doc) -> bool {
        let Some(width) = flat_width(doc) else {
            return false;
        };
        self.column + width <= self.options.max_line_length
    }

    fn push_text(&mut self, text: &str) {
        self.output.push_str(text);
        self.column += text.chars().count();
    }

    fn push_line(&mut self, indent: usize) {
        self.output.push('\n');
        for _ in 0..indent {
            self.output.push(' ');
        }
        self.column = indent;
    }
}

fn flat_width(doc: &Doc) -> Option<usize> {
    match doc {
        Doc::Text(text) => Some(text.chars().count()),
        Doc::Line => None,
        Doc::SoftLine => Some(1),
        Doc::Concat(parts) => parts.iter().try_fold(0usize, |sum, part| {
            flat_width(part).map(|width| sum + width)
        }),
        Doc::Indent(inner) | Doc::Group(inner) => flat_width(inner),
    }
}
