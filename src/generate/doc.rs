//! 轻量 Doc 模型。
//!
//! Generate 不直接在 visitor 里拼字符串，是为了把“语义输出”和“换行布局”拆开。
//! 这个 Doc 足够小，只覆盖当前项目实际需要的布局原语。
//! 固定关键字和标点借用静态文本，动态格式化结果移交所有权，避免逐 token 分配。

use std::borrow::Cow;

/// Generate 内部使用的轻量文档树。
///
/// `Alt` 是 Wadler pretty printing 的 flat-alternative：同一位置的两份内容，
/// Flat 模式渲染 `flat`，Break 模式渲染 `broken`。`Grid` 只应出现在 `Alt` 的
/// broken 侧，渲染成按列对齐的表格行；行数与填充由 renderer 结合当前缩进计算，
/// emitter 只提供单行单元格文本。
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Doc {
    Text(Cow<'static, str>),
    Line,
    SoftLine,
    Concat(Vec<Doc>),
    Fill { docs: Vec<Doc>, separator: Box<Doc> },
    Indent(Box<Doc>),
    Group(Box<Doc>),
    Alt { flat: Box<Doc>, broken: Box<Doc> },
    Grid { cells: Vec<String> },
}

impl Doc {
    pub fn text<T>(text: T) -> Self
    where
        T: Into<Cow<'static, str>>,
    {
        Self::Text(text.into())
    }

    pub const fn line() -> Self {
        Self::Line
    }

    pub const fn soft_line() -> Self {
        Self::SoftLine
    }

    pub fn concat<I>(docs: I) -> Self
    where
        I: IntoIterator<Item = Doc>,
    {
        let docs = docs.into_iter().collect::<Vec<_>>();
        Self::Concat(docs)
    }

    pub fn indent(doc: Doc) -> Self {
        Self::Indent(Box::new(doc))
    }

    pub fn group(doc: Doc) -> Self {
        Self::Group(Box::new(doc))
    }

    pub fn fill<I>(docs: I, separator: Doc) -> Self
    where
        I: IntoIterator<Item = Doc>,
    {
        Self::Fill {
            docs: docs.into_iter().collect(),
            separator: Box::new(separator),
        }
    }

    /// 两份互斥布局：整体放得下时渲染 `flat`，否则渲染 `broken`。
    /// 宽度测量只看 `flat` 侧，`broken` 侧允许包含硬换行。
    pub fn alt(flat: Doc, broken: Doc) -> Self {
        Self::Alt {
            flat: Box::new(flat),
            broken: Box::new(broken),
        }
    }

    /// 单行单元格文本组成的对齐网格；行布局由 renderer 决定。
    pub fn grid(cells: Vec<String>) -> Self {
        Self::Grid { cells }
    }

    pub fn join<I>(docs: I, separator: Doc) -> Self
    where
        I: IntoIterator<Item = Doc>,
    {
        let mut docs = docs.into_iter();
        let Some(first) = docs.next() else {
            return Self::concat([]);
        };
        let mut parts = vec![first];
        for doc in docs {
            parts.push(separator.clone());
            parts.push(doc);
        }
        Self::concat(parts)
    }
}
