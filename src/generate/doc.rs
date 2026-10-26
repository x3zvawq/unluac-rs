//! 轻量 Doc 模型。
//!
//! Generate 不直接在 visitor 里拼字符串，是为了把“语义输出”和“换行布局”拆开。
//! 这个 Doc 足够小，只覆盖当前项目实际需要的布局原语。
//! 固定关键字和标点借用静态文本，动态格式化结果移交所有权，避免逐 token 分配。

use std::borrow::Cow;

/// Generate 内部使用的轻量文档树。
///
/// `Cascade` 是表格布局的三段式级联：Flat 模式渲染 `flat`；Break 模式先复测
/// `flat` 是否仍在当前列放得下，再尝试把内容平铺进缩进一层后的下一行
/// （`content_width` 预先量好，`None` 表示内容含硬换行、永远放不下），
/// 最后才渲染 `broken`。`Grid` 只应出现在 `broken` 侧，渲染成按列对齐的表格行。
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Doc {
    Text(Cow<'static, str>),
    Line,
    SoftLine,
    Concat(Vec<Doc>),
    Fill { docs: Vec<Doc>, separator: Box<Doc> },
    Indent(Box<Doc>),
    Group(Box<Doc>),
    Cascade {
        flat: Box<Doc>,
        content: Box<Doc>,
        content_width: Option<usize>,
        broken: Box<Doc>,
    },
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

    /// 表格级联：Flat 模式渲染 `flat`；Break 模式先复测 `flat`，再尝试
    /// `content`（内容平铺在下一行），最后渲染 `broken`。`content_width`
    /// 是内容侧的平铺宽度，供 renderer 做行宽预算判断。
    pub fn cascade(flat: Doc, content: Doc, content_width: Option<usize>, broken: Doc) -> Self {
        Self::Cascade {
            flat: Box::new(flat),
            content: Box::new(content),
            content_width,
            broken: Box::new(broken),
        }
    }

    /// 文档平铺在单行时的精确宽度；含硬换行（`Line`/`Grid`）时返回 `None`。
    /// 与 renderer 的预算探测不同，这里不短路，给出的是完整宽度。
    pub(crate) fn flat_width(&self) -> Option<usize> {
        match self {
            Self::Text(text) => Some(text.chars().count()),
            Self::Line => None,
            Self::SoftLine => Some(1),
            Self::Concat(parts) => parts
                .iter()
                .try_fold(0usize, |total, part| {
                    part.flat_width().map(|width| total + width)
                }),
            Self::Fill { docs, separator } => docs
                .iter()
                .enumerate()
                .try_fold::<_, _, Option<usize>>(0usize, |total, (index, doc)| {
                    let total = if index == 0 {
                        Some(total)
                    } else {
                        separator.flat_width().map(|width| total + width)
                    }?;
                    doc.flat_width().map(|width| total + width)
                }),
            Self::Indent(inner) | Self::Group(inner) => inner.flat_width(),
            Self::Cascade { flat, .. } => flat.flat_width(),
            Self::Grid { .. } => None,
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
