//! 轻量 Doc 模型。
//!
//! Generate 不直接在 visitor 里拼字符串，是为了把“语义输出”和“换行布局”拆开。
//! 这个 Doc 足够小，只覆盖当前项目实际需要的布局原语。
//! 固定关键字和标点借用静态文本，动态格式化结果移交所有权，避免逐 token 分配。

use std::borrow::Cow;

/// Generate 内部使用的轻量文档树。
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Doc {
    Text(Cow<'static, str>),
    Line,
    SoftLine,
    Concat(Vec<Doc>),
    Fill { docs: Vec<Doc>, separator: Box<Doc> },
    Indent(Box<Doc>),
    Group(Box<Doc>),
    AlignedTable(Box<AlignedTable>),
}

/// 四种布局共享一份字段树；嵌套表的单行宽度自底向上缓存，不复制子树。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AlignedTable {
    pub fields: Vec<AlignedTableField>,
    pub content_width: Option<usize>,
    /// Some 仅用于已验证为单行 Text 的同类数组字段，bool 表示右对齐。
    pub grid_align: Option<bool>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AlignedTableField {
    pub key: Option<Doc>,
    pub value: Doc,
    pub key_width: Option<usize>,
    /// 仅逐字段布局在等号前使用，单行布局始终只用一个空格。
    pub padding: usize,
}

impl AlignedTableField {
    pub fn flat_width(&self) -> Option<usize> {
        let key = if self.key.is_some() {
            self.key_width? + 3
        } else {
            0
        };
        Some(key + self.value.flat_width()?)
    }
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

    /// 表字段的单行宽度；嵌套对齐表只读取缓存，硬换行没有单行宽度。
    pub(crate) fn flat_width(&self) -> Option<usize> {
        match self {
            Self::Text(text) if !text.contains(['\n', '\r']) => Some(text.chars().count()),
            Self::Text(_) | Self::Line => None,
            Self::SoftLine => Some(1),
            Self::Concat(parts) => parts
                .iter()
                .try_fold(0, |total, part| Some(total + part.flat_width()?)),
            Self::Fill { docs, separator } => {
                let separator_width = separator.flat_width()?;
                docs.iter().enumerate().try_fold(0, |total, (index, doc)| {
                    Some(total + if index == 0 { 0 } else { separator_width } + doc.flat_width()?)
                })
            }
            Self::Indent(inner) | Self::Group(inner) => inner.flat_width(),
            Self::AlignedTable(table) => table.content_width.map(|width| width + 4),
        }
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
