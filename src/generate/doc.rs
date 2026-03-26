//! 轻量 Doc 模型。
//!
//! Generate 不直接在 visitor 里拼字符串，是为了把“语义输出”和“换行布局”拆开。
//! 这个 Doc 足够小，只覆盖当前项目实际需要的布局原语。

/// Generate 内部使用的轻量文档树。
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Doc {
    Text(String),
    Line,
    SoftLine,
    Concat(Vec<Doc>),
    Indent(Box<Doc>),
    Group(Box<Doc>),
}

impl Doc {
    pub fn text<T>(text: T) -> Self
    where
        T: Into<String>,
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
