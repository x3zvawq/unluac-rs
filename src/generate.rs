//! Generate 层入口。
//!
//! 这一层只负责把 Readability 之后的稳定 AST 和 NameMap 落成最终 Lua 源码文本。
//! 它不再回头修改 AST，也不重新决定命名；这里的核心是把“语法输出”和“文本布局”
//! 分开，所以内部采用 `AST -> Doc -> String` 的两步结构。

mod common;
mod debug;
mod doc;
mod emit;
mod error;
mod render;

pub use common::{GenerateOptions, GeneratedChunk, QuoteStyle, TableStyle};
pub use debug::dump_generate;
pub use emit::generate_chunk;
pub use error::GenerateError;
