//! readability 专用的 block 类别标签。
//!
//! 共享的结构递归宏已提升至 `crate::ast::traverse`；这里只保留 readability
//! 内部需要的 `BlockKind`，方便 pass 按 module/function/regular 分支做不同处理。

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum BlockKind {
    ModuleBody,
    FunctionBody,
    Regular,
}
