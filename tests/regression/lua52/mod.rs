//! 这个模块归档 Lua 5.2 的 regression 测试。
//!
//! 这里优先固定 HIR 对 `goto/_ENV` 这些 5.2 特性暴露出的跨层契约，避免后续继续
//! 写 AST 时，底层又悄悄退回 fallback 或把 `goto` 误折成别的结构。

mod goto_shapes;
