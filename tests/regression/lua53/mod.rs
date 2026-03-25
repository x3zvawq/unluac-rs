//! 这个模块归档 Lua 5.3 的 regression 测试。
//!
//! 当前先固定主 pipeline 已经能以 `lua5.3` dialect 真正跑通到 transform/HIR，
//! 避免后面继续推进 5.4 或 AST 时把入口链路重新弄断。

mod pipeline;
