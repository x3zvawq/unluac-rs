//! 这个模块归档 LuaJIT 的 regression 测试。
//!
//! 当前先锁那些已经确认由 luajit 字节码/HIR 稳定支持的结构回归，避免 fallback
//! `goto` 循环再次退回机械的状态 temp 形状。

mod pipeline;
