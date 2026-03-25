//! 这个模块归档 Lua 5.4 的 regression 测试。
//!
//! 这里先锁主 pipeline 已经能以 `lua5.4` dialect 跑到 transform/HIR；但暂时不把
//! 它纳入 clean-HIR 总回归，因为 5.4 的整体 HIR 覆盖面还在继续扩；不过 `<close>/TBC`
//! 这类关键语义已经单独用 regression 锁住，避免再退回 `unstructured`。

mod pipeline;
