//! 这个 integration test 入口聚合所有 regression 风格测试。
//!
//! 回归测试强调的是对外契约和跨层组合行为，因此按 `regression/<dialect>/...`
//! 拆分后，新增 dialect 时不会把根目录继续堆成平铺文件列表。

#[path = "support/mod.rs"]
mod support;

#[path = "regression/lua51/mod.rs"]
mod lua51;

#[path = "regression/lua52/mod.rs"]
mod lua52;

#[path = "regression/lua53/mod.rs"]
mod lua53;
