//! 这个 integration test 入口聚合所有 unit 风格测试。
//!
//! 这里按 `tests/unit/<dialect>/...` 组织，是为了让“层内契约测试”和
//! “主流程回归测试”分开演进，同时继续兼容 Cargo 对 tests 根目录的发现规则。

#[path = "support/mod.rs"]
mod support;

#[path = "unit/lua51/mod.rs"]
mod lua51;
