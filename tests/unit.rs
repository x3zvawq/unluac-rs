//! 这个 integration test 入口聚合所有 unit 测试。
//!
//! unit 只负责 case-health 和 decompile-pipeline-health 两类健康检查，
//! 它们都是围绕 `(case, dialect)` 这个最小支持单元展开的。

#[path = "support/mod.rs"]
mod support;

#[path = "unit/case_health.rs"]
mod case_health;

#[path = "unit/decompile_pipeline_health.rs"]
mod decompile_pipeline_health;
