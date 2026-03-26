//! 这些测试固定 case-health。
//!
//! `case-health` 只回答一个问题：case 自己在对应 dialect 下是不是健康的。
//! 它要求源码直跑、源码编译后再跑的退出码和输出完全一致。

use crate::support::build_case_health_baseline;
use crate::support::case_manifest::{LuaCaseDialect, case_health_cases};

#[test]
fn lua51_cases_are_healthy() {
    assert_case_health_for_dialect(LuaCaseDialect::Lua51);
}

#[test]
fn lua52_cases_are_healthy() {
    assert_case_health_for_dialect(LuaCaseDialect::Lua52);
}

#[test]
fn lua53_cases_are_healthy() {
    assert_case_health_for_dialect(LuaCaseDialect::Lua53);
}

#[test]
fn lua54_cases_are_healthy() {
    assert_case_health_for_dialect(LuaCaseDialect::Lua54);
}

#[test]
fn lua55_cases_are_healthy() {
    assert_case_health_for_dialect(LuaCaseDialect::Lua55);
}

fn assert_case_health_for_dialect(dialect: LuaCaseDialect) {
    let mut failures = Vec::new();

    for entry in case_health_cases().filter(|entry| entry.dialect == dialect) {
        if let Err(error) = build_case_health_baseline(&entry, "case-health") {
            failures.push(format!("case: {}\n{}", entry.path, error));
        }
    }

    assert!(
        failures.is_empty(),
        "case-health failed for {}:\n\n{}",
        dialect.luac_label(),
        failures.join("\n\n")
    );
}
