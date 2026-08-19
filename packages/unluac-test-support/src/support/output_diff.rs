//! 比较 Lua 命令输出并按测试 tag 聚合差异；依赖命令结果，不负责启动进程；例如报告某个 proto tag 的期望/实际行。

use super::*;

pub(crate) fn diff_command_outputs(
    expected_label: &str,
    expected: &LuaCommandOutput,
    actual_label: &str,
    actual: &LuaCommandOutput,
) -> Option<String> {
    let mut diffs = Vec::new();

    if expected.status_code != actual.status_code {
        diffs.push(format!(
            "status mismatch:\n  {expected_label}: {}\n  {actual_label}: {}",
            render_status_code(expected.status_code),
            render_status_code(actual.status_code)
        ));
    }

    if expected.stdout != actual.stdout {
        diffs.push(format!(
            "stdout mismatch:\n  {expected_label}:\n{}\n  {actual_label}:\n{}",
            render_bytes(&expected.stdout),
            render_bytes(&actual.stdout)
        ));
    }

    if expected.stderr != actual.stderr {
        diffs.push(format!(
            "stderr mismatch:\n  {expected_label}:\n{}\n  {actual_label}:\n{}",
            render_bytes(&expected.stderr),
            render_bytes(&actual.stderr)
        ));
    }

    (!diffs.is_empty()).then(|| diffs.join("\n"))
}

/// 从 stdout 行中提取 `file#N` 风格标签（每行第一个 tab 之前的字段，需包含 `#`）。
pub(super) fn extract_line_tag(line: &str) -> Option<&str> {
    let field = line.split('\t').next()?;
    if field.contains('#') {
        Some(field)
    } else {
        None
    }
}

/// 统计 stdout 中出现过的不重复 tag 数量，即文件内的 proto 数量。
pub(super) fn count_output_tags(stdout: &[u8]) -> usize {
    let text = String::from_utf8_lossy(stdout);
    let mut seen = std::collections::BTreeSet::new();
    for line in text.lines() {
        if let Some(tag) = extract_line_tag(line) {
            seen.insert(tag.to_owned());
        }
    }
    seen.len()
}

/// 按 tag 对比两份 stdout，返回不一致的 tag 列表。
pub(super) fn diff_output_tags(expected_stdout: &[u8], actual_stdout: &[u8]) -> Vec<String> {
    use std::collections::BTreeMap;

    fn group_by_tag(stdout: &[u8]) -> BTreeMap<String, Vec<String>> {
        let text = String::from_utf8_lossy(stdout);
        let mut map: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for line in text.lines() {
            if let Some(tag) = extract_line_tag(line) {
                map.entry(tag.to_owned()).or_default().push(line.to_owned());
            }
        }
        map
    }

    let expected = group_by_tag(expected_stdout);
    let actual = group_by_tag(actual_stdout);
    let mut failed = Vec::new();

    // 在 expected 中出现但 actual 不同（或缺失）的 tag
    for (tag, expected_lines) in &expected {
        match actual.get(tag) {
            Some(actual_lines) if actual_lines == expected_lines => {}
            _ => failed.push(tag.clone()),
        }
    }
    // 在 actual 中出现但 expected 没有的 tag（不应发生，但防御性记录）
    for tag in actual.keys() {
        if !expected.contains_key(tag) && !failed.contains(tag) {
            failed.push(tag.clone());
        }
    }
    failed
}
