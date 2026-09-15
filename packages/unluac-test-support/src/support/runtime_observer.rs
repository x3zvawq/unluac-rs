//! 在独立编译的观察器中执行原 chunk，保留被测模块的编译边界。
//!
//! `unluac-runtime:` 注释提供观察器源码，chunk 参数是待执行函数；编译器仍只看到
//! 原 case 的注释，不把 setfenv 等观察逻辑加入被测模块并改变其优化决策。
//! 普通执行之后追加一次观察执行，两份完整输出分别参与各轮比较。这里不参与反编译。

use std::fmt::Write;

use super::*;

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) struct RuntimeObserver {
    compiled: PathBuf,
    source_output: LuaCommandOutput,
}

impl RuntimeObserver {
    pub(super) fn prepare(
        entry: &LuaCaseManifestEntry,
        suite: &str,
    ) -> Result<Option<Self>, String> {
        let source = fs::read_to_string(repo_root().join(entry.path)).map_err(|error| {
            format!("read runtime observer from {} failed: {error}", entry.path)
        })?;
        let mut observer = String::new();
        for line in source.lines() {
            if let Some(code) = line
                .trim_start()
                .strip_prefix("--")
                .map(str::trim_start)
                .and_then(|comment| comment.strip_prefix("unluac-runtime:"))
            {
                observer.push_str(code.strip_prefix(' ').unwrap_or(code));
                observer.push('\n');
            }
        }
        if observer.is_empty() {
            return Ok(None);
        }
        if entry.dialect != LuaCaseDialect::Luau {
            return Err("unluac-runtime currently requires a Luau case".to_owned());
        }
        if entry.expectation != LuaCaseExpectation::Source {
            return Err("unluac-runtime requires the ordinary equivalence pipeline".to_owned());
        }
        let observer_path = suite_artifact_path(suite, entry, "runtime-observer", "lua");
        let compiled = suite_artifact_path(suite, entry, "runtime-observer", "luau");
        write_output_file(&observer_path, observer.as_bytes())?;
        let output =
            compile_lua_file_to_path("luau", &observer_path, &compiled, true, entry.options)?;
        if !output.success() {
            return Err(format!(
                "compile runtime observer failed:\n{}",
                output.render()
            ));
        }

        // 按字节引用，既不改变源码自身的 hotcomment，也不让长括号/转义提前结束字符串。
        let runner = format!(
            "local observe = assert(loadstring({}, '@runtime-observer'))\n\
             local run = assert(loadstring({}, '@observed-case'))\nobserve(run)\n",
            quote_bytes(observer.as_bytes()),
            quote_bytes(source.as_bytes()),
        );
        let source_runner = suite_artifact_path(suite, entry, "observed-source", "lua");
        write_output_file(&source_runner, runner.as_bytes())?;
        let level = format!("-O{}", entry.options.luau_optimization_level.unwrap_or(1));
        let source_output = run_lua_file_with_args("luau", &source_runner, &[&level])?;
        if !source_output.success() {
            return Err(format!(
                "source runtime observation failed:\n{}",
                source_output.render()
            ));
        }
        Ok(Some(Self {
            compiled,
            source_output,
        }))
    }

    pub(super) fn check_chunk(&self, input: &Path) -> Result<(), String> {
        let runtime = lua_tool_path("luau", "luau-bytecode-runner")?;
        let observed = run_command(
            &runtime,
            [input.as_os_str(), self.compiled.as_os_str()],
            "luau-bytecode-runner",
        )?;
        if !observed.success() {
            return Err(format!(
                "compiled runtime observation failed:\n{}",
                observed.render()
            ));
        }
        if let Some(diff) = diff_command_outputs(
            "observed-source",
            &self.source_output,
            "observed-chunk",
            &observed,
        ) {
            return Err(format!("runtime observation output mismatch:\n{diff}"));
        }
        Ok(())
    }
}

fn quote_bytes(bytes: &[u8]) -> String {
    let mut quoted = String::with_capacity(bytes.len() * 4 + 2);
    quoted.push('"');
    for byte in bytes {
        write!(quoted, "\\{byte:03}").expect("writing to String cannot fail");
    }
    quoted.push('"');
    quoted
}
