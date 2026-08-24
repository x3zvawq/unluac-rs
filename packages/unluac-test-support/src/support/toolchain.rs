//! 定位 pinned Lua 工具、管理 artifact 路径并执行子进程；依赖仓库布局和文件系统，不负责测试语义；例如按方言选择 luac/luau-compile。

use super::*;

pub(super) fn repo_root() -> &'static PathBuf {
    static REPO_ROOT: OnceLock<PathBuf> = OnceLock::new();

    REPO_ROOT.get_or_init(|| {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .map(Path::to_path_buf)
            .expect("test support crate should live under packages/")
    })
}

pub(super) fn sanitize_repo_paths(text: &str) -> String {
    let root = repo_root();
    let root = root.to_string_lossy();
    let root_with_separator = format!("{root}/");
    text.replace(&root_with_separator, "")
}

pub(super) fn primary_command_reason(output: &LuaCommandOutput) -> Option<String> {
    [&output.stderr, &output.stdout]
        .into_iter()
        .find_map(|bytes| {
            String::from_utf8_lossy(bytes)
                .lines()
                .map(str::trim)
                .find(|line| !line.is_empty())
                .map(sanitize_repo_paths)
        })
        .map(|line| {
            line.rsplit(": ")
                .next()
                .map(str::trim)
                .filter(|reason| !reason.is_empty())
                .unwrap_or(line.as_str())
                .to_owned()
        })
}

pub(super) fn lua_tool_path(dialect_label: &str, tool_name: &str) -> Result<PathBuf, String> {
    let tool = repo_root()
        .join("lua")
        .join("build")
        .join(dialect_label)
        .join(tool_name);
    if !tool.exists() {
        return Err(format!(
            "missing bundled {tool_name} for {dialect_label}: {}",
            tool.display()
        ));
    }
    Ok(tool)
}

pub(super) fn suite_artifact_path(
    suite_label: &str,
    dialect_label: &str,
    variant: Option<LuaCaseVariant>,
    artifact_label: &str,
    source_relative: &str,
    extension: &str,
) -> PathBuf {
    let dialect_root = repo_root()
        .join("target")
        .join("unluac-tests")
        .join(suite_label)
        .join(dialect_label);
    variant
        .map_or(dialect_root.clone(), |variant| {
            dialect_root.join(variant.label())
        })
        .join(artifact_label)
        .join(source_relative)
        .with_extension(extension)
}

pub(super) fn write_output_file(path: &Path, bytes: &[u8]) -> Result<(), String> {
    ensure_parent_dir(path)?;
    fs::write(path, bytes)
        .map_err(|error| format!("should write output file {}: {error}", path.display()))
}

pub(super) fn ensure_parent_dir(path: &Path) -> Result<(), String> {
    let Some(parent) = path.parent() else {
        return Err(format!(
            "path {} should always have a parent",
            path.display()
        ));
    };
    fs::create_dir_all(parent)
        .map_err(|error| format!("should create directory {}: {error}", parent.display()))
}

pub(super) fn run_compiler_to_output_path(
    toolchain: LuaToolchain,
    compiler: &Path,
    source: &Path,
    output: &Path,
    strip_debug: bool,
    options: LuaCaseOptions,
) -> Result<LuaCommandOutput, String> {
    if toolchain.compiler_protocol != LuaCompilerProtocol::LuauBinaryStdout
        && (options.luau_optimization_level.is_some() || options.luau_vector.is_some())
    {
        return Err("Luau case options require the Luau compiler".to_owned());
    }

    match toolchain.compiler_protocol {
        LuaCompilerProtocol::LuacStyle => {
            let mut command = Command::new(compiler);
            if strip_debug {
                command.arg("-s");
            }
            command.arg("-o").arg(output).arg(source);
            let output = command.output().map_err(|error| {
                format!(
                    "should spawn compiler {} for {}: {error}",
                    compiler.display(),
                    source.display()
                )
            })?;
            Ok(LuaCommandOutput {
                status_code: output.status.code(),
                stdout: output.stdout,
                stderr: output.stderr,
            })
        }
        LuaCompilerProtocol::LuaJitBytecodeTool => {
            let mut command = Command::new(compiler);
            #[cfg(windows)]
            configure_windows_luajit_compiler(&mut command, compiler);
            command.arg(if strip_debug { "-s" } else { "-g" });
            let output = command.arg(source).arg(output).output().map_err(|error| {
                format!(
                    "should spawn compiler {} for {}: {error}",
                    compiler.display(),
                    source.display()
                )
            })?;
            Ok(LuaCommandOutput {
                status_code: output.status.code(),
                stdout: output.stdout,
                stderr: output.stderr,
            })
        }
        LuaCompilerProtocol::LuauBinaryStdout => {
            let debug_level = if strip_debug { "-g0" } else { "-g2" };
            let mut command = Command::new(compiler);
            command.arg("--binary").arg(debug_level);
            if let Some(level) = options.luau_optimization_level {
                if level > 2 {
                    return Err(format!("invalid Luau optimization level: {level}"));
                }
                command.arg(format!("-O{level}"));
            }
            if let Some(vector) = options.luau_vector {
                if vector.constructor.is_empty() {
                    return Err("Luau vector constructor must not be empty".to_owned());
                }
                if !matches!(vector.components, 3 | 4) {
                    return Err(format!(
                        "unsupported Luau vector component count: {}",
                        vector.components
                    ));
                }
                if let Some(library) = vector.library {
                    if library.is_empty() {
                        return Err("Luau vector library must not be empty".to_owned());
                    }
                    command.arg(format!("--vector-lib={library}"));
                }
                command.arg(format!("--vector-ctor={}", vector.constructor));
            }
            let output_bytes = command.arg(source).output().map_err(|error| {
                format!(
                    "should spawn compiler {} for {}: {error}",
                    compiler.display(),
                    source.display()
                )
            })?;
            if output_bytes.status.success() {
                write_output_file(output, &output_bytes.stdout)?;
            }
            Ok(LuaCommandOutput {
                status_code: output_bytes.status.code(),
                stdout: output_bytes.stdout,
                stderr: output_bytes.stderr,
            })
        }
    }
}

#[cfg(windows)]
fn configure_windows_luajit_compiler(command: &mut Command, compiler: &Path) {
    command.arg("-b");
    let root = compiler.parent().unwrap_or_else(|| Path::new("."));
    let lua_path = [
        root.join("?.lua"),
        root.join("?").join("init.lua"),
        root.join("jit").join("?.lua"),
        root.join("jit").join("?").join("init.lua"),
    ]
    .into_iter()
    .map(|path| path.to_string_lossy().into_owned())
    .chain(std::iter::once(String::new()))
    .collect::<Vec<_>>()
    .join(";");
    command.env("LUA_PATH", lua_path);
}

pub(super) fn run_command<I, S>(
    command_path: &Path,
    args: I,
    tool_name: &str,
) -> Result<LuaCommandOutput, String>
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    let output = Command::new(command_path)
        .args(args)
        .output()
        .map_err(|error| {
            format!(
                "should spawn {tool_name} {}: {error}",
                command_path.display()
            )
        })?;
    Ok(LuaCommandOutput {
        status_code: output.status.code(),
        stdout: output.stdout,
        stderr: output.stderr,
    })
}

pub(super) fn render_status_code(status_code: Option<i32>) -> String {
    match status_code {
        Some(code) => code.to_string(),
        None => "terminated-by-signal".to_owned(),
    }
}

pub(super) fn render_bytes(bytes: &[u8]) -> String {
    if bytes.is_empty() {
        "<empty>".to_owned()
    } else {
        sanitize_repo_paths(&String::from_utf8_lossy(bytes))
    }
}
