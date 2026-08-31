//! 管理仓库固定的 Lua、LuaJIT 和 Luau 源码与构建产物。
//!
//! Unix 复用上游 Makefile；Windows 使用 Visual Studio C++ 工具链、LuaJIT 的
//! `msvcbuild.bat` 和 Luau 的 CMake，统一输出到 `lua/build`，供 CLI 与测试复用。

use std::env;
use std::ffi::{OsStr, OsString};
use std::fs;
#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;
#[cfg(windows)]
use std::os::windows::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, Result, bail};

const LUAJIT_REV: &str = "659a61693aa3b87661864ad0f12eee14c865cd7f";
const LUAJIT_BRANCH: &str = "v2.1";
const LUAU_URL: &str = "https://github.com/luau-lang/luau/archive/refs/tags/0.713.tar.gz";
const LUAU_EXTRACTED_DIR: &str = "luau-0.713";
const LUAU_UPSTREAM_TARGETS: &[&str] = &["luau", "luau-analyze", "luau-compile", "luau-bytecode"];
const LUAU_TARGETS: &[&str] = &[
    "luau",
    "luau-analyze",
    "luau-compile",
    "luau-bytecode",
    "luau-bytecode-runner",
];
#[cfg(windows)]
const LUAU_CMAKE_TARGETS: &[&str] = &[
    "Luau.Repl.CLI",
    "Luau.Analyze.CLI",
    "Luau.Compile.CLI",
    "Luau.Bytecode.CLI",
    "Luau.BytecodeRunner.CLI",
];

#[derive(Clone, Copy, Debug)]
enum SourceKind {
    Tarball {
        url: &'static str,
        extracted_dir: &'static str,
    },
    Git {
        url: &'static str,
        branch: &'static str,
        rev: &'static str,
    },
}

#[derive(Clone, Copy, Debug)]
enum BuildKind {
    Lua,
    LuaJit,
    Luau,
}

#[derive(Clone, Copy, Debug)]
struct Toolchain {
    key: &'static str,
    pinned: &'static str,
    source: SourceKind,
    build: BuildKind,
}

const TOOLCHAINS: &[Toolchain] = &[
    Toolchain {
        key: "lua5.1",
        pinned: "Lua 5.1.5",
        source: SourceKind::Tarball {
            url: "https://www.lua.org/ftp/lua-5.1.5.tar.gz",
            extracted_dir: "lua-5.1.5",
        },
        build: BuildKind::Lua,
    },
    Toolchain {
        key: "lua5.2",
        pinned: "Lua 5.2.4",
        source: SourceKind::Tarball {
            url: "https://www.lua.org/ftp/lua-5.2.4.tar.gz",
            extracted_dir: "lua-5.2.4",
        },
        build: BuildKind::Lua,
    },
    Toolchain {
        key: "lua5.3",
        pinned: "Lua 5.3.6",
        source: SourceKind::Tarball {
            url: "https://www.lua.org/ftp/lua-5.3.6.tar.gz",
            extracted_dir: "lua-5.3.6",
        },
        build: BuildKind::Lua,
    },
    Toolchain {
        key: "lua5.4",
        pinned: "Lua 5.4.8",
        source: SourceKind::Tarball {
            url: "https://www.lua.org/ftp/lua-5.4.8.tar.gz",
            extracted_dir: "lua-5.4.8",
        },
        build: BuildKind::Lua,
    },
    Toolchain {
        key: "lua5.5",
        pinned: "Lua 5.5.0",
        source: SourceKind::Tarball {
            url: "https://www.lua.org/ftp/lua-5.5.0.tar.gz",
            extracted_dir: "lua-5.5.0",
        },
        build: BuildKind::Lua,
    },
    Toolchain {
        key: "luajit",
        pinned: "LuaJIT v2.1 @ 659a61693aa3b87661864ad0f12eee14c865cd7f",
        source: SourceKind::Git {
            url: "https://luajit.org/git/luajit.git",
            branch: LUAJIT_BRANCH,
            rev: LUAJIT_REV,
        },
        build: BuildKind::LuaJit,
    },
    Toolchain {
        key: "luau",
        pinned: "Luau 0.713",
        source: SourceKind::Tarball {
            url: LUAU_URL,
            extracted_dir: LUAU_EXTRACTED_DIR,
        },
        build: BuildKind::Luau,
    },
];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Action {
    Fetch,
    Build,
    FetchAndBuild,
    Clean,
}

#[derive(Debug, Eq, PartialEq)]
enum CommandLine {
    Help,
    List,
    Run { action: Action, target: String },
}

pub(crate) fn run<I>(args: I) -> Result<()>
where
    I: IntoIterator,
    I::Item: Into<String>,
{
    match parse_args(args)? {
        CommandLine::Help => print_help(),
        CommandLine::List => list_toolchains(),
        CommandLine::Run { action, target } => {
            let root = workspace_root()?;
            run_many(&root, select_toolchains(&target)?, action)?;
        }
    }

    Ok(())
}

fn parse_args<I>(args: I) -> Result<CommandLine>
where
    I: IntoIterator,
    I::Item: Into<String>,
{
    let args = args.into_iter().map(Into::into).collect::<Vec<_>>();

    match args.as_slice() {
        [] => Ok(CommandLine::Help),
        [cmd] if cmd == "help" => Ok(CommandLine::Help),
        [cmd] if cmd == "list" => Ok(CommandLine::List),
        [cmd] if cmd == "init" => Ok(CommandLine::Run {
            action: Action::FetchAndBuild,
            target: "all".to_owned(),
        }),
        [cmd, target] if cmd == "init" => Ok(CommandLine::Run {
            action: Action::FetchAndBuild,
            target: target.clone(),
        }),
        [cmd, target] => Ok(CommandLine::Run {
            action: parse_action(cmd)?,
            target: target.clone(),
        }),
        _ => bail!("unsupported command: {}", args.join(" ")),
    }
}

fn parse_action(value: &str) -> Result<Action> {
    match value {
        "fetch" => Ok(Action::Fetch),
        "build" => Ok(Action::Build),
        "clean" => Ok(Action::Clean),
        _ => bail!("unknown action: {value}"),
    }
}

fn print_help() {
    println!("usage:");
    println!("  cargo lua list");
    println!("  cargo lua init [all|toolchain]");
    println!("  cargo lua fetch <all|toolchain>");
    println!("  cargo lua build <all|toolchain>");
    println!("  cargo lua clean <all|toolchain>");
}

fn list_toolchains() {
    for toolchain in TOOLCHAINS {
        println!("{:<8} {}", toolchain.key, toolchain.pinned);
    }
}

fn select_toolchains(name: &str) -> Result<Vec<&'static Toolchain>> {
    if name == "all" {
        return Ok(TOOLCHAINS.iter().collect());
    }

    TOOLCHAINS
        .iter()
        .find(|toolchain| toolchain.key == name)
        .map(|toolchain| vec![toolchain])
        .with_context(|| format!("unknown toolchain: {name}"))
}

fn run_many(root: &Path, toolchains: Vec<&Toolchain>, action: Action) -> Result<()> {
    for toolchain in toolchains {
        println!("==> {} ({})", toolchain.key, toolchain.pinned);

        match action {
            Action::Fetch => fetch_toolchain(root, toolchain)?,
            Action::Build => build_toolchain(root, toolchain)?,
            Action::FetchAndBuild => {
                fetch_toolchain(root, toolchain)?;
                build_toolchain(root, toolchain)?;
            }
            Action::Clean => clean_toolchain(root, toolchain)?,
        }
    }

    Ok(())
}

fn fetch_toolchain(root: &Path, toolchain: &Toolchain) -> Result<()> {
    match toolchain.source {
        SourceKind::Tarball { url, extracted_dir } => {
            fetch_tarball(root, toolchain, url, extracted_dir)
        }
        SourceKind::Git { url, branch, rev } => fetch_git(root, toolchain, url, branch, rev),
    }
}

fn build_toolchain(root: &Path, toolchain: &Toolchain) -> Result<()> {
    if !source_dir(root, toolchain).exists() {
        fetch_toolchain(root, toolchain)?;
    }

    match toolchain.build {
        BuildKind::Lua => build_stock_lua(root, toolchain),
        BuildKind::LuaJit => build_luajit(root, toolchain),
        BuildKind::Luau => build_luau(root, toolchain),
    }
}

fn clean_toolchain(root: &Path, toolchain: &Toolchain) -> Result<()> {
    remove_dir_if_exists(&source_dir(root, toolchain))?;
    remove_dir_if_exists(&build_dir(root, toolchain))?;
    Ok(())
}

fn fetch_tarball(root: &Path, toolchain: &Toolchain, url: &str, extracted_dir: &str) -> Result<()> {
    let source_root = sources_root(root);
    let destination = source_dir(root, toolchain);

    if destination.exists() {
        println!("reuse {}", destination.display());
        return Ok(());
    }

    fs::create_dir_all(&source_root)
        .with_context(|| format!("failed to create {}", source_root.display()))?;

    let temporary_root = tmp_root(root);
    fs::create_dir_all(&temporary_root)
        .with_context(|| format!("failed to create {}", temporary_root.display()))?;

    let archive_path = temporary_root.join(format!("{}.tar.gz", toolchain.key));
    let extracted_path = source_root.join(extracted_dir);

    run_command(
        "curl",
        [
            OsStr::new("-fL"),
            OsStr::new("--retry"),
            OsStr::new("3"),
            OsStr::new("-o"),
            archive_path.as_os_str(),
            OsStr::new(url),
        ],
        root,
    )?;
    remove_dir_if_exists(&extracted_path)?;
    run_command(
        "tar",
        [
            OsStr::new("-xzf"),
            archive_path.as_os_str(),
            OsStr::new("-C"),
            source_root.as_os_str(),
        ],
        root,
    )?;

    fs::remove_file(&archive_path)
        .with_context(|| format!("failed to remove {}", archive_path.display()))?;
    fs::rename(&extracted_path, &destination).with_context(|| {
        format!(
            "failed to move extracted source from {} to {}",
            extracted_path.display(),
            destination.display()
        )
    })?;

    Ok(())
}

fn fetch_git(root: &Path, toolchain: &Toolchain, url: &str, branch: &str, rev: &str) -> Result<()> {
    let source_root = sources_root(root);
    let destination = source_dir(root, toolchain);

    if destination.exists() {
        println!("reuse {}", destination.display());
        return Ok(());
    }

    fs::create_dir_all(&source_root)
        .with_context(|| format!("failed to create {}", source_root.display()))?;

    run_command(
        "git",
        [
            OsStr::new("clone"),
            OsStr::new("--branch"),
            OsStr::new(branch),
            OsStr::new(url),
            destination.as_os_str(),
        ],
        root,
    )?;
    run_command(
        "git",
        [
            OsStr::new("-C"),
            destination.as_os_str(),
            OsStr::new("checkout"),
            OsStr::new("--detach"),
            OsStr::new(rev),
        ],
        root,
    )?;

    Ok(())
}

#[cfg(not(windows))]
fn build_stock_lua(root: &Path, toolchain: &Toolchain) -> Result<()> {
    let source = source_dir(root, toolchain);
    let build = build_dir(root, toolchain);
    let make_target = lua_make_target()?;

    run_command("make", ["clean"], &source)?;
    run_command("make", [make_target], &source)?;

    reset_build_dir(&build)?;
    copy_executable(&source.join("src/lua"), &build.join(executable_name("lua")))?;
    copy_executable(
        &source.join("src/luac"),
        &build.join(executable_name("luac")),
    )?;

    Ok(())
}

#[cfg(windows)]
fn build_stock_lua(root: &Path, toolchain: &Toolchain) -> Result<()> {
    let source = source_dir(root, toolchain).join("src");
    let build = build_dir(root, toolchain);
    let temporary = tmp_root(root).join(format!("{}-msvc", toolchain.key));
    let vsdevcmd = windows_vsdevcmd()?;
    let source_files = stock_lua_source_files(&source)?;

    remove_dir_if_exists(&temporary)?;
    fs::create_dir_all(&temporary)
        .with_context(|| format!("failed to create {}", temporary.display()))?;

    let files = source_files.join(" ");
    let source_arg = windows_cmd_path(&source);
    let temporary_arg = windows_cmd_path(&temporary);
    let vsdevcmd_arg = windows_cmd_path(&vsdevcmd);
    let architecture = windows_visual_studio_architecture();
    let cl_flags = "/nologo /O2 /MD /D_CRT_SECURE_NO_DEPRECATE /I.";
    let command = format!(
        "call {vsdevcmd_arg} -arch={architecture} -no_logo && cd /d {source_arg} && cl {cl_flags} /Fo{temporary_arg}\\ /Fe:{temporary_arg}\\lua.exe {files} lua.c && cl {cl_flags} /Fo{temporary_arg}\\ /Fe:{temporary_arg}\\luac.exe {files} luac.c"
    );
    run_windows_command(&command, root)?;

    reset_build_dir(&build)?;
    copy_executable(
        &temporary.join("lua.exe"),
        &build.join(executable_name("lua")),
    )?;
    copy_executable(
        &temporary.join("luac.exe"),
        &build.join(executable_name("luac")),
    )?;
    remove_dir_if_exists(&temporary)?;

    Ok(())
}

#[cfg(not(windows))]
fn build_luajit(root: &Path, toolchain: &Toolchain) -> Result<()> {
    ensure_unix_host("LuaJIT")?;

    let source = source_dir(root, toolchain);
    let build = build_dir(root, toolchain);
    let macos_target = macos_deployment_target()?;
    let extra_env = macos_target
        .as_deref()
        .map(|target| [("MACOSX_DEPLOYMENT_TARGET", target)])
        .unwrap_or_default();

    run_with_env("make", ["clean"], &source, &extra_env)?;
    run_with_env("make", std::iter::empty::<&str>(), &source, &extra_env)?;

    reset_build_dir(&build)?;
    copy_executable(
        &source.join("src/luajit"),
        &build.join(executable_name("luajit")),
    )?;
    copy_dir_all(&source.join("src/jit"), &build.join("jit"))?;
    write_script(
        &build.join(executable_name("luac")),
        r#"#!/usr/bin/env sh
SELF_DIR="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
export LUA_PATH="$SELF_DIR/?.lua;$SELF_DIR/?/init.lua;$SELF_DIR/jit/?.lua;$SELF_DIR/jit/?/init.lua;;"
exec "$SELF_DIR/luajit" -b "$@"
"#,
    )?;

    Ok(())
}

#[cfg(windows)]
fn build_luajit(root: &Path, toolchain: &Toolchain) -> Result<()> {
    let source = source_dir(root, toolchain);
    let build = build_dir(root, toolchain);
    let vsdevcmd = windows_vsdevcmd()?;
    let command = format!(
        "call {} -arch={} -no_logo && cd /d {} && call msvcbuild.bat",
        windows_cmd_path(&vsdevcmd),
        windows_visual_studio_architecture(),
        windows_cmd_path(&source.join("src")),
    );
    run_windows_command(&command, root)?;

    reset_build_dir(&build)?;
    copy_executable(
        &source.join("src/luajit.exe"),
        &build.join(executable_name("luajit")),
    )?;
    // Windows 构建是 DLL 版本；把运行时 DLL 放在两个入口旁边，保证直接启动时能解析。
    copy_executable(&source.join("src/lua51.dll"), &build.join("lua51.dll"))?;
    copy_executable(
        &source.join("src/luajit.exe"),
        &build.join(executable_name("luac")),
    )?;
    copy_dir_all(&source.join("src/jit"), &build.join("jit"))?;

    Ok(())
}

#[cfg(not(windows))]
fn build_luau(root: &Path, toolchain: &Toolchain) -> Result<()> {
    ensure_unix_host("Luau")?;

    let source = source_dir(root, toolchain);
    let build = build_dir(root, toolchain);

    run_command("make", ["config=release", "clean"], &source)?;
    run_command(
        "make",
        std::iter::once("config=release").chain(LUAU_UPSTREAM_TARGETS.iter().copied()),
        &source,
    )?;
    build_luau_bytecode_runner_unix(root, &source)?;

    reset_build_dir(&build)?;
    for target in LUAU_TARGETS {
        copy_executable(
            &source.join("build/release").join(target),
            &build.join(executable_name(target)),
        )?;
    }

    Ok(())
}

#[cfg(not(windows))]
fn build_luau_bytecode_runner_unix(root: &Path, source: &Path) -> Result<()> {
    let compiler = env::var("CXX").unwrap_or_else(|_| "c++".to_owned());
    let output = source.join("build/release/luau-bytecode-runner");
    let args = vec![
        OsString::from("-std=c++17"),
        OsString::from("-O2"),
        OsString::from("-DNDEBUG"),
        OsString::from("-ICommon/include"),
        OsString::from("-IVM/include"),
        root.join("lua/patches/luau/BytecodeRunner.cpp")
            .into_os_string(),
        source.join("build/release/libluauvm.a").into_os_string(),
        source
            .join("build/release/libluaucommon.a")
            .into_os_string(),
        OsString::from("-o"),
        output.into_os_string(),
    ];
    run_command(&compiler, args, source)
}

#[cfg(windows)]
fn build_luau(root: &Path, toolchain: &Toolchain) -> Result<()> {
    let source = source_dir(root, toolchain);
    let build = build_dir(root, toolchain);
    let temporary = tmp_root(root).join("luau-cmake");
    let vsdevcmd = windows_vsdevcmd()?;

    remove_dir_if_exists(&temporary)?;
    // Luau 在 MSVC 下默认用 C++ 异常传播错误；CLI 的 extern-C 边界会导致运行时崩溃，
    // 该选项让上游启用 longjmp 错误路径。固定源码是 UTF-8，显式指定编码以避免本地代码页
    // 触发 C4819 并误读源文件。
    let command = format!(
        "call {} -arch={} -no_logo && cmake -S {} -B {} -G Ninja -DCMAKE_BUILD_TYPE=Release -DLUAU_SOURCE_DIR={} -DLUAU_EXTERN_C=ON -DCMAKE_CXX_FLAGS=/utf-8 -DCMAKE_C_FLAGS=/utf-8 && cmake --build {} --target {} --parallel",
        windows_cmd_path(&vsdevcmd),
        windows_visual_studio_architecture(),
        windows_cmd_path(&root.join("lua/patches/luau")),
        windows_cmd_path(&temporary),
        windows_cmd_path(&source),
        windows_cmd_path(&temporary),
        LUAU_CMAKE_TARGETS.join(" "),
    );
    run_windows_command(&command, root)?;

    reset_build_dir(&build)?;
    for target in LUAU_TARGETS {
        copy_executable(
            &temporary.join(format!("{target}.exe")),
            &build.join(executable_name(target)),
        )?;
    }
    remove_dir_if_exists(&temporary)?;

    Ok(())
}

fn workspace_root() -> Result<PathBuf> {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .map(Path::to_path_buf)
        .context("failed to resolve workspace root")
}

fn lua_root(root: &Path) -> PathBuf {
    root.join("lua")
}

fn sources_root(root: &Path) -> PathBuf {
    lua_root(root).join("sources")
}

fn source_dir(root: &Path, toolchain: &Toolchain) -> PathBuf {
    sources_root(root).join(toolchain.key)
}

fn build_dir(root: &Path, toolchain: &Toolchain) -> PathBuf {
    lua_root(root).join("build").join(toolchain.key)
}

fn executable_name(name: &str) -> String {
    format!("{name}{}", env::consts::EXE_SUFFIX)
}

fn tmp_root(root: &Path) -> PathBuf {
    lua_root(root).join(".tmp")
}

#[cfg(windows)]
fn stock_lua_source_files(source: &Path) -> Result<Vec<String>> {
    let mut files = fs::read_dir(source)
        .with_context(|| format!("failed to read {}", source.display()))?
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().and_then(OsStr::to_str) == Some("c"))
        .filter_map(|path| {
            let name = path.file_name()?.to_str()?.to_owned();
            (!matches!(name.as_str(), "lua.c" | "luac.c")).then_some(name)
        })
        .collect::<Vec<_>>();
    files.sort();
    if files.is_empty() {
        bail!("no stock Lua C sources found in {}", source.display());
    }
    Ok(files)
}

#[cfg(windows)]
fn windows_visual_studio_architecture() -> &'static str {
    match env::consts::ARCH {
        "x86" => "x86",
        "aarch64" => "arm64",
        _ => "x64",
    }
}

#[cfg(windows)]
fn windows_cmd_path(path: &Path) -> String {
    format!("\"{}\"", path.display())
}

#[cfg(windows)]
fn windows_vsdevcmd() -> Result<PathBuf> {
    if let Some(installation) = env::var_os("VSINSTALLDIR") {
        let candidate = PathBuf::from(installation)
            .join("Common7")
            .join("Tools")
            .join("VsDevCmd.bat");
        if candidate.is_file() {
            return Ok(candidate);
        }
    }

    let mut vswhere_candidates = Vec::new();
    if let Some(program_files_x86) = env::var_os("ProgramFiles(x86)") {
        vswhere_candidates.push(
            PathBuf::from(program_files_x86)
                .join("Microsoft Visual Studio")
                .join("Installer")
                .join("vswhere.exe"),
        );
    }
    if let Some(program_files) = env::var_os("ProgramFiles") {
        vswhere_candidates.push(
            PathBuf::from(program_files)
                .join("Microsoft Visual Studio")
                .join("Installer")
                .join("vswhere.exe"),
        );
    }

    for vswhere in vswhere_candidates {
        if !vswhere.is_file() {
            continue;
        }
        let output = Command::new(&vswhere)
            .args([
                OsStr::new("-latest"),
                OsStr::new("-products"),
                OsStr::new("*"),
                OsStr::new("-requires"),
                OsStr::new("Microsoft.VisualStudio.Component.VC.Tools.x86.x64"),
                OsStr::new("-property"),
                OsStr::new("installationPath"),
            ])
            .output()
            .with_context(|| format!("failed to run {}", vswhere.display()))?;
        if !output.status.success() {
            continue;
        }
        if let Some(installation) = String::from_utf8_lossy(&output.stdout)
            .lines()
            .map(str::trim)
            .find(|line| !line.is_empty())
        {
            let candidate = PathBuf::from(installation)
                .join("Common7")
                .join("Tools")
                .join("VsDevCmd.bat");
            if candidate.is_file() {
                return Ok(candidate);
            }
        }
    }

    if let Some(program_files) = env::var_os("ProgramFiles") {
        let visual_studio_root = PathBuf::from(program_files).join("Microsoft Visual Studio");
        if let Ok(versions) = fs::read_dir(&visual_studio_root) {
            for version in versions.flatten() {
                if let Ok(editions) = fs::read_dir(version.path()) {
                    for edition in editions.flatten() {
                        let candidate = edition
                            .path()
                            .join("Common7")
                            .join("Tools")
                            .join("VsDevCmd.bat");
                        if candidate.is_file() {
                            return Ok(candidate);
                        }
                    }
                }
            }
        }
    }

    bail!(
        "Windows Lua bootstrap requires Visual Studio C++ build tools ".to_owned()
            + "(Desktop development with C++, Windows SDK, and CMake/Ninja); "
            + "install that workload or run from a Visual Studio developer prompt"
    )
}

#[cfg(windows)]
fn run_windows_command(command_line: &str, cwd: &Path) -> Result<()> {
    let mut command = Command::new("cmd.exe");
    command
        .arg("/d")
        .arg("/c")
        // `/c` 会把余下内容当作完整 shell 文本；不能用普通参数转义，否则会破坏
        // Visual Studio 与 workspace 路径上的嵌套引号。
        .raw_arg(command_line);
    let status = command
        .current_dir(cwd)
        .status()
        .with_context(|| format!("failed to run Windows command in {}", cwd.display()))?;

    if status.success() {
        Ok(())
    } else {
        bail!("Windows command failed with status {status}: {command_line}")
    }
}

fn reset_build_dir(path: &Path) -> Result<()> {
    remove_dir_if_exists(path)?;
    fs::create_dir_all(path).with_context(|| format!("failed to create {}", path.display()))?;
    Ok(())
}

fn remove_dir_if_exists(path: &Path) -> Result<()> {
    if path.exists() {
        fs::remove_dir_all(path).with_context(|| format!("failed to remove {}", path.display()))?;
    }

    Ok(())
}

fn copy_executable(from: &Path, to: &Path) -> Result<()> {
    fs::copy(from, to)
        .with_context(|| format!("failed to copy {} to {}", from.display(), to.display()))?;
    make_executable(to)?;
    Ok(())
}

fn copy_dir_all(from: &Path, to: &Path) -> Result<()> {
    fs::create_dir_all(to).with_context(|| format!("failed to create {}", to.display()))?;

    for entry in fs::read_dir(from).with_context(|| format!("failed to read {}", from.display()))? {
        let entry = entry.with_context(|| format!("failed to read entry in {}", from.display()))?;
        let file_type = entry
            .file_type()
            .with_context(|| format!("failed to inspect {}", entry.path().display()))?;
        let destination = to.join(entry.file_name());

        if file_type.is_dir() {
            copy_dir_all(&entry.path(), &destination)?;
        } else {
            fs::copy(entry.path(), &destination).with_context(|| {
                format!(
                    "failed to copy {} to {}",
                    entry.path().display(),
                    destination.display()
                )
            })?;
        }
    }

    Ok(())
}

#[cfg(not(windows))]
fn write_script(path: &Path, contents: &str) -> Result<()> {
    fs::write(path, contents).with_context(|| format!("failed to write {}", path.display()))?;
    make_executable(path)?;
    Ok(())
}

#[cfg(unix)]
fn make_executable(path: &Path) -> Result<()> {
    let mut permissions = fs::metadata(path)
        .with_context(|| format!("failed to stat {}", path.display()))?
        .permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(path, permissions)
        .with_context(|| format!("failed to chmod {}", path.display()))?;
    Ok(())
}

#[cfg(not(unix))]
fn make_executable(_: &Path) -> Result<()> {
    Ok(())
}

#[cfg(not(windows))]
fn lua_make_target() -> Result<&'static str> {
    match env::consts::OS {
        "macos" => Ok("macosx"),
        "linux" => Ok("linux"),
        other => bail!("unsupported host OS for stock Lua builds: {other}"),
    }
}

#[cfg(not(windows))]
fn ensure_unix_host(name: &str) -> Result<()> {
    match env::consts::OS {
        "macos" | "linux" => Ok(()),
        other => bail!("{name} bootstrap currently supports macOS/Linux only, got {other}"),
    }
}

fn run_command<I, S>(program: &str, args: I, cwd: &Path) -> Result<()>
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    run_with_env(program, args, cwd, &[])
}

fn run_with_env<I, S>(program: &str, args: I, cwd: &Path, extra_env: &[(&str, &str)]) -> Result<()>
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    let mut command = Command::new(program);
    command.args(args).current_dir(cwd);

    for (key, value) in extra_env {
        command.env(key, value);
    }

    let status = command
        .status()
        .with_context(|| format!("failed to spawn `{program}` in {}", cwd.display()))?;

    if status.success() {
        Ok(())
    } else {
        bail!("`{program}` failed with status {status}")
    }
}

#[cfg(not(windows))]
fn macos_deployment_target() -> Result<Option<String>> {
    if env::consts::OS != "macos" {
        return Ok(None);
    }

    let output = Command::new("sw_vers")
        .arg("-productVersion")
        .output()
        .context("failed to run `sw_vers -productVersion`")?;

    if !output.status.success() {
        bail!(
            "`sw_vers -productVersion` failed with status {}",
            output.status
        );
    }

    let version = String::from_utf8(output.stdout).context("macOS version is not valid UTF-8")?;
    let mut parts = version.trim().split('.');
    let major = parts.next().context("missing macOS major version")?;
    let minor = parts.next().unwrap_or("0");

    Ok(Some(format!("{major}.{minor}")))
}

#[cfg(test)]
mod tests {
    use super::{Action, CommandLine, parse_action, parse_args, select_toolchains};

    #[test]
    fn parse_args_should_return_help_when_no_arguments_are_provided() {
        let command = parse_args(Vec::<String>::new()).expect("empty args should be accepted");

        assert_eq!(command, CommandLine::Help);
    }

    #[test]
    fn parse_args_should_expand_init_to_fetch_and_build_all_toolchains() {
        let command = parse_args(["init"]).expect("init should be accepted");

        assert_eq!(
            command,
            CommandLine::Run {
                action: Action::FetchAndBuild,
                target: "all".to_owned(),
            }
        );
    }

    #[test]
    fn parse_action_should_reject_unknown_commands() {
        let error = parse_action("deploy").expect_err("unknown actions should fail");

        assert_eq!(error.to_string(), "unknown action: deploy");
    }

    #[test]
    fn select_toolchains_should_return_matching_toolchain() {
        let toolchains = select_toolchains("lua5.4").expect("known toolchain should resolve");

        assert_eq!(toolchains.len(), 1);
        assert_eq!(toolchains[0].key, "lua5.4");
    }
}
