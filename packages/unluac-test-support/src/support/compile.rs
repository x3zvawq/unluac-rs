//! 构造反编译选项并调用各方言编译器生成 suite artifact；依赖 manifest 和 toolchain，不负责输出比较；例如编译临时生成的 Lua 源码。

use super::*;

pub(super) fn decompile_options(entry: &LuaCaseManifestEntry) -> DecompileOptions {
    let mut options = DecompileOptions {
        dialect: DecompileDialect::Auto,
        target_stage: DecompileStage::Generate,
        debug: Default::default(),
        ..DecompileOptions::default()
    };
    if let Some(mode) = entry.options.naming_mode {
        options.naming.mode = mode;
    }
    options.parse.ignore_debug = entry.options.ignore_debug;
    options.generate.luau_vector_constructor =
        entry
            .options
            .luau_vector
            .map(|vector| LuauVectorConstructor {
                library: vector.library.map(str::to_owned),
                constructor: vector.constructor.to_owned(),
                size: match vector.components {
                    3 => LuauVectorSize::Three,
                    4 => LuauVectorSize::Four,
                    components => panic!("unsupported Luau vector component count: {components}"),
                },
            });
    options
}

/// 使用 vendored 的 `luac` 把某个仓库内 Lua case 编译成测试 chunk。
#[allow(dead_code)]
pub(super) fn compile_manifest_case(entry: &LuaCaseManifestEntry) -> Vec<u8> {
    compile_lua_case_inner(
        <&'static str>::from(entry.dialect),
        entry.path,
        !entry.options.retain_debug,
        entry.options,
    )
}

static TEST_CHUNK_COUNTER: AtomicUsize = AtomicUsize::new(0);

pub(super) fn compile_lua_case_inner(
    dialect_label: &str,
    source_relative: &str,
    strip_debug: bool,
    options: LuaCaseOptions,
) -> Vec<u8> {
    let repo_root = repo_root();
    let source = repo_root.join(source_relative);
    let toolchain = lua_toolchain(dialect_label)
        .unwrap_or_else(|error| panic!("invalid test dialect {dialect_label}: {error}"));
    let output = test_chunk_output_path(
        repo_root,
        dialect_label,
        &source,
        strip_debug,
        toolchain.chunk_extension,
    );
    let command_output =
        compile_lua_file_to_path(dialect_label, &source, &output, strip_debug, options)
            .unwrap_or_else(|error| {
                panic!("should compile test chunk {}: {error}", source.display())
            });
    assert!(
        command_output.success(),
        "bundled compiler failed for {}:\n{}",
        source.display(),
        command_output.render()
    );

    fs::read(&output).unwrap_or_else(|error| {
        panic!(
            "should read compiled test chunk {}: {error}",
            output.display()
        )
    })
}

/// 使用 vendored 的 `luac` 把已经生成好的源码落成稳定的 health chunk 产物。
pub(crate) fn compile_generated_source_to_suite_artifact(
    entry: &LuaCaseManifestEntry,
    suite_label: &str,
    generated_source_path: &Path,
    strip_debug: bool,
) -> Result<(PathBuf, LuaCommandOutput), String> {
    let dialect_label = <&'static str>::from(entry.dialect);
    let toolchain = lua_toolchain(dialect_label)?;
    let output = suite_artifact_path(
        suite_label,
        dialect_label,
        entry.variant,
        "generated-chunk",
        entry.path,
        toolchain.chunk_extension,
    );
    let command_output = compile_lua_file_to_path(
        dialect_label,
        generated_source_path,
        &output,
        strip_debug,
        entry.options,
    )?;
    Ok((output, command_output))
}

pub(super) fn compile_lua_file_to_path(
    dialect_label: &str,
    source: &Path,
    output: &Path,
    strip_debug: bool,
    options: LuaCaseOptions,
) -> Result<LuaCommandOutput, String> {
    let toolchain = lua_toolchain(dialect_label)?;
    let compiler = lua_tool_path(dialect_label, toolchain.compiler_name)?;
    ensure_parent_dir(output)?;
    run_compiler_to_output_path(toolchain, &compiler, source, output, strip_debug, options)
}

#[allow(dead_code)]
pub(super) fn test_chunk_output_path(
    repo_root: &Path,
    dialect_label: &str,
    source: &Path,
    strip_debug: bool,
    chunk_extension: &str,
) -> PathBuf {
    let unique = TEST_CHUNK_COUNTER.fetch_add(1, Ordering::Relaxed);
    let relative = source
        .strip_prefix(repo_root)
        .expect("test source should stay inside repo root");
    repo_root
        .join("target")
        .join("unluac-tests")
        .join(dialect_label)
        .join(if strip_debug { "stripped" } else { "debug" })
        .join(relative)
        .with_extension(format!("{chunk_extension}.{}.{unique}", std::process::id()))
}
