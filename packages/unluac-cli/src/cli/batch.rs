//! 目录递归批量并发反编译执行器。
//!
//! 仅在 CLI 层处理文件系统遍历、魔数过滤、多线程调度与目录镜像写回；核心反编译逻辑完全复用 `unluac`。

use std::collections::BTreeMap;
use std::ffi::OsStr;
use std::fs;
use std::io::Read;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

use unluac::decompile::{DecompileOptions, GeneratedChunkKind, decompile};
use unluac::parser::{ParseError, detect_dialect};

use super::CliError;

const WORKER_STACK_SIZE: usize = 16 * 1024 * 1024;

#[derive(Debug)]
pub(super) struct BatchFailure {
    pub path: String,
    pub error: String,
}

#[derive(Debug)]
pub(super) struct BatchSummary {
    pub input_dir: String,
    pub output_dir: String,
    pub scanned: usize,
    pub decompiled: usize,
    pub diagnostic: usize,
    pub skipped: usize,
    pub failed: usize,
    pub failures: Vec<BatchFailure>,
}

pub(super) fn run_batch_directory(
    input_dir: &Path,
    output_dir: &Path,
    options: &DecompileOptions,
    jobs: Option<usize>,
) -> Result<BatchSummary, CliError> {
    let canonical_input = fs::canonicalize(input_dir).map_err(|source| CliError::Io {
        action: "resolve batch input directory",
        path: input_dir.to_path_buf(),
        source,
    })?;

    if output_dir.exists()
        && let Ok(canonical_out) = fs::canonicalize(output_dir)
        && canonical_out == canonical_input
    {
        return Err(CliError::Usage(format!(
            "refusing to run batch decompilation in place (`{}` == `{}`); choose a different `--output` directory",
            input_dir.display(),
            output_dir.display()
        )));
    }

    fs::create_dir_all(output_dir).map_err(|source| CliError::Io {
        action: "create batch output directory",
        path: output_dir.to_path_buf(),
        source,
    })?;

    let canonical_output = fs::canonicalize(output_dir).map_err(|source| CliError::Io {
        action: "resolve batch output directory",
        path: output_dir.to_path_buf(),
        source,
    })?;
    if canonical_output == canonical_input {
        return Err(CliError::Usage(format!(
            "refusing to run batch decompilation in place (`{}` == `{}`); choose a different `--output` directory",
            input_dir.display(),
            output_dir.display()
        )));
    }

    let mut files = Vec::new();
    let mut walk_skipped = 0usize;
    let mut walk_failures = Vec::new();
    collect_files_recursive(
        input_dir,
        input_dir,
        &canonical_output,
        &mut files,
        &mut walk_skipped,
        &mut walk_failures,
    )?;
    files.sort();

    // 预计算每个输入文件对应的输出路径并自动消解同名不同后缀碰撞（例如 `foo.lua` 与 `foo.luac`）。
    let output_paths = resolve_batch_output_paths(input_dir, output_dir, &files);

    let worker_count = jobs
        .filter(|&j| j > 0)
        .unwrap_or_else(|| {
            std::thread::available_parallelism()
                .map(usize::from)
                .unwrap_or(4)
        })
        .min(files.len().max(1));

    let next_index = AtomicUsize::new(0);
    let decompiled = AtomicUsize::new(0);
    let diagnostic = AtomicUsize::new(0);
    let skipped = AtomicUsize::new(walk_skipped);
    let failures = Mutex::new(walk_failures);

    std::thread::scope(|scope| {
        for worker_idx in 0..worker_count {
            let builder = std::thread::Builder::new()
                .name(format!("unluac-batch-{worker_idx}"))
                .stack_size(WORKER_STACK_SIZE);
            builder
                .spawn_scoped(scope, || {
                    loop {
                        let idx = next_index.fetch_add(1, Ordering::Relaxed);
                        let Some(path) = files.get(idx) else {
                            break;
                        };
                        let out_path = &output_paths[idx];
                        let rel = path.strip_prefix(input_dir).unwrap_or(path);
                        let rel_display = rel.to_string_lossy().replace('\\', "/");

                        // 仅读前 16 字节快速筛除非字节码资源（如图片/视频/普通文本），避免整文件读入内存。
                        match quick_sniff_may_be_bytecode(path) {
                            Ok(false) => {
                                skipped.fetch_add(1, Ordering::Relaxed);
                                continue;
                            }
                            Ok(true) => {}
                            Err(err) => {
                                failures.lock().unwrap().push(BatchFailure {
                                    path: rel_display,
                                    error: format!("read failed: {err}"),
                                });
                                continue;
                            }
                        }

                        let bytes = match fs::read(path) {
                            Ok(b) => b,
                            Err(err) => {
                                failures.lock().unwrap().push(BatchFailure {
                                    path: rel_display,
                                    error: format!("read failed: {err}"),
                                });
                                continue;
                            }
                        };

                        // 依据完整头部协议魔数自动跳过非编译脚本文件
                        if matches!(
                            detect_dialect(&bytes),
                            Err(ParseError::InvalidSignature { .. })
                        ) {
                            skipped.fetch_add(1, Ordering::Relaxed);
                            continue;
                        }

                        let run_res = catch_unwind(AssertUnwindSafe(|| {
                            decompile(&bytes, options.clone())
                        }));
                        match run_res {
                            Ok(Ok(result)) => {
                                let Some(generated) = result.state.generated else {
                                    failures.lock().unwrap().push(BatchFailure {
                                        path: rel_display,
                                        error: "no generated source produced".to_owned(),
                                    });
                                    continue;
                                };
                                if let Some(parent) = out_path.parent()
                                    && let Err(err) = fs::create_dir_all(parent)
                                {
                                    failures.lock().unwrap().push(BatchFailure {
                                        path: rel_display,
                                        error: format!("create parent dir failed: {err}"),
                                    });
                                    continue;
                                }
                                if let Err(err) = fs::write(out_path, &generated.source) {
                                    failures.lock().unwrap().push(BatchFailure {
                                        path: rel_display,
                                        error: format!("write failed: {err}"),
                                    });
                                    continue;
                                }
                                decompiled.fetch_add(1, Ordering::Relaxed);
                                if generated.kind == GeneratedChunkKind::DiagnosticPseudocode {
                                    diagnostic.fetch_add(1, Ordering::Relaxed);
                                }
                            }
                            Ok(Err(err)) => {
                                failures.lock().unwrap().push(BatchFailure {
                                    path: rel_display,
                                    error: err.to_string(),
                                });
                            }
                            Err(panic_payload) => {
                                let msg = panic_payload
                                    .downcast_ref::<&str>()
                                    .copied()
                                    .or_else(|| {
                                        panic_payload.downcast_ref::<String>().map(String::as_str)
                                    })
                                    .unwrap_or("unknown internal panic");
                                failures.lock().unwrap().push(BatchFailure {
                                    path: rel_display,
                                    error: format!("internal panic while decompiling: {msg}"),
                                });
                            }
                        }
                    }
                })
                .expect("spawn batch worker thread");
        }
    });

    let mut failures = failures.into_inner().unwrap();
    failures.sort_by(|a, b| a.path.cmp(&b.path));
    let failed = failures.len();

    Ok(BatchSummary {
        input_dir: input_dir.display().to_string(),
        output_dir: output_dir.display().to_string(),
        scanned: files.len() + walk_skipped,
        decompiled: decompiled.load(Ordering::Relaxed),
        diagnostic: diagnostic.load(Ordering::Relaxed),
        skipped: skipped.load(Ordering::Relaxed),
        failed,
        failures,
    })
}

fn quick_sniff_may_be_bytecode(path: &Path) -> std::io::Result<bool> {
    let mut file = fs::File::open(path)?;
    let mut head = [0u8; 16];
    let n = file.read(&mut head)?;
    if n < 2 {
        return Ok(false);
    }
    // PUC Lua / LuaJIT 均以 0x1b ('\x1bLua' 或 '\x1bLJ') 开头；Luau 字节码首字节为版本号 3..=7。
    let b0 = head[0];
    if b0 == 0x1b {
        return Ok(head.starts_with(b"\x1bLua") || head.starts_with(b"\x1bLJ"));
    }
    Ok((3..=7).contains(&b0))
}

fn collect_files_recursive(
    root: &Path,
    dir: &Path,
    skip_canonical_dir: &Path,
    out: &mut Vec<PathBuf>,
    skipped: &mut usize,
    failures: &mut Vec<BatchFailure>,
) -> Result<(), CliError> {
    let entries = match fs::read_dir(dir) {
        Ok(entries) => entries,
        Err(source) => {
            if dir == root {
                return Err(CliError::Io {
                    action: "read directory",
                    path: dir.to_path_buf(),
                    source,
                });
            }
            let rel = dir.strip_prefix(root).unwrap_or(dir);
            failures.push(BatchFailure {
                path: rel.to_string_lossy().replace('\\', "/"),
                error: format!("read subdirectory failed: {source}"),
            });
            return Ok(());
        }
    };
    for entry in entries {
        let entry = match entry {
            Ok(e) => e,
            Err(err) => {
                let rel = dir.strip_prefix(root).unwrap_or(dir);
                failures.push(BatchFailure {
                    path: rel.to_string_lossy().replace('\\', "/"),
                    error: format!("read directory entry failed: {err}"),
                });
                continue;
            }
        };
        let path = entry.path();
        let file_type = match entry.file_type() {
            Ok(ft) => ft,
            Err(err) => {
                let rel = path.strip_prefix(root).unwrap_or(&path);
                failures.push(BatchFailure {
                    path: rel.to_string_lossy().replace('\\', "/"),
                    error: format!("inspect entry failed: {err}"),
                });
                continue;
            }
        };
        if file_type.is_symlink() {
            *skipped += 1;
            continue;
        }
        if file_type.is_dir() {
            if fs::canonicalize(&path).is_ok_and(|c| c == skip_canonical_dir) {
                continue;
            }
            collect_files_recursive(root, &path, skip_canonical_dir, out, skipped, failures)?;
        } else if file_type.is_file() {
            out.push(path);
        }
    }
    Ok(())
}

fn resolve_batch_output_paths(
    input_dir: &Path,
    output_dir: &Path,
    files: &[PathBuf],
) -> Vec<PathBuf> {
    let mut initial: Vec<PathBuf> = files
        .iter()
        .map(|p| mirror_output_path(output_dir, p.strip_prefix(input_dir).unwrap_or(p)))
        .collect();
    let mut counts: BTreeMap<PathBuf, usize> = BTreeMap::new();
    for out in &initial {
        *counts.entry(out.clone()).or_insert(0) += 1;
    }
    for (idx, path) in files.iter().enumerate() {
        if counts.get(&initial[idx]).copied().unwrap_or(0) > 1 {
            let rel = path.strip_prefix(input_dir).unwrap_or(path);
            let is_plain_lua = rel
                .extension()
                .and_then(OsStr::to_str)
                .is_some_and(|e| e.eq_ignore_ascii_case("lua"));
            if !is_plain_lua {
                let mut os = output_dir.join(rel).into_os_string();
                os.push(".lua");
                initial[idx] = PathBuf::from(os);
            }
        }
    }
    initial
}

fn mirror_output_path(output_dir: &Path, rel: &Path) -> PathBuf {
    let ext = rel
        .extension()
        .and_then(OsStr::to_str)
        .map(str::to_ascii_lowercase);
    match ext.as_deref() {
        Some("lua") => output_dir.join(rel),
        Some("luac" | "out" | "lb" | "ljbc" | "luau" | "bc") => {
            output_dir.join(rel.with_extension("lua"))
        }
        _ => {
            let mut os = output_dir.join(rel).into_os_string();
            os.push(".lua");
            PathBuf::from(os)
        }
    }
}
