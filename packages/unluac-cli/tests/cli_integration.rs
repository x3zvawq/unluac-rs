use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

const SAMPLE_LUA51: &[u8] = &[
    27, 76, 117, 97, 81, 0, 1, 4, 8, 4, 8, 0, 12, 0, 0, 0, 0, 0, 0, 0, 64, 115, 97, 109, 112, 108,
    101, 46, 108, 117, 97, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 5, 9, 0, 0, 0, 36, 0, 0, 0, 65, 0,
    0, 0, 133, 64, 0, 0, 192, 0, 0, 0, 1, 129, 0, 0, 220, 128, 0, 1, 20, 1, 128, 0, 156, 64, 128,
    1, 30, 0, 128, 0, 3, 0, 0, 0, 4, 5, 0, 0, 0, 0, 0, 0, 0, 128, 129, 1, 2, 0, 4, 6, 0, 0, 0, 0,
    0, 0, 0, 112, 114, 105, 110, 116, 0, 4, 7, 0, 0, 0, 0, 0, 0, 0, 228, 184, 150, 231, 149, 140,
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 3, 5, 0, 0, 0, 65, 0,
    0, 0, 128, 0, 0, 0, 85, 128, 128, 0, 94, 0, 0, 1, 30, 0, 128, 0, 1, 0, 0, 0, 4, 9, 0, 0, 0, 0,
    0, 0, 0, 228, 189, 160, 229, 165, 189, 44, 32, 0, 0, 0, 0, 0, 5, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0,
    0, 2, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 110, 97, 109, 101,
    0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 5, 0, 0, 0, 5, 0, 0,
    0, 5, 0, 0, 0, 5, 0, 0, 0, 5, 0, 0, 0, 5, 0, 0, 0, 5, 0, 0, 0, 2, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0,
    0, 103, 114, 101, 101, 116, 0, 1, 0, 0, 0, 8, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 114, 97, 119, 0,
    2, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0,
];

const GBK_LUA51: &[u8] = &[
    27, 76, 117, 97, 81, 0, 1, 4, 8, 4, 8, 0, 9, 0, 0, 0, 0, 0, 0, 0, 64, 103, 98, 107, 46, 108,
    117, 97, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 3, 0, 0, 0, 1, 0, 0, 0, 30, 0, 0, 1, 30, 0,
    128, 0, 1, 0, 0, 0, 4, 17, 0, 0, 0, 0, 0, 0, 0, 196, 227, 186, 195, 202, 192, 189, 231, 178,
    226, 202, 212, 206, 196, 177, 190, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0,
];

static COUNTER: AtomicUsize = AtomicUsize::new(0);

struct TempDir(PathBuf);

impl TempDir {
    fn new(tag: &str) -> Self {
        let id = COUNTER.fetch_add(1, Ordering::Relaxed);
        let dir = std::env::temp_dir().join(format!(
            "unluac-cli-test-{tag}-{}-{id}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).expect("create temp test dir");
        Self(dir)
    }

    fn path(&self) -> &Path {
        &self.0
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn cli() -> Command {
    Command::new(env!("CARGO_BIN_EXE_unluac-cli"))
}

#[test]
fn positional_input_presets_and_bare_bool_flags_work() {
    let dir = TempDir::new("positional");
    let input = dir.path().join("sample.luac");
    fs::write(&input, SAMPLE_LUA51).unwrap();

    // Positional input + bare boolean flag `--readable-strings` (trailing & before `-i`)
    let out = cli()
        .args([input.to_str().unwrap(), "--readable-strings"])
        .output()
        .unwrap();
    assert!(out.status.success(), "stderr: {}", String::from_utf8_lossy(&out.stderr));
    let stdout = String::from_utf8(out.stdout).unwrap();
    assert!(stdout.contains("function greet(name)"), "stdout:\n{stdout}");
    assert!(stdout.contains("你好, "), "stdout:\n{stdout}");

    let bare_before_flag = cli()
        .args(["--readable-strings", "-i", input.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(
        bare_before_flag.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&bare_before_flag.stderr)
    );

    // Explicit `--readable-strings false` preserves raw non-UTF-8 (GBK) bytes as escapes
    let gbk_input = dir.path().join("gbk.luac");
    fs::write(&gbk_input, GBK_LUA51).unwrap();
    let gbk_readable = cli()
        .args([gbk_input.to_str().unwrap(), "--readable-strings"])
        .output()
        .unwrap();
    assert!(gbk_readable.status.success());
    assert!(
        String::from_utf8(gbk_readable.stdout)
            .unwrap()
            .contains("你好世界测试文本")
    );
    let raw_out = cli()
        .args(["--readable-strings", "false", gbk_input.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(
        raw_out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&raw_out.stderr)
    );
    let raw_stdout = String::from_utf8(raw_out.stdout).unwrap();
    assert!(!raw_stdout.contains("你好"), "raw GBK bytes should be escaped:\n{raw_stdout}");
    assert!(raw_stdout.contains("\\196\\227"), "expected raw GBK escapes:\n{raw_stdout}");

    // `--preset ai` uses minimal comments (`-- lines=...`), `--preset exact` uses full (`proto#...`)
    let ai_out = cli()
        .args(["--preset", "ai", input.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(ai_out.status.success(), "stderr: {}", String::from_utf8_lossy(&ai_out.stderr));
    let ai_stdout = String::from_utf8(ai_out.stdout).unwrap();
    assert!(ai_stdout.contains("-- lines="), "expected AI minimal line comments:\n{ai_stdout}");

    // `--preset exact` succeeds cleanly on valid bytecode and emits full proto comments
    let exact_out = cli()
        .args(["--preset", "exact", input.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(
        exact_out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&exact_out.stderr)
    );
    let exact_stdout = String::from_utf8(exact_out.stdout).unwrap();
    assert!(exact_stdout.contains("proto#"), "expected exact full comments:\n{exact_stdout}");
}

#[test]
fn list_protos_supports_output_file_and_json_and_proto_extract() {
    let dir = TempDir::new("protos");
    let input = dir.path().join("sample.luac");
    let index_json = dir.path().join("protos.json");
    fs::write(&input, SAMPLE_LUA51).unwrap();

    let out = cli()
        .args([
            "--list-protos",
            "--format",
            "json",
            "-o",
            index_json.to_str().unwrap(),
            input.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(out.status.success(), "stderr: {}", String::from_utf8_lossy(&out.stderr));
    let json = fs::read_to_string(&index_json).unwrap();
    assert!(json.contains("\"dialect\": \"lua5.1\""), "json:\n{json}");
    assert!(json.contains("\"id\": 0"), "json:\n{json}");
    assert!(json.contains("\"id\": 1"), "json:\n{json}");

    // Normal decompile `--format json` includes protoCount & failedProtos
    let decompile_json = cli()
        .args(["--format", "json", input.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(
        decompile_json.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&decompile_json.stderr)
    );
    let dj = String::from_utf8(decompile_json.stdout).unwrap();
    assert!(dj.contains("\"protoCount\": 2"), "decompile json:\n{dj}");
    assert!(dj.contains("\"failedProtos\": []"), "decompile json:\n{dj}");

    let proto_out = cli()
        .args(["--proto", "1", input.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(
        proto_out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&proto_out.stderr)
    );
    let proto_src = String::from_utf8(proto_out.stdout).unwrap();
    assert!(proto_src.contains("proto#1"), "proto#1 header:\n{proto_src}");
    assert!(proto_src.contains("function greet(name)"), "proto#1:\n{proto_src}");
    assert!(proto_src.contains("你好, "), "proto#1:\n{proto_src}");
    assert!(!proto_src.contains("print("), "proto#1 should not include root body:\n{proto_src}");
}

#[test]
fn refuses_single_file_inplace_overwrite_and_prints_source_hint() {
    let dir = TempDir::new("guards");
    let input = dir.path().join("sample.luac");
    fs::write(&input, SAMPLE_LUA51).unwrap();

    let out = cli()
        .args(["-i", input.to_str().unwrap(), "-o", input.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(!out.status.success(), "must refuse overwriting input bytecode");
    assert_eq!(
        fs::read(&input).unwrap(),
        SAMPLE_LUA51,
        "original bytecode must stay intact"
    );

    let plain_lua = dir.path().join("plain.lua");
    fs::write(&plain_lua, "print('hello')\n").unwrap();
    let bad = cli().arg(plain_lua.to_str().unwrap()).output().unwrap();
    assert!(!bad.status.success());
    let stderr = String::from_utf8_lossy(&bad.stderr);
    assert!(
        stderr.contains("-s") || stderr.contains("hint"),
        "expected helpful hint on plain Lua source, got:\n{stderr}"
    );
}

#[test]
fn batch_refuses_inplace_skips_nested_out_and_disambiguates_collisions() {
    let dir = TempDir::new("batch");
    let in_dir = dir.path().join("in");
    let out_dir = in_dir.join("out");
    fs::create_dir_all(&in_dir).unwrap();
    fs::write(in_dir.join("dup.luac"), SAMPLE_LUA51).unwrap();
    fs::write(in_dir.join("dup.lua"), SAMPLE_LUA51).unwrap();
    fs::write(in_dir.join("readme.txt"), b"not lua bytecode at all").unwrap();

    // In-place directory overwrite must fail
    let inplace = cli()
        .args(["-i", in_dir.to_str().unwrap(), "-o", in_dir.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(!inplace.status.success(), "batch in-place must be refused");

    // Nested output directory + collision disambiguation + non-bytecode skip
    let batch = cli()
        .args([in_dir.to_str().unwrap(), "-o", out_dir.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(
        batch.status.success(),
        "batch stderr: {}",
        String::from_utf8_lossy(&batch.stderr)
    );
    assert!(out_dir.join("dup.lua").is_file(), "dup.lua output missing");
    assert!(
        out_dir.join("dup.luac.lua").is_file(),
        "colliding dup.luac should disambiguate to dup.luac.lua"
    );
    assert!(
        !out_dir.join("readme.lua").exists(),
        "non-bytecode readme.txt should be skipped"
    );
}
