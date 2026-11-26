---
name: unluac
description: Decompile and inspect compiled Lua bytecode (Lua 5.1–5.5, LuaJIT 2.1, Luau) using `unluac-cli`. Use when the user asks to read, analyze, batch-decompile, search, or reverse-engineer `.luac`, `.out`, compiled `.lua`, or stripped Lua bytecode files.
---

# Decompiling Lua Bytecode with `unluac-cli`

Use `unluac-cli` (or the release binary `unluac` / `cargo unluac` inside the repo) to recover readable Lua source from compiled chunks across Lua 5.1–5.5, LuaJIT 2.1, and Luau. Dialect detection is automatic (`-D auto` by default), so you normally do not need to guess the Lua version.

## 1. Quick Commands

```bash
# Single file -> stdout (best token efficiency for AI analysis)
unluac-cli sample.luac --preset ai

# Single file -> output file (readable tables & aligned columns for human review)
unluac-cli sample.luac -o recovered.lua --preset readable

# Recursively decompile an entire directory in parallel (auto-skips non-bytecode files)
unluac-cli ./scripts_bin -o ./scripts_src -j 8 --preset ai

# Read from stdin
cat sample.luac | unluac-cli - --preset ai
```

### Presets

| Preset | Best for | Key behavior |
| --- | --- | --- |
| `--preset ai` | Feeding code to an LLM / agent | Heuristic names, minimal comments, compact tables, drops sequential `[1]..[n]` keys |
| `--preset readable` | Human reading & config tables | Heuristic names, minimal comments, aligned table grids/columns, drops sequential keys |
| `--preset exact` | Byte-accurate diffing / recompilation | Strict mode, numbered `debug-like` names, raw byte strings (`--readable-strings false`), full proto comments |

Explicit flags placed alongside `--preset` always override the preset (for example `--preset ai -e gbk`).

## 2. Handling Large Scripts (Avoid Context Overflow)

Before dumping a multi-thousand-line bytecode file into context, list its functions (protos) with their string constants in JSON, find the proto IDs you care about, and decompile only those functions:

```bash
# 1. Inspect every function (line range, instruction count, and up to 32 unique string constants per proto)
unluac-cli big_script.luac --list-protos --format json

# 2. Decompile only the target function cleanly as Lua source
unluac-cli big_script.luac --proto 17 --preset ai
```

- `--proto <id>` (without `--dump`/`--debug`) outputs clean Lua source for that single function (with nested closures included).
- Combine `--list-protos` or `--proto <id>` with `-o <file>` or `--format json` when scripting.
- Note: `--list-protos --format json` caps `strings` at 32 unique entries per proto for compact indexing; to search every string in a giant function, decompile that proto directly.

## 3. Fixing Garbled CJK / Non-UTF-8 Strings

`auto` encoding detection can misidentify very short non-UTF-8 strings (common in Chinese, Japanese, or Korean game scripts). If you see garbled characters or unexpected `\x..` escapes, specify the source encoding explicitly:

```bash
unluac-cli script.luac -e gbk --preset ai        # Simplified Chinese (legacy games)
unluac-cli script.luac -e big5 --preset ai       # Traditional Chinese
unluac-cli script.luac -e shift_jis --preset ai  # Japanese
unluac-cli script.luac -e euc-kr --preset ai     # Korean
```

To inspect raw binary payloads or byte-length-sensitive protocols without UTF-8 conversion, pass `--readable-strings false`.

## 4. Machine-Readable Output & Exit Codes

Use `--format json` when automating or triaging batches:

```bash
unluac-cli sample.luac --format json
unluac-cli ./scripts_bin -o ./scripts_src --format json
```

Single-file JSON includes `dialect`, `kind` (`"source"` or `"diagnostic-pseudocode"`), `protoId`, `protoCount`, `failedProtos`, and `source`.

Check the process exit code:

- `0` — Clean decompilation (`kind == "source"`).
- `2` — Partial recovery (`kind == "diagnostic-pseudocode"`): one or more protos failed in permissive mode and were emitted as `-- [unluac error]` diagnostic blocks, while all other functions still succeeded. Re-run with `--proto <id>` on the IDs in `failedProtos` if you need to inspect a specific failing function.
- `1` — Hard failure (invalid file, I/O error, unsupported option, or failure under `--generate-mode strict`).

## 5. Interpreting Decompiled Output

- **Heuristic names & `:` methods**: By default (`-n heuristic`), stripped variables get readable guesses (including `function M:foo(...)` when parameter 1 is used as `self`). These are readability hints, not original source names—runtime behavior is identical. Switch to `-n debug-like` when cross-referencing registers or bytecode offsets.
- **Preserved debug info**: If the bytecode contains debug symbols, original local names and line numbers are preferred automatically unless `--ignore-debug` is passed.
- **Directory batch mode**: Non-Lua-bytecode files (plain text `.lua`, textures, JSON, etc.) are automatically skipped by magic bytes rather than failing the batch.
