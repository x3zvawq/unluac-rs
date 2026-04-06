# unluac-rs

[简体中文](./README.md) | English

> This repository is still in a testing phase, and its behavior, APIs, and output details may continue to evolve. Bug reports, problematic test cases, incompatibility findings, usage feedback, and release-related suggestions are all very welcome.

## Introduction

A Lua decompiler written in Rust with support for multiple dialects. The repository currently supports the following Lua versions and dialects:

- [Lua 5.1](https://www.lua.org/versions.html#5.1)
- [Lua 5.2](https://www.lua.org/versions.html#5.2)
- [Lua 5.3](https://www.lua.org/versions.html#5.3)
- [Lua 5.4](https://www.lua.org/versions.html#5.4)
- [Lua 5.5](https://www.lua.org/versions.html#5.5)
- [LuaJIT 2.1](https://luajit.org/)
- [Luau](https://luau.org/)

It uses techniques such as control-flow analysis and dominator-tree analysis to eliminate most intermediate variables. For the cases currently tracked in this repository, it can usually reconstruct source code with a close-to-original shape.

The repository is currently organized roughly like this:

- Root package `unluac`: core decompiler library
- `packages/unluac-cli`: command-line entry point
- `packages/unluac-wasm`: wasm bindings
- `packages/unluac-js`: npm wrapper package
- `xtask`: test orchestration and Lua toolchain helpers

## Usage

The repository is currently organized around these integration and distribution paths:

1. **CLI**: inside this repository, the fastest way to debug is `cargo unluac`; future GitHub Release binaries will be produced from the same CLI package.
2. **Rust library**: integrate the core crate `unluac` into a Rust project and call the decompilation pipeline directly.
3. **npm package**: the repository ships `packages/unluac-js` as the npm-facing wrapper for Node.js and browser-based JavaScript environments.
4. **WebAssembly**: the repository ships `packages/unluac-wasm` as the wasm binding layer for additional language or runtime wrappers.

### CLI

The most direct CLI entry point inside this repository is:

```bash
cargo unluac -- --input /absolute/path/to/chunk.out --dialect=lua5.1
cargo unluac -- --source tests/lua_cases/lua5.1/01_setfenv.lua --dialect=lua5.1
```

Equivalent command:

```bash
cargo run -p unluac-cli -- --input /absolute/path/to/chunk.out --dialect=lua5.1
```

Notes:

- The CLI currently requires you to pass either `--input` or `--source`
- When `--source` is provided, the CLI first invokes an external compiler to produce a chunk, then decompiles that generated chunk
- The standalone `unluac-cli` binaries published on GitHub Release do not bundle a Lua compiler; `--source` only works when you pass `--luac` explicitly, or when a compatible compiler is available under `lua/build/<dialect>/` or on PATH
- The CLI prints plain generated source by default and does not emit debug dumps
- The default dialect / parse / readability / naming / generate values still share the same repo debug preset used by [examples/debug.rs](./examples/debug.rs)
- If you want repo-debug-style dump output, explicitly add `--debug`

| Argument | Description | Default |
| - | - | - |
| `--input` | Path to a compiled chunk | None |
| `--source` | Path to Lua source; the CLI invokes an external compiler before decompiling | None |
| `--luac` | Explicit compiler path used by `--source` | First tries `lua/build/<dialect>/`, otherwise falls back to a compatible compiler on PATH |
| `--dialect` | Dialect used for compilation / decompilation | `lua5.1` |
| `--stop-after` | Last pipeline stage to run | `generate` |
| `--debug` | Enable debug dumps | `false` |
| `--detail` | Debug output detail level | `verbose` when debug is enabled |
| `--color` | Debug color mode | `always` when debug is enabled |
| `--timing` | Print timing report | `false` |
| `--parse-mode` | Strict vs permissive parser mode | `permissive` |
| `--encoding` | String decoding encoding | `utf-8` |
| `--decode-mode` | String decode failure strategy | `strict` |
| `--naming-mode` | Naming strategy | `debug-like` |

For more debugging examples and flags, see [docs/debug.md](./docs/debug.md).

### Rust Library

The current core crate name is `unluac`.

If you want to integrate it from a local checkout or another Rust project, the most reliable setup right now is a `path` or `git` dependency:

```toml
[dependencies]
unluac = { git = "https://github.com/X3ZvaWQ/unluac-rs" }
```

Minimal example:

```rust
use std::fs;

use unluac::decompile::{decompile, DecompileDialect, DecompileOptions, DecompileStage};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let bytes = fs::read("sample.out")?;

    let result = decompile(
        &bytes,
        DecompileOptions {
            dialect: DecompileDialect::Lua51,
            target_stage: DecompileStage::Generate,
            ..DecompileOptions::default()
        },
    )?;

    if let Some(generated) = result.state.generated.as_ref() {
        println!("{}", generated.source);
    }

    Ok(())
}
```

A few things to keep in mind:

- The library API accepts bytes of an already compiled chunk and does not compile Lua source for you
- If all you have is Lua source, the CLI is usually the more convenient entry point right now
- The main decompiler entry points are re-exported from [src/decompile/mod.rs](./src/decompile/mod.rs)

### npm Package

The npm wrapper lives at [packages/unluac-js](./packages/unluac-js).

It is currently a thin TypeScript wrapper that consumes the wasm bindings produced by `packages/unluac-wasm` and narrows the publishable contents to `dist/`.

The published npm wasm build trims out `debug` / `timing` support to keep the package smaller. The CLI and in-repo Rust APIs still keep the full debugging surface.
The npm-facing `decompile()` API also returns the final source string directly instead of exposing intermediate pipeline metadata.

Local build:

```bash
cd packages/unluac-js
npm install
npm run build
```

After the build completes, the publish directory is:

```text
packages/unluac-js/dist
```

The main public APIs are:

- `init(input?)`
- `decompile(bytes, options?)`
- `supportedOptionValues()`

Minimal Node.js example:

```js
import { decompile } from "unluac-js";
import { readFile } from "node:fs/promises";

const chunkBytes = await readFile("./sample.luac");
const source = await decompile(chunkBytes, {
  dialect: "lua5.1",
});

console.log(source);
```

For browser usage and more complete examples, see [packages/unluac-js/README.md](./packages/unluac-js/README.md).

### WebAssembly

The wasm binding layer lives at [packages/unluac-wasm](./packages/unluac-wasm).

It currently uses `wasm-bindgen` and `serde-wasm-bindgen` to expose a JS-friendly object protocol instead of leaking Rust internal layouts across the boundary.

If you only want to use this project from JavaScript or TypeScript, the npm wrapper above is the recommended entry point.  
If you need to integrate the wasm layer into another language or runtime, you can:

- Take the built `unluac_wasm.js` and `unluac_wasm_bg.wasm` files from the published npm package
- Or build `packages/unluac-wasm` directly in this repository and prepare language-specific bindings yourself

If you plan to extend the wasm support to a specific language or runtime, PRs are welcome.

## Contributing and Feedback

Contributions of all kinds are welcome, including code, documentation, test cases, and other improvements.
If you run into issues while using the project, or have ideas and suggestions, feel free to open an issue. If the project performs poorly on a specific case, attaching the corresponding binary file is also very helpful for diagnosis.

## License MIT

This project is released under the MIT License. See [LICENSE.txt](./LICENSE.txt) for details.

## Acknowledgements

- [metaworms's lua decompiler](https://luadec.metaworm.site) - This project's design and implementation were inspired by it, and the author's tutorial was also very helpful. The website is no longer accessible today.
- Codex + GPT-5.4 - Most of this project's code was generated with Codex and GPT-5.4. Thanks to OpenAI for building such strong tools.
