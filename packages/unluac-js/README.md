# unluac-js

JavaScript / TypeScript bindings for [unluac-rs](https://github.com/x3zvawq/unluac-rs), powered by WebAssembly. Decompile Lua 5.1–5.5, LuaJIT 2.1, and Luau bytecode in Node.js (`>= 18`) or any modern browser bundler.

## Installation

```bash
npm install unluac-js
```

## Quick Start

### Node.js

The package auto-loads its bundled `.wasm` binary on first call:

```js
import { readFile } from "node:fs/promises";
import { decompile, decompileWithMeta, detectDialect } from "unluac-js";

const bytes = await readFile("./sample.luac");

// 1. Check whether the input is compiled Lua bytecode (null for plain source)
const dialect = await detectDialect(bytes); // e.g. "lua5.1" | "luajit" | "luau" | null

// 2. Decompile straight to a Lua source string
const source = await decompile(bytes, {
  dialect: "auto",
  parse: { stringEncoding: "gbk" },
  generate: { tableStyle: "aligned" },
});

// 3. Decompile with lightweight metadata (dialect, kind, proto count, failed protos)
const meta = await decompileWithMeta(bytes);
console.log(meta.dialect, meta.kind, meta.protoCount, meta.failedProtos);
```

### Browser (Vite / Webpack / Rollup)

Call `init()` once if you want to warm up the WASM module ahead of time. Most modern bundlers resolve the relative `.wasm` asset automatically; if yours needs an explicit URL, pass it to `init(url)`:

```ts
import { decompile, init } from "unluac-js";
import wasmUrl from "unluac-js/unluac_wasm_bg.wasm?url";

await init(wasmUrl);

const source = await decompile(chunkBytes, {
  preset: "readable",
  dialect: "luau",
  generate: {
    luauVectorConstructor: { library: "Vector3", constructor: "new", size: 3 },
  },
});
```

## API

All functions accept `bytes` as `BufferSource` (`Uint8Array`, `ArrayBuffer`, etc.) or `ArrayLike<number>`. Option/decompile failures throw `UnluacError` (an `Error` subclass carrying `.code` and optional `.field`).

| Function | Returns | Use When |
| --- | --- | --- |
| `init(input?)` | `Promise<void>` | Pre-initialize the WASM module or pass a custom WASM URL/buffer. |
| `detectDialect(bytes)` | `Promise<UnluacDialect \| null>` | Check dialect from header bytes (`null` if input is not Lua bytecode; throws `UnluacError` on truncated/corrupt headers). |
| `decompile(bytes, options?)` | `Promise<string>` | You only need the final Lua source text (supports `preset` and `proto`). |
| `decompileWithMeta(bytes, options?)` | `Promise<UnluacDecompileResult>` | You need `source` plus `dialect`, `kind` (`"source"` \| `"diagnostic-pseudocode"`), `protoCount`, and `failedProtos`, without paying for full CFG generation. |
| `decompileRich(bytes, options?)` | `Promise<UnluacRichResult>` | You want `source`, `dialect`, `kind`, `failedProtos`, the full preorder `protos` tree (function names, generated line spans, constants, line ranges, upvalues, children), and per-proto `cfgs`. |
| `supportedOptionValues()` | `Promise<UnluacSupportedOptionValues>` | Inspect all accepted enum strings at runtime (`presets`, `dialects`, `namingModes`, `tableStyles`, `tableAlignCells`, `commentStyles`, etc.). |

> Note: Debug dumps and stage timing reports are omitted from the npm WASM bundle to keep bundle size small. Use `unluac-cli` or the Rust `unluac` crate if you need stage-by-stage dumps.

## Options & Defaults

```ts
interface UnluacDecompileOptions {
  preset?: "readable" | "exact" | "ai";
  proto?: number;
  dialect?: "auto" | "lua5.1" | "lua5.2" | "lua5.3" | "lua5.4" | "lua5.5" | "luajit" | "luau";
  parse?: {
    mode?: "strict" | "permissive";          // default: "permissive"
    stringEncoding?: string;                 // default: "auto" (or "utf-8", "gbk", "shift_jis", ...)
    stringDecodeMode?: "strict" | "lossy";   // default: "strict"
    ignoreDebug?: boolean;                   // default: false
  };
  readability?: {
    returnInlineMaxComplexity?: number;      // default: 10
    indexInlineMaxComplexity?: number;       // default: 10
    argsInlineMaxComplexity?: number;        // default: 6
    accessBaseInlineMaxComplexity?: number;  // default: 5
  };
  naming?: {
    mode?: "heuristic" | "simple" | "debug-like"; // default: "heuristic"
    debugLikeIncludeFunction?: boolean;           // default: true
  };
  generate?: {
    mode?: "strict" | "permissive";               // default: "permissive"
    indentWidth?: number;                         // default: 4
    maxLineLength?: number;                       // default: 100
    numberFormat?: "decimal" | "hex";             // default: "decimal"
    quoteStyle?: "prefer-double" | "prefer-single" | "min-escape"; // default: "min-escape"
    readableStrings?: boolean;                    // default: true
    tableStyle?: "compact" | "balanced" | "aligned" | "expanded";  // default: "balanced"
    tableAlignWidth?: number;                     // default: maxLineLength
    tableAlignStringWidth?: number;               // default: 16
    tableAlignEq?: boolean;                       // default: true
    tableAlignEqMaxSpaces?: number;               // default: 8
    tableAlignCells?: "auto" | "left" | "right";  // default: "auto"
    tableDropIndexKeys?: boolean;                 // default: false
    luauVectorConstructor?: {
      library?: string | null;
      constructor: string;
      size: 3 | 4;
    };
    comment?: boolean | "none" | "minimal" | "full"; // default: "minimal" (true -> "full", false -> "none")
  };
}
```

## Local Development

```bash
npm run build   # Compiles packages/unluac-wasm via wasm-pack and bundles ESM/CJS/DTS
npm test        # Runs ESM + CJS smoke tests against Lua 5.4 bytecode
```

## Related Links

- Repository: [x3zvawq/unluac-rs](https://github.com/x3zvawq/unluac-rs)
- Rust crate: [unluac on crates.io](https://crates.io/crates/unluac)
- CLI binaries: [GitHub Releases](https://github.com/x3zvawq/unluac-rs/releases)
