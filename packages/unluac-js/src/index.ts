export type UnluacDialect =
  | "lua5.1"
  | "lua5.2"
  | "lua5.3"
  | "lua5.4"
  | "lua5.5"
  | "luajit"
  | "luau";

export type UnluacParseMode = "strict" | "permissive";
export type UnluacStringEncoding = "utf-8" | "gbk";
export type UnluacStringDecodeMode = "strict" | "lossy";
export type UnluacNamingMode = "debug-like" | "simple" | "heuristic";
export type UnluacQuoteStyle = "prefer-double" | "prefer-single" | "min-escape";
export type UnluacTableStyle = "compact" | "balanced" | "expanded";

export interface UnluacDecompileOptions {
  dialect?: UnluacDialect;
  parse?: {
    mode?: UnluacParseMode;
    stringEncoding?: UnluacStringEncoding;
    stringDecodeMode?: UnluacStringDecodeMode;
  };
  // The published npm package ships a slim wasm build and rejects debug/timing options.
  debug?: never;
  readability?: {
    returnInlineMaxComplexity?: number;
    indexInlineMaxComplexity?: number;
    argsInlineMaxComplexity?: number;
    accessBaseInlineMaxComplexity?: number;
  };
  naming?: {
    mode?: UnluacNamingMode;
    debugLikeIncludeFunction?: boolean;
  };
  generate?: {
    indentWidth?: number;
    maxLineLength?: number;
    quoteStyle?: UnluacQuoteStyle;
    tableStyle?: UnluacTableStyle;
    conservativeOutput?: boolean;
    comment?: boolean;
  };
}

export interface UnluacSupportedOptionValues {
  dialects: UnluacDialect[];
  parseModes: UnluacParseMode[];
  stringEncodings: UnluacStringEncoding[];
  stringDecodeModes: UnluacStringDecodeMode[];
  namingModes: UnluacNamingMode[];
  quoteStyles: UnluacQuoteStyle[];
  tableStyles: UnluacTableStyle[];
}

type UnluacBytes = BufferSource | ArrayLike<number>;
type UnluacInitInput = RequestInfo | URL | Response | BufferSource | WebAssembly.Module;
type WasmInitArgument =
  | { module_or_path: UnluacInitInput | Promise<UnluacInitInput> }
  | UnluacInitInput
  | Promise<UnluacInitInput>;

interface WasmBindings {
  default(input?: WasmInitArgument): Promise<unknown>;
  decompile(bytes: Uint8Array, options: UnluacDecompileOptions): string;
  supportedOptionValues(): UnluacSupportedOptionValues;
}

const WASM_GLUE_SPECIFIER = "./unluac_wasm.js";

let bindingsPromise: Promise<WasmBindings> | null = null;
let initPromise: Promise<void> | null = null;

function isNodeRuntime(): boolean {
  return typeof process !== "undefined" && typeof process.versions?.node === "string";
}

function toUint8Array(bytes: UnluacBytes): Uint8Array {
  if (bytes instanceof Uint8Array) {
    return bytes;
  }
  if (bytes instanceof ArrayBuffer) {
    return new Uint8Array(bytes);
  }
  if (ArrayBuffer.isView(bytes)) {
    return new Uint8Array(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  }
  return Uint8Array.from(bytes);
}

async function loadBindings(): Promise<WasmBindings> {
  if (!bindingsPromise) {
    bindingsPromise = import(WASM_GLUE_SPECIFIER) as Promise<WasmBindings>;
  }
  return bindingsPromise;
}

async function defaultInitInput(): Promise<UnluacInitInput | undefined> {
  if (!isNodeRuntime()) {
    return undefined;
  }

  const [{ readFile }, { dirname, resolve }, { fileURLToPath, pathToFileURL }] =
    await Promise.all([
      import("node:fs/promises"),
      import("node:path"),
      import("node:url"),
    ]);

  const moduleUrl =
    typeof __filename === "string" ? pathToFileURL(__filename) : new URL(import.meta.url);
  const wasmPath = resolve(dirname(fileURLToPath(moduleUrl)), "unluac_wasm_bg.wasm");
  return readFile(wasmPath);
}

export async function init(input?: UnluacInitInput | Promise<UnluacInitInput>): Promise<void> {
  if (!initPromise) {
    initPromise = (async () => {
      const bindings = await loadBindings();
      const resolvedInput = input ?? (await defaultInitInput());
      if (resolvedInput === undefined) {
        await bindings.default();
        return;
      }
      await bindings.default({ module_or_path: await resolvedInput });
    })();
  }

  await initPromise;
}

export async function decompile(
  bytes: UnluacBytes,
  options: UnluacDecompileOptions = {}
): Promise<string> {
  await init();
  const bindings = await loadBindings();
  return bindings.decompile(toUint8Array(bytes), options);
}

export async function supportedOptionValues(): Promise<UnluacSupportedOptionValues> {
  await init();
  const bindings = await loadBindings();
  return bindings.supportedOptionValues();
}
