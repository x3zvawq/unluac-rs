export type UnluacDialect =
  | "auto"
  | "lua5.1"
  | "lua5.2"
  | "lua5.3"
  | "lua5.4"
  | "lua5.5"
  | "luajit"
  | "luau";

export type UnluacParseMode = "strict" | "permissive";
export type UnluacStringEncoding =
  | "auto"
  | "utf-8"
  | "GBK"
  | "gb18030"
  | "Big5"
  | "Shift_JIS"
  | "EUC-JP"
  | "EUC-KR"
  | "windows-1252"
  | "windows-1251"
  | "KOI8-R"
  | "windows-874"
  | (string & {});
export type UnluacStringDecodeMode = "strict" | "lossy";
/** Fallback names: numbered, generic roles, or expression/usage hints. All modes prefer debug names. */
export type UnluacNamingMode = "debug-like" | "simple" | "heuristic";
export type UnluacGenerateMode = "strict" | "permissive";
export type UnluacQuoteStyle = "prefer-double" | "prefer-single" | "min-escape";
export type UnluacNumberFormat = "decimal" | "hex";
export type UnluacTableStyle = "compact" | "balanced" | "aligned" | "expanded";
export type UnluacTableCellAlign = "auto" | "left" | "right";
export type UnluacCommentStyle = "none" | "minimal" | "full";

export type UnluacPreset = "readable" | "exact" | "ai";

export interface UnluacLuauVectorConstructor {
  library?: string | null;
  constructor: string;
  size: 3 | 4;
}

export interface UnluacDecompileOptions {
  /** Curated preset applied before explicit option overrides. */
  preset?: UnluacPreset;
  /** Decompile only a single DFS proto id (supported by `decompile` and `decompileWithMeta`). */
  proto?: number;
  dialect?: UnluacDialect;
  parse?: {
    mode?: UnluacParseMode;
    stringEncoding?: UnluacStringEncoding;
    stringDecodeMode?: UnluacStringDecodeMode;
    ignoreDebug?: boolean;
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
    mode?: UnluacGenerateMode;
    indentWidth?: number;
    maxLineLength?: number;
    numberFormat?: UnluacNumberFormat;
    quoteStyle?: UnluacQuoteStyle;
    /** Decode literals to readable UTF-8 (default true); false preserves original bytes. */
    readableStrings?: boolean;
    tableStyle?: UnluacTableStyle;
    /** Max rendered row width (including indentation) of aligned table grids. */
    tableAlignWidth?: number | null;
    /** Max rendered width of string literals allowed inside aligned table grids. */
    tableAlignStringWidth?: number;
    /** Align record keys by `=` in non-single-line aligned tables (default true). */
    tableAlignEq?: boolean;
    /** Max padding spaces when aligning record keys by `=` (default 8). */
    tableAlignEqMaxSpaces?: number;
    /** Horizontal alignment of aligned table grid cells (default "auto"). */
    tableAlignCells?: UnluacTableCellAlign;
    /** Omit contiguous `[1]..[n]` keys in safe PUC scalar constructors (default false). */
    tableDropIndexKeys?: boolean;
    luauVectorConstructor?: UnluacLuauVectorConstructor;
    /** Comment verbosity: "minimal" (default), "full", "none", or boolean alias (true=full, false=none). */
    comment?: boolean | UnluacCommentStyle;
  };
}

export interface UnluacDecompileResult {
  /** Generated Lua source or diagnostic pseudocode. */
  source: string;
  /** Resolved dialect (e.g. "lua5.1", "luajit", "luau"). */
  dialect: Exclude<UnluacDialect, "auto">;
  /** Whether the output is valid target source or permissive diagnostic pseudocode. */
  kind: "source" | "diagnostic-pseudocode";
  /** Total number of protos in the chunk. */
  protoCount: number;
  /** DFS proto ids that fell back to error placeholders in permissive mode. */
  failedProtos: number[];
}

export interface UnluacSupportedOptionValues {
  presets: UnluacPreset[];
  dialects: UnluacDialect[];
  parseModes: UnluacParseMode[];
  stringEncodings: UnluacStringEncoding[];
  stringDecodeModes: UnluacStringDecodeMode[];
  namingModes: UnluacNamingMode[];
  generateModes: UnluacGenerateMode[];
  quoteStyles: UnluacQuoteStyle[];
  numberFormats: UnluacNumberFormat[];
  tableStyles: UnluacTableStyle[];
  tableAlignCells: UnluacTableCellAlign[];
  commentStyles: UnluacCommentStyle[];
}

// ── 结构化反编译结果（decompileRich 返回） ──

export type UnluacBlockKind = "normal" | "synthetic-exit";
export type UnluacEdgeKind =
  | "fallthrough"
  | "jump"
  | "branch-true"
  | "branch-false"
  | "loop-body"
  | "loop-exit"
  | "return"
  | "tail-call";

export interface UnluacRichResult {
  /** 反编译生成的源码或诊断伪源码 */
  source: string;
  /** 识别到的方言 */
  dialect: Exclude<UnluacDialect, "auto">;
  /** 可重编译源码或带 Error 标记的诊断伪源码 */
  kind: "source" | "diagnostic-pseudocode";
  /** 宽容模式下产生错误占位符的 proto ID 列表 */
  failedProtos: number[];
  /** 完整 proto 树的先序数组，ID 等于索引，根为 0 */
  protos: UnluacProtoMeta[];
  /** 每个 proto 的 CFG（与 protos 平行数组） */
  cfgs: UnluacProtoCfg[];
}

export interface UnluacProtoMeta {
  /** 先序数组索引（0 = 主 proto） */
  id: number;
  /** 函数声明名或 Luau debug 名（根 proto 为源文件名） */
  name: string | null;
  lineStart: number;
  lineEnd: number;
  /** 该 proto 在生成源码中的 1-based 起始行 */
  generatedLineStart: number | null;
  /** 该 proto 在生成源码中的 1-based 结束行 */
  generatedLineEnd: number | null;
  numParams: number;
  isVararg: boolean;
  numUpvalues: number;
  numConstants: number;
  numInstructions: number;
  /** 常量池字面量列表 */
  constants: UnluacConstant[];
  /** 子 proto 的 DFS ID 列表 */
  children: number[];
}

export interface UnluacConstant {
  /** 常量在池中的索引（0-based） */
  index: number;
  /** 类型标签 */
  type:
    | "nil"
    | "boolean"
    | "integer"
    | "number"
    | "string"
    | "int64"
    | "uint64"
    | "complex"
    | "vector";
  /** 人类可读的值表示 */
  display: string;
}

export interface UnluacProtoCfg {
  protoId: number;
  blocks: UnluacCfgBlock[];
  edges: UnluacCfgEdge[];
  entryBlock: number;
  exitBlock: number;
  /** 拓扑序 block ID 列表 */
  blockOrder: number[];
}

export interface UnluacCfgBlock {
  id: number;
  kind: UnluacBlockKind;
  /** 人类可读的 Low-IR 指令行 */
  instructions: string[];
  /** 对应的原始字节码指令行（通过 LoweringMap 映射） */
  rawInstructions: string[];
}

export interface UnluacCfgEdge {
  from: number;
  to: number;
  kind: UnluacEdgeKind;
}

type UnluacBytes = BufferSource | ArrayLike<number>;
type UnluacInitInput = RequestInfo | URL | Response | BufferSource | WebAssembly.Module;
type WasmInitArgument =
  | { module_or_path: UnluacInitInput | Promise<UnluacInitInput> }
  | UnluacInitInput
  | Promise<UnluacInitInput>;

interface WasmBindings {
  default(input?: WasmInitArgument): Promise<unknown>;
  detectDialect(bytes: Uint8Array): Exclude<UnluacDialect, "auto"> | null;
  decompile(bytes: Uint8Array, options: UnluacDecompileOptions): string;
  decompileWithMeta(bytes: Uint8Array, options: UnluacDecompileOptions): UnluacDecompileResult;
  decompileRich(bytes: Uint8Array, options: UnluacDecompileOptions): UnluacRichResult;
  supportedOptionValues(): UnluacSupportedOptionValues;
}

/** Structured error thrown by `unluac-js` when option validation, dialect detection, or decompilation fails. */
export class UnluacError extends Error {
  readonly code: string;
  readonly field?: string;

  constructor(code: string, message: string, field?: string) {
    super(message);
    this.name = "UnluacError";
    this.code = code;
    if (field !== undefined) {
      this.field = field;
    }
  }
}

function wrapBridgeError(error: unknown): never {
  if (error instanceof UnluacError) {
    throw error;
  }
  if (error && typeof error === "object" && "code" in error && "message" in error) {
    const bridge = error as { code: unknown; message: unknown; field?: unknown };
    throw new UnluacError(
      String(bridge.code),
      String(bridge.message),
      typeof bridge.field === "string" ? bridge.field : undefined
    );
  }
  if (error instanceof Error) {
    throw error;
  }
  throw new UnluacError("unknown-error", String(error));
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
    bindingsPromise = (import(WASM_GLUE_SPECIFIER) as Promise<WasmBindings>).catch((error) => {
      bindingsPromise = null;
      throw error;
    });
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
    })().catch((error) => {
      initPromise = null;
      throw error;
    });
  }

  await initPromise;
}

export async function decompile(
  bytes: UnluacBytes,
  options: UnluacDecompileOptions = {}
): Promise<string> {
  await init();
  const bindings = await loadBindings();
  try {
    return bindings.decompile(toUint8Array(bytes), options);
  } catch (error) {
    wrapBridgeError(error);
  }
}

/** Lightweight structured decompilation returning source, resolved dialect, kind, and failed proto ids without heavy CFG serialization. */
export async function decompileWithMeta(
  bytes: UnluacBytes,
  options: UnluacDecompileOptions = {}
): Promise<UnluacDecompileResult> {
  await init();
  const bindings = await loadBindings();
  try {
    return bindings.decompileWithMeta(toUint8Array(bytes), options);
  } catch (error) {
    wrapBridgeError(error);
  }
}

/** Detect bytecode with the core parser; null means ordinary source input. */
export async function detectDialect(
  bytes: UnluacBytes
): Promise<Exclude<UnluacDialect, "auto"> | null> {
  await init();
  const bindings = await loadBindings();
  try {
    return bindings.detectDialect(toUint8Array(bytes));
  } catch (error) {
    wrapBridgeError(error);
  }
}

export async function decompileRich(
  bytes: UnluacBytes,
  options: UnluacDecompileOptions = {}
): Promise<UnluacRichResult> {
  await init();
  const bindings = await loadBindings();
  try {
    return bindings.decompileRich(toUint8Array(bytes), options);
  } catch (error) {
    wrapBridgeError(error);
  }
}

export async function supportedOptionValues(): Promise<UnluacSupportedOptionValues> {
  await init();
  const bindings = await loadBindings();
  return bindings.supportedOptionValues();
}
