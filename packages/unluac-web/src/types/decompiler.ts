/**
 * 反编译器相关的前端类型声明。
 *
 * 这些类型镜像 unluac-js 的导出类型，额外增加了前端 UI 层面需要的状态类型。
 * 统一在此处声明，避免各组件重复定义。
 */

export type UnluacDialect = 'lua5.1' | 'lua5.2' | 'lua5.3' | 'lua5.4' | 'lua5.5' | 'luajit' | 'luau'

export type UnluacParseMode = 'strict' | 'permissive'
export type UnluacStringEncoding =
  | 'utf-8'
  | 'gbk'
  | 'gb18030'
  | 'big5'
  | 'shift_jis'
  | 'euc-jp'
  | 'euc-kr'
  | 'windows-1252'
  | 'windows-1251'
  | 'koi8-r'
  | 'windows-874'
export type UnluacStringDecodeMode = 'strict' | 'lossy'
export type UnluacNamingMode = 'debug-like' | 'simple' | 'heuristic'
export type UnluacQuoteStyle = 'prefer-double' | 'prefer-single' | 'min-escape'
export type UnluacTableStyle = 'compact' | 'balanced' | 'expanded'
export type UnluacGenerateMode = 'strict' | 'best-effort' | 'permissive'

export interface DecompileOptions {
  dialect: UnluacDialect
  parse: {
    mode: UnluacParseMode
    stringEncoding: UnluacStringEncoding
    stringDecodeMode: UnluacStringDecodeMode
  }
  readability: {
    returnInlineMaxComplexity: number
    indexInlineMaxComplexity: number
    argsInlineMaxComplexity: number
    accessBaseInlineMaxComplexity: number
  }
  naming: {
    mode: UnluacNamingMode
    debugLikeIncludeFunction: boolean
  }
  generate: {
    mode: UnluacGenerateMode
    indentWidth: number
    maxLineLength: number
    quoteStyle: UnluacQuoteStyle
    tableStyle: UnluacTableStyle
    conservativeOutput: boolean
    comment: boolean
  }
}

/** 文件在反编译流程中的状态 */
export type FileStatus = 'pending' | 'processing' | 'success' | 'error' | 'skipped'

/** 文件列表面板中每个文件的元数据 */
export interface FileEntry {
  /** 唯一标识，用文件路径 + 时间戳生成 */
  id: string
  /** 显示名称 */
  name: string
  /** 文件在文件夹中的相对路径（拖入文件夹时保留目录结构） */
  relativePath: string
  /** 原始二进制数据 */
  bytes: Uint8Array
  /** 文件大小（字节） */
  size: number
  /** 反编译状态 */
  status: FileStatus
  /** 反编译结果（成功时） */
  result?: string
  /** 用户手动编辑后的结果（仅在用户修改后存在） */
  editedResult?: string
  /** 结构化分析结果（按需获取） */
  richResult?: RichDecompileResult
  /** 错误信息（失败时） */
  error?: string
}

/** Worker 发给主线程的消息类型 */
export type WorkerResponse =
  | { type: 'ready' }
  | { type: 'result'; fileId: string; source: string }
  | { type: 'rich-result'; fileId: string; rich: RichDecompileResult }
  | { type: 'error'; fileId: string; message: string }

/** 主线程发给 Worker 的消息类型 */
export type WorkerRequest =
  | {
      type: 'decompile'
      fileId: string
      bytes: Uint8Array
      options: DecompileOptions
    }
  | {
      type: 'decompile-rich'
      fileId: string
      bytes: Uint8Array
      options: DecompileOptions
    }

// ── 结构化反编译结果 ──

export type BlockKind = 'normal' | 'synthetic-exit'
export type EdgeKind =
  | 'fallthrough'
  | 'jump'
  | 'branch-true'
  | 'branch-false'
  | 'loop-body'
  | 'loop-exit'
  | 'return'
  | 'tail-call'

export interface RichDecompileResult {
  source: string
  warnings: string[]
  protos: ProtoMeta[]
  cfgs: ProtoCfg[]
}

export interface ProtoMeta {
  id: number
  name: string | null
  lineStart: number
  lineEnd: number
  numParams: number
  isVararg: boolean
  numUpvalues: number
  numConstants: number
  numInstructions: number
  constants: ProtoConstant[]
  children: number[]
}

export interface ProtoConstant {
  index: number
  type: 'nil' | 'boolean' | 'integer' | 'number' | 'string' | 'int64' | 'uint64' | 'complex'
  display: string
}

export interface ProtoCfg {
  protoId: number
  blocks: CfgBlock[]
  edges: CfgEdge[]
  entryBlock: number
  exitBlock: number
  blockOrder: number[]
}

export interface CfgBlock {
  id: number
  kind: BlockKind
  instructions: string[]
  rawInstructions: string[]
}

export interface CfgEdge {
  from: number
  to: number
  kind: EdgeKind
}
