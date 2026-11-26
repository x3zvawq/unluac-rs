/**
 * 反编译参数设置 store。
 *
 * 集中管理所有反编译选项的状态，持久化到 localStorage。
 * 所有来自 localStorage 或分享 URL 的外部数据都通过 sanitizeOptions 白名单校验，
 * 防止原型污染与非法枚举/越界参数进入 WASM 边界。
 */

import { defineStore } from 'pinia'
import { computed, reactive, watch } from 'vue'
import type {
  DecompileOptions,
  LuauVectorConstructor,
  SettingsPresetId,
  UnluacCommentStyle,
  UnluacDialect,
  UnluacGenerateMode,
  UnluacNamingMode,
  UnluacNumberFormat,
  UnluacParseMode,
  UnluacQuoteStyle,
  UnluacStringDecodeMode,
  UnluacStringEncoding,
  UnluacTableCellAlign,
  UnluacTableStyle,
} from '@/types/decompiler'

const STORAGE_KEY = 'unluac-settings'

const VALID_DIALECTS = new Set<UnluacDialect>([
  'auto',
  'lua5.1',
  'lua5.2',
  'lua5.3',
  'lua5.4',
  'lua5.5',
  'luajit',
  'luau',
])
const VALID_PARSE_MODES = new Set<UnluacParseMode>(['strict', 'permissive'])
const VALID_ENCODINGS = new Set<UnluacStringEncoding>([
  'auto',
  'utf-8',
  'gbk',
  'gb18030',
  'big5',
  'shift_jis',
  'euc-jp',
  'euc-kr',
  'windows-1252',
  'windows-1251',
  'koi8-r',
  'windows-874',
])
const VALID_DECODE_MODES = new Set<UnluacStringDecodeMode>(['strict', 'lossy'])
const VALID_NAMING_MODES = new Set<UnluacNamingMode>(['debug-like', 'simple', 'heuristic'])
const VALID_GENERATE_MODES = new Set<UnluacGenerateMode>(['strict', 'permissive'])
const VALID_NUMBER_FORMATS = new Set<UnluacNumberFormat>(['decimal', 'hex'])
const VALID_QUOTE_STYLES = new Set<UnluacQuoteStyle>([
  'prefer-double',
  'prefer-single',
  'min-escape',
])
const VALID_TABLE_STYLES = new Set<UnluacTableStyle>(['compact', 'balanced', 'aligned', 'expanded'])
const VALID_TABLE_ALIGN_CELLS = new Set<UnluacTableCellAlign>(['auto', 'left', 'right'])

export function defaultOptions(): DecompileOptions {
  return {
    dialect: 'auto',
    parse: {
      mode: 'permissive',
      stringEncoding: 'auto',
      stringDecodeMode: 'strict',
      ignoreDebug: false,
    },
    readability: {
      returnInlineMaxComplexity: 10,
      indexInlineMaxComplexity: 10,
      argsInlineMaxComplexity: 6,
      accessBaseInlineMaxComplexity: 5,
    },
    naming: {
      mode: 'heuristic',
      debugLikeIncludeFunction: true,
    },
    generate: {
      mode: 'permissive',
      indentWidth: 4,
      maxLineLength: 100,
      numberFormat: 'decimal',
      quoteStyle: 'min-escape',
      readableStrings: true,
      tableStyle: 'balanced',
      tableAlignWidth: null,
      tableAlignStringWidth: 16,
      tableAlignEq: true,
      tableAlignEqMaxSpaces: 8,
      tableAlignCells: 'auto',
      tableDropIndexKeys: false,
      luauVectorConstructor: null,
      comment: 'minimal',
    },
  }
}

export function normalizeCommentStyle(
  value: unknown,
  fallback: UnluacCommentStyle,
): UnluacCommentStyle {
  if (value === true) return 'full'
  if (value === false) return 'none'
  if (value === 'none' || value === 'minimal' || value === 'full') return value
  return fallback
}

function asRecord(value: unknown): Record<string, unknown> | null {
  return value !== null && typeof value === 'object' && !Array.isArray(value)
    ? (value as Record<string, unknown>)
    : null
}

function pickEnum<T extends string>(value: unknown, valid: Set<T>, fallback: T): T {
  return typeof value === 'string' && valid.has(value as T) ? (value as T) : fallback
}

function pickBool(value: unknown, fallback: boolean): boolean {
  return typeof value === 'boolean' ? value : fallback
}

function pickInt(value: unknown, min: number, max: number, fallback: number): number {
  if (typeof value !== 'number' || !Number.isFinite(value)) return fallback
  return Math.min(max, Math.max(min, Math.trunc(value)))
}

function pickNullableInt(
  value: unknown,
  min: number,
  max: number,
  fallback: number | null,
): number | null {
  if (value === null) return null
  if (typeof value !== 'number' || !Number.isFinite(value)) return fallback
  return Math.min(max, Math.max(min, Math.trunc(value)))
}

function pickLuauVector(
  value: unknown,
  fallback: LuauVectorConstructor | null,
): LuauVectorConstructor | null {
  if (value === null) return null
  const rec = asRecord(value)
  if (!rec) return fallback
  const rawCtor: unknown = Object.hasOwn(rec, 'constructor') ? rec.constructor : undefined
  const ctorName = typeof rawCtor === 'string' ? rawCtor.trim() : ''
  if (!ctorName || ctorName.length > 64) return fallback
  const library =
    rec.library === null || rec.library === undefined || rec.library === ''
      ? null
      : typeof rec.library === 'string' && rec.library.trim().length <= 64
        ? rec.library.trim()
        : null
  const size = rec.size === 3 || rec.size === 4 ? rec.size : 3
  return { library, constructor: ctorName, size }
}

/** 从不可信对象（localStorage / URL）按白名单重建合法的 DecompileOptions */
export function sanitizeOptions(
  raw: unknown,
  base: DecompileOptions = defaultOptions(),
): DecompileOptions {
  const root = asRecord(raw)
  if (!root) return base

  const parse = asRecord(root.parse)
  const readability = asRecord(root.readability)
  const naming = asRecord(root.naming)
  const generate = asRecord(root.generate)

  return {
    dialect: pickEnum(root.dialect, VALID_DIALECTS, base.dialect),
    parse: {
      mode: pickEnum(parse?.mode, VALID_PARSE_MODES, base.parse.mode),
      stringEncoding: pickEnum(parse?.stringEncoding, VALID_ENCODINGS, base.parse.stringEncoding),
      stringDecodeMode: pickEnum(
        parse?.stringDecodeMode,
        VALID_DECODE_MODES,
        base.parse.stringDecodeMode,
      ),
      ignoreDebug: pickBool(parse?.ignoreDebug, base.parse.ignoreDebug),
    },
    readability: {
      returnInlineMaxComplexity: pickInt(
        readability?.returnInlineMaxComplexity,
        1,
        50,
        base.readability.returnInlineMaxComplexity,
      ),
      indexInlineMaxComplexity: pickInt(
        readability?.indexInlineMaxComplexity,
        1,
        50,
        base.readability.indexInlineMaxComplexity,
      ),
      argsInlineMaxComplexity: pickInt(
        readability?.argsInlineMaxComplexity,
        1,
        50,
        base.readability.argsInlineMaxComplexity,
      ),
      accessBaseInlineMaxComplexity: pickInt(
        readability?.accessBaseInlineMaxComplexity,
        1,
        50,
        base.readability.accessBaseInlineMaxComplexity,
      ),
    },
    naming: {
      mode: pickEnum(naming?.mode, VALID_NAMING_MODES, base.naming.mode),
      debugLikeIncludeFunction: pickBool(
        naming?.debugLikeIncludeFunction,
        base.naming.debugLikeIncludeFunction,
      ),
    },
    generate: {
      mode: pickEnum(generate?.mode, VALID_GENERATE_MODES, base.generate.mode),
      indentWidth: pickInt(generate?.indentWidth, 1, 8, base.generate.indentWidth),
      maxLineLength: pickInt(generate?.maxLineLength, 40, 200, base.generate.maxLineLength),
      numberFormat: pickEnum(
        generate?.numberFormat,
        VALID_NUMBER_FORMATS,
        base.generate.numberFormat,
      ),
      quoteStyle: pickEnum(generate?.quoteStyle, VALID_QUOTE_STYLES, base.generate.quoteStyle),
      readableStrings: pickBool(generate?.readableStrings, base.generate.readableStrings),
      tableStyle: pickEnum(generate?.tableStyle, VALID_TABLE_STYLES, base.generate.tableStyle),
      tableAlignWidth: pickNullableInt(
        generate?.tableAlignWidth,
        20,
        240,
        base.generate.tableAlignWidth,
      ),
      tableAlignStringWidth: pickInt(
        generate?.tableAlignStringWidth,
        4,
        120,
        base.generate.tableAlignStringWidth,
      ),
      tableAlignEq: pickBool(generate?.tableAlignEq, base.generate.tableAlignEq),
      tableAlignEqMaxSpaces: pickInt(
        generate?.tableAlignEqMaxSpaces,
        0,
        32,
        base.generate.tableAlignEqMaxSpaces,
      ),
      tableAlignCells: pickEnum(
        generate?.tableAlignCells,
        VALID_TABLE_ALIGN_CELLS,
        base.generate.tableAlignCells,
      ),
      tableDropIndexKeys: pickBool(generate?.tableDropIndexKeys, base.generate.tableDropIndexKeys),
      luauVectorConstructor: pickLuauVector(
        generate?.luauVectorConstructor,
        base.generate.luauVectorConstructor,
      ),
      comment: normalizeCommentStyle(generate?.comment, base.generate.comment),
    },
  }
}

function loadPersistedOptions(): DecompileOptions {
  try {
    const raw = localStorage.getItem(STORAGE_KEY)
    if (raw) {
      return sanitizeOptions(JSON.parse(raw))
    }
  } catch {
    // localStorage 损坏或不可用时回退默认值
  }
  return defaultOptions()
}

interface PresetPatch {
  parseMode: DecompileOptions['parse']['mode']
  ignoreDebug: boolean
  namingMode: DecompileOptions['naming']['mode']
  generateMode: DecompileOptions['generate']['mode']
  readableStrings: boolean
  tableStyle: DecompileOptions['generate']['tableStyle']
  tableDropIndexKeys: boolean
  comment: UnluacCommentStyle
}

const PRESET_PATCHES: Record<SettingsPresetId, PresetPatch> = {
  readable: {
    parseMode: 'permissive',
    ignoreDebug: false,
    namingMode: 'heuristic',
    generateMode: 'permissive',
    readableStrings: true,
    tableStyle: 'aligned',
    tableDropIndexKeys: true,
    comment: 'minimal',
  },
  exact: {
    parseMode: 'strict',
    ignoreDebug: false,
    namingMode: 'debug-like',
    generateMode: 'strict',
    readableStrings: false,
    tableStyle: 'balanced',
    tableDropIndexKeys: false,
    comment: 'full',
  },
  ai: {
    parseMode: 'permissive',
    ignoreDebug: false,
    namingMode: 'heuristic',
    generateMode: 'permissive',
    readableStrings: true,
    tableStyle: 'compact',
    tableDropIndexKeys: true,
    comment: 'minimal',
  },
}

function matchesPreset(options: DecompileOptions, patch: PresetPatch): boolean {
  return (
    options.parse.mode === patch.parseMode &&
    options.parse.ignoreDebug === patch.ignoreDebug &&
    options.naming.mode === patch.namingMode &&
    options.generate.mode === patch.generateMode &&
    options.generate.readableStrings === patch.readableStrings &&
    options.generate.tableStyle === patch.tableStyle &&
    options.generate.tableDropIndexKeys === patch.tableDropIndexKeys &&
    options.generate.comment === patch.comment
  )
}

export const useSettingsStore = defineStore('settings', () => {
  const options = reactive(loadPersistedOptions())

  watch(
    () => ({ ...options }),
    (val) => {
      try {
        localStorage.setItem(STORAGE_KEY, JSON.stringify(val))
      } catch {
        // quota exceeded 等情况静默忽略
      }
    },
    { deep: true },
  )

  const activePreset = computed<SettingsPresetId | null>(() => {
    for (const [id, patch] of Object.entries(PRESET_PATCHES) as [SettingsPresetId, PresetPatch][]) {
      if (matchesPreset(options, patch)) return id
    }
    return null
  })

  function applyPreset(preset: SettingsPresetId) {
    const patch = PRESET_PATCHES[preset]
    options.parse.mode = patch.parseMode
    options.parse.ignoreDebug = patch.ignoreDebug
    options.naming.mode = patch.namingMode
    options.generate.mode = patch.generateMode
    options.generate.readableStrings = patch.readableStrings
    options.generate.tableStyle = patch.tableStyle
    options.generate.tableDropIndexKeys = patch.tableDropIndexKeys
    options.generate.comment = patch.comment
  }

  function applySanitized(next: DecompileOptions) {
    options.dialect = next.dialect
    Object.assign(options.parse, next.parse)
    Object.assign(options.readability, next.readability)
    Object.assign(options.naming, next.naming)
    Object.assign(options.generate, next.generate)
  }

  function resetToDefaults() {
    applySanitized(defaultOptions())
  }

  return {
    options,
    activePreset,
    applyPreset,
    applySanitized,
    resetToDefaults,
  }
})
