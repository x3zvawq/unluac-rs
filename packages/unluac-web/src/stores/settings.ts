/**
 * 反编译参数设置 store。
 *
 * 集中管理所有反编译选项的状态，持久化到 localStorage。
 * 各组件通过此 store 读取/更新参数，避免 prop drilling。
 */

import { defineStore } from 'pinia'
import { reactive, watch } from 'vue'
import type { DecompileOptions } from '@/types/decompiler'

const STORAGE_KEY = 'unluac-settings'

export function defaultOptions(): DecompileOptions {
  return {
    dialect: 'lua5.1',
    parse: {
      mode: 'permissive',
      stringEncoding: 'utf-8',
      stringDecodeMode: 'strict',
    },
    readability: {
      returnInlineMaxComplexity: 10,
      indexInlineMaxComplexity: 10,
      argsInlineMaxComplexity: 6,
      accessBaseInlineMaxComplexity: 5,
    },
    naming: {
      mode: 'debug-like',
      debugLikeIncludeFunction: true,
    },
    generate: {
      mode: 'permissive',
      indentWidth: 4,
      maxLineLength: 100,
      quoteStyle: 'min-escape',
      tableStyle: 'balanced',
      conservativeOutput: true,
      comment: true,
    },
  }
}

function loadPersistedOptions(): DecompileOptions {
  try {
    const raw = localStorage.getItem(STORAGE_KEY)
    if (raw) {
      const parsed = JSON.parse(raw)
      // 用默认值兜底缺失字段（版本升级时新增字段不会丢失默认值）
      const defaults = defaultOptions()
      return {
        dialect: parsed.dialect ?? defaults.dialect,
        parse: { ...defaults.parse, ...parsed.parse },
        readability: { ...defaults.readability, ...parsed.readability },
        naming: { ...defaults.naming, ...parsed.naming },
        generate: { ...defaults.generate, ...parsed.generate },
      }
    }
  } catch {
    // localStorage 损坏或不可用时回退默认值
  }
  return defaultOptions()
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

  function resetToDefaults() {
    const defaults = defaultOptions()
    Object.assign(options, defaults)
  }

  return {
    options,
    resetToDefaults,
  }
})
