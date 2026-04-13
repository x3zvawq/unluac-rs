/**
 * URL 参数分享 composable。
 *
 * 将当前反编译选项编码到 URL search params 中，便于分享。
 * 页面加载时如果 URL 中有参数则自动恢复，覆盖 localStorage 的值。
 *
 * 编码策略：使用扁平化的 key 格式（如 `parse.mode`），
 * 只编码与默认值不同的选项，保持 URL 简洁。
 */

import { defaultOptions, useSettingsStore } from '@/stores/settings'
import type { DecompileOptions } from '@/types/decompiler'

/** 将嵌套对象扁平化为 dot-separated 的键值对 */
function flatten(obj: Record<string, any>, prefix = ''): Record<string, string> {
  const result: Record<string, string> = {}
  for (const [key, value] of Object.entries(obj)) {
    const fullKey = prefix ? `${prefix}.${key}` : key
    if (value !== null && typeof value === 'object' && !Array.isArray(value)) {
      Object.assign(result, flatten(value, fullKey))
    } else {
      result[fullKey] = String(value)
    }
  }
  return result
}

/** 从扁平键值对恢复为嵌套对象 */
function unflatten(flat: Record<string, string>): Record<string, any> {
  const result: Record<string, any> = {}
  for (const [key, value] of Object.entries(flat)) {
    const parts = key.split('.')
    let current = result
    for (let i = 0; i < parts.length - 1; i++) {
      current[parts[i]] ??= {}
      current = current[parts[i]]
    }
    // 自动转换数字和布尔值
    if (value === 'true') current[parts[parts.length - 1]] = true
    else if (value === 'false') current[parts[parts.length - 1]] = false
    else if (/^\d+$/.test(value)) current[parts[parts.length - 1]] = Number(value)
    else current[parts[parts.length - 1]] = value
  }
  return result
}

/**
 * 从当前 URL 读取选项参数，如有则合并到 store 并返回 true。
 */
export function restoreFromUrl(): boolean {
  const params = new URLSearchParams(window.location.search)
  if (params.size === 0) return false

  const flat: Record<string, string> = {}
  for (const [key, value] of params) {
    flat[key] = value
  }

  const restored = unflatten(flat) as Partial<DecompileOptions>
  if (Object.keys(restored).length === 0) return false

  const store = useSettingsStore()
  // 深度合并恢复的选项到当前 store
  if (restored.dialect) store.options.dialect = restored.dialect as DecompileOptions['dialect']
  if (restored.parse) Object.assign(store.options.parse, restored.parse)
  if (restored.readability) Object.assign(store.options.readability, restored.readability)
  if (restored.naming) Object.assign(store.options.naming, restored.naming)
  if (restored.generate) Object.assign(store.options.generate, restored.generate)

  return true
}

/**
 * 生成分享 URL。只包含与默认值不同的参数。
 */
export function generateShareUrl(): string {
  const store = useSettingsStore()
  const currentFlat = flatten(store.options as unknown as Record<string, any>)

  // 需要临时拿到默认值对比——但不能破坏当前 store
  const defaults = flatten(defaultOptions() as unknown as Record<string, any>)

  const params = new URLSearchParams()
  for (const [key, value] of Object.entries(currentFlat)) {
    if (defaults[key] !== value) {
      params.set(key, value)
    }
  }

  const url = new URL(window.location.href)
  url.search = params.toString()
  return url.toString()
}
