/**
 * URL 参数分享 composable。
 *
 * 将当前反编译选项编码到 URL search params 中，便于分享。
 * 页面加载时通过严格白名单校验恢复并清理地址栏，防止原型污染、非法参数注入和刷新覆写。
 */

import { defaultOptions, sanitizeOptions, useSettingsStore } from '@/stores/settings'

const FORBIDDEN_KEYS = new Set(['__proto__', 'constructor', 'prototype'])

/** 将嵌套对象扁平化为 dot-separated 的键值对 */
function flatten(obj: Record<string, unknown>, prefix = ''): Record<string, string> {
  const result: Record<string, string> = {}
  for (const [key, value] of Object.entries(obj)) {
    const fullKey = prefix ? `${prefix}.${key}` : key
    if (value !== null && typeof value === 'object' && !Array.isArray(value)) {
      Object.assign(result, flatten(value as Record<string, unknown>, fullKey))
    } else {
      result[fullKey] = String(value)
    }
  }
  return result
}

/** 安全地从扁平键值对恢复为嵌套对象（屏蔽原型链键） */
export function unflattenSafe(flat: Record<string, string>): Record<string, unknown> {
  const result = Object.create(null) as Record<string, unknown>
  for (const [key, value] of Object.entries(flat)) {
    const parts = key.split('.')
    if (parts.length === 0 || parts.length > 4) continue
    if (parts.some((part) => !part || FORBIDDEN_KEYS.has(part))) continue

    let current = result
    let valid = true
    for (let i = 0; i < parts.length - 1; i++) {
      const part = parts[i]
      const existing = current[part]
      if (existing === undefined) {
        current[part] = Object.create(null)
      } else if (typeof existing !== 'object' || existing === null) {
        valid = false
        break
      }
      current = current[part] as Record<string, unknown>
    }
    if (!valid) continue

    const leaf = parts[parts.length - 1]
    if (value === 'true') current[leaf] = true
    else if (value === 'false') current[leaf] = false
    else if (value === 'null') current[leaf] = null
    else if (/^\d+$/.test(value)) current[leaf] = Number(value)
    else current[leaf] = value
  }
  return result
}

/**
 * 从当前 URL 读取选项参数，经白名单校验后应用到 store 并清理 URL 查询参数。
 */
export function restoreFromUrl(): boolean {
  const params = new URLSearchParams(window.location.search)
  if (params.size === 0) return false

  const flat: Record<string, string> = Object.create(null)
  for (const [key, value] of params) {
    flat[key] = value
  }

  const restored = unflattenSafe(flat)
  if (Object.keys(restored).length === 0) return false

  const store = useSettingsStore()
  // 以默认值为基线叠加分享参数，避免本地旧配置与分享链接互相污染
  const sanitized = sanitizeOptions(restored, defaultOptions())
  store.applySanitized(sanitized)

  try {
    const clean = new URL(window.location.href)
    clean.search = ''
    window.history.replaceState(null, '', clean.toString())
  } catch {
    // 忽略只读 history 环境
  }

  return true
}

/**
 * 生成分享 URL。只包含与默认值不同的参数。
 */
export function generateShareUrl(): string {
  const store = useSettingsStore()
  const currentFlat = flatten(store.options as unknown as Record<string, unknown>)
  const defaults = flatten(defaultOptions() as unknown as Record<string, unknown>)

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
