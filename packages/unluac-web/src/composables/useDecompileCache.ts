/**
 * 反编译结果 IndexedDB 缓存。
 *
 * 使用 (文件内容 hash + 参数 hash) 作为 key 缓存反编译结果，
 * 避免对相同文件+参数组合重复执行 WASM 反编译。
 *
 * 设计决策：
 * - 使用 SubtleCrypto SHA-256 做内容 hash，性能好且浏览器原生支持
 * - 参数 hash 用 JSON.stringify 后 SHA-256，确保参数变更不命中旧缓存
 * - 缓存不设过期，用户清空浏览器数据或版本升级时自然淘汰
 * - 所有操作都是 best-effort：IndexedDB 不可用时静默回退，不影响反编译流程
 */

import type { DecompileOptions } from '@/types/decompiler'

const DB_NAME = 'unluac-cache'
const DB_VERSION = 1
const STORE_NAME = 'results'

let dbPromise: Promise<IDBDatabase> | null = null

function openDB(): Promise<IDBDatabase> {
  if (!dbPromise) {
    dbPromise = new Promise((resolve, reject) => {
      const request = indexedDB.open(DB_NAME, DB_VERSION)
      request.onupgradeneeded = () => {
        const db = request.result
        if (!db.objectStoreNames.contains(STORE_NAME)) {
          db.createObjectStore(STORE_NAME)
        }
      }
      request.onsuccess = () => resolve(request.result)
      request.onerror = () => reject(request.error)
    })
  }
  return dbPromise
}

async function sha256Hex(data: ArrayBuffer | Uint8Array): Promise<string> {
  const hashBuffer = await crypto.subtle.digest('SHA-256', data as ArrayBuffer)
  const bytes = new Uint8Array(hashBuffer)
  return Array.from(bytes, (b) => b.toString(16).padStart(2, '0')).join('')
}

async function computeCacheKey(bytes: Uint8Array, options: DecompileOptions): Promise<string> {
  const [fileHash, optionsHash] = await Promise.all([
    sha256Hex(bytes),
    sha256Hex(new TextEncoder().encode(JSON.stringify(options))),
  ])
  return `${fileHash}:${optionsHash}`
}

/** 查询缓存，miss 时返回 undefined */
export async function getCached(
  bytes: Uint8Array,
  options: DecompileOptions,
): Promise<string | undefined> {
  try {
    const key = await computeCacheKey(bytes, options)
    const db = await openDB()
    return new Promise((resolve) => {
      const tx = db.transaction(STORE_NAME, 'readonly')
      const store = tx.objectStore(STORE_NAME)
      const req = store.get(key)
      req.onsuccess = () => resolve(req.result as string | undefined)
      req.onerror = () => resolve(undefined)
    })
  } catch {
    return undefined
  }
}

/** 写入缓存 */
export async function setCache(
  bytes: Uint8Array,
  options: DecompileOptions,
  source: string,
): Promise<void> {
  try {
    const key = await computeCacheKey(bytes, options)
    const db = await openDB()
    const tx = db.transaction(STORE_NAME, 'readwrite')
    tx.objectStore(STORE_NAME).put(source, key)
  } catch {
    // 静默失败，缓存写入不影响核心流程
  }
}
