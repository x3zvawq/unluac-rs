/**
 * 文件历史 IndexedDB 持久化。
 *
 * 将用户添加的文件元信息 + 原始字节持久化到 IndexedDB，
 * 页面刷新后可恢复文件列表，避免丢失工作状态。
 *
 * 设计决策：
 * - 存储完整 bytes（Uint8Array）：文件一般不大（几十 KB 级别），
 *   IndexedDB 支持存储二进制数据，不需要转 base64
 * - 不存储 result / richResult / error 等运行时状态：
 *   这些可通过重新反编译恢复
 * - best-effort：IndexedDB 不可用时静默回退
 */

const DB_NAME = 'unluac-file-history'
const DB_VERSION = 1
const STORE_NAME = 'files'

let dbPromise: Promise<IDBDatabase> | null = null

/** 存入 IndexedDB 的文件记录（不含运行时状态） */
export interface FileHistoryRecord {
  id: string
  name: string
  relativePath: string
  bytes: Uint8Array
  size: number
  /** 文件添加时间戳，用于排序和清理 */
  addedAt: number
}

function openDB(): Promise<IDBDatabase> {
  if (!dbPromise) {
    dbPromise = new Promise((resolve, reject) => {
      const request = indexedDB.open(DB_NAME, DB_VERSION)
      request.onupgradeneeded = () => {
        const db = request.result
        if (!db.objectStoreNames.contains(STORE_NAME)) {
          db.createObjectStore(STORE_NAME, { keyPath: 'id' })
        }
      }
      request.onsuccess = () => resolve(request.result)
      request.onerror = () => reject(request.error)
    })
  }
  return dbPromise
}

/** 获取所有已保存的文件记录 */
export async function getAllFileRecords(): Promise<FileHistoryRecord[]> {
  try {
    const db = await openDB()
    return new Promise((resolve) => {
      const tx = db.transaction(STORE_NAME, 'readonly')
      const store = tx.objectStore(STORE_NAME)
      const req = store.getAll()
      req.onsuccess = () => resolve(req.result as FileHistoryRecord[])
      req.onerror = () => resolve([])
    })
  } catch {
    return []
  }
}

/** 批量保存文件记录 */
export async function putFileRecords(records: FileHistoryRecord[]): Promise<void> {
  try {
    const db = await openDB()
    const tx = db.transaction(STORE_NAME, 'readwrite')
    const store = tx.objectStore(STORE_NAME)
    for (const record of records) {
      store.put(record)
    }
  } catch {
    // 静默失败
  }
}

/** 删除指定 id 的文件记录 */
export async function deleteFileRecord(id: string): Promise<void> {
  try {
    const db = await openDB()
    const tx = db.transaction(STORE_NAME, 'readwrite')
    tx.objectStore(STORE_NAME).delete(id)
  } catch {
    // 静默失败
  }
}

/** 批量删除文件记录 */
export async function deleteFileRecords(ids: string[]): Promise<void> {
  try {
    const db = await openDB()
    const tx = db.transaction(STORE_NAME, 'readwrite')
    const store = tx.objectStore(STORE_NAME)
    for (const id of ids) {
      store.delete(id)
    }
  } catch {
    // 静默失败
  }
}

/** 清空所有文件记录 */
export async function clearAllFileRecords(): Promise<void> {
  try {
    const db = await openDB()
    const tx = db.transaction(STORE_NAME, 'readwrite')
    tx.objectStore(STORE_NAME).clear()
  } catch {
    // 静默失败
  }
}
