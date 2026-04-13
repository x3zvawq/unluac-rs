/**
 * 文件历史 store。
 *
 * 管理用户添加的字节码文件集合，追踪每个文件的反编译状态和结果。
 * 文件元信息和原始字节通过 IndexedDB 持久化，刷新页面后可恢复。
 * 运行时状态（result / richResult / error）不持久化，恢复后重新反编译。
 *
 * 文件历史（files）和打开的标签页（openTabIds）是独立的两个概念：
 * - files：用户的全部反编译历史，显示在侧边栏。
 * - openTabIds：用户当前正在观察的文件，显示在标签栏。
 * 关闭标签不会删除文件历史；从侧边栏移除文件才会真正删除。
 */

import { defineStore } from 'pinia'
import { computed, shallowRef } from 'vue'
import {
  clearAllFileRecords,
  deleteFileRecord,
  deleteFileRecords,
  type FileHistoryRecord,
  getAllFileRecords,
  putFileRecords,
} from '@/composables/useFileHistoryDB'
import type { FileEntry, FileStatus, RichDecompileResult } from '@/types/decompiler'

export const useFilesStore = defineStore('files', () => {
  const files = shallowRef<FileEntry[]>([])
  const selectedFileId = shallowRef<string | null>(null)
  /** 当前打开的标签页文件 ID 列表（有序） */
  const openTabIds = shallowRef<string[]>([])
  /** 标记是否已从 IndexedDB 恢复过，避免重复恢复 */
  const restored = shallowRef(false)

  const selectedFile = computed(
    () => files.value.find((f) => f.id === selectedFileId.value) ?? null,
  )

  /** 标签栏展示的文件列表——按 openTabIds 的顺序，仅包含已完成的文件 */
  const openFiles = computed(() => {
    const ids = openTabIds.value
    const map = new Map(files.value.map((f) => [f.id, f]))
    return ids
      .map((id) => map.get(id))
      .filter((f): f is FileEntry => f !== undefined && (f.status === 'success' || f.status === 'skipped'))
  })

  const pendingCount = computed(() => files.value.filter((f) => f.status === 'pending').length)

  const processingCount = computed(
    () => files.value.filter((f) => f.status === 'processing').length,
  )

  function addFiles(entries: FileEntry[]) {
    // 去重：不添加已有同名同大小的文件
    const existing = new Set(files.value.map((f) => `${f.relativePath}:${f.size}`))
    const newEntries = entries.filter((e) => !existing.has(`${e.relativePath}:${e.size}`))
    if (newEntries.length > 0) {
      files.value = [...files.value, ...newEntries]
      // 新文件加入打开标签列表
      openTabIds.value = [...openTabIds.value, ...newEntries.map((e) => e.id)]
      // 异步持久化新增文件（不阻塞 UI）
      const records: FileHistoryRecord[] = newEntries.map((e) => ({
        id: e.id,
        name: e.name,
        relativePath: e.relativePath,
        bytes: e.bytes,
        size: e.size,
        addedAt: Date.now(),
      }))
      putFileRecords(records)
    }
  }

  /** 从文件历史中彻底移除文件（侧边栏操作），同时关闭对应标签 */
  function removeFile(id: string) {
    files.value = files.value.filter((f) => f.id !== id)
    openTabIds.value = openTabIds.value.filter((tid) => tid !== id)
    if (selectedFileId.value === id) {
      selectedFileId.value = openTabIds.value[0] ?? null
    }
    deleteFileRecord(id)
  }

  /** 关闭单个标签页（不删除文件历史） */
  function closeTab(id: string) {
    openTabIds.value = openTabIds.value.filter((tid) => tid !== id)
    if (selectedFileId.value === id) {
      selectedFileId.value = openTabIds.value[0] ?? null
    }
  }

  /** 关闭指定文件之外的所有标签页 */
  function closeOtherTabs(keepId: string) {
    openTabIds.value = openTabIds.value.filter((tid) => tid === keepId)
    if (selectedFileId.value !== keepId) {
      selectedFileId.value = keepId
    }
  }

  /** 关闭指定文件右侧的所有标签页 */
  function closeTabsToRight(refId: string) {
    const idx = openTabIds.value.indexOf(refId)
    if (idx < 0) return
    const removed = new Set(openTabIds.value.slice(idx + 1))
    openTabIds.value = openTabIds.value.slice(0, idx + 1)
    if (selectedFileId.value && removed.has(selectedFileId.value)) {
      selectedFileId.value = refId
    }
  }

  /** 关闭所有标签页 */
  function closeAllTabs() {
    openTabIds.value = []
    selectedFileId.value = null
  }

  /** 按目录前缀批量移除文件 */
  function removeByPrefix(prefix: string) {
    const toRemove = files.value.filter((f) => f.relativePath.startsWith(prefix))
    if (toRemove.length === 0) return
    const removeIds = new Set(toRemove.map((f) => f.id))
    files.value = files.value.filter((f) => !removeIds.has(f.id))
    openTabIds.value = openTabIds.value.filter((tid) => !removeIds.has(tid))
    if (selectedFileId.value && removeIds.has(selectedFileId.value)) {
      selectedFileId.value = openTabIds.value[0] ?? null
    }
    deleteFileRecords(Array.from(removeIds))
  }

  function clearAllFiles() {
    files.value = []
    openTabIds.value = []
    selectedFileId.value = null
    clearAllFileRecords()
  }

  /** 选中文件，如果该文件尚未打开则自动加入标签栏 */
  function selectFile(id: string) {
    if (!openTabIds.value.includes(id)) {
      openTabIds.value = [...openTabIds.value, id]
    }
    selectedFileId.value = id
  }

  function updateFileStatus(id: string, status: FileStatus, result?: string, error?: string) {
    files.value = files.value.map((f) =>
      f.id === id ? { ...f, status, result: result ?? f.result, error: error ?? f.error } : f,
    )
  }

  function updateRichResult(id: string, richResult: RichDecompileResult) {
    files.value = files.value.map((f) => (f.id === id ? { ...f, richResult } : f))
  }

  function updateEditedResult(id: string, editedResult: string) {
    files.value = files.value.map((f) => (f.id === id ? { ...f, editedResult } : f))
  }

  function clearEditedResult(id: string) {
    files.value = files.value.map((f) => {
      if (f.id !== id) return f
      const { editedResult: _, ...rest } = f
      return rest
    })
  }

  /**
   * 从 IndexedDB 恢复文件历史。
   * 返回恢复的 FileEntry 列表（status 为 pending），
   * 调用方决定是否自动触发反编译。
   */
  async function restoreFromHistory(): Promise<FileEntry[]> {
    if (restored.value) return []
    restored.value = true
    const records = await getAllFileRecords()
    if (records.length === 0) return []
    const entries: FileEntry[] = records.map((r) => ({
      id: r.id,
      name: r.name,
      relativePath: r.relativePath,
      bytes: r.bytes,
      size: r.size,
      status: 'pending',
    }))
    files.value = entries
    // 恢复时所有文件都加入标签栏
    openTabIds.value = entries.map((e) => e.id)
    // 默认选中第一个
    selectedFileId.value = entries[0].id
    return entries
  }

  return {
    files,
    selectedFileId,
    selectedFile,
    openTabIds,
    openFiles,
    pendingCount,
    processingCount,
    restored,
    addFiles,
    removeFile,
    removeByPrefix,
    closeTab,
    closeOtherTabs,
    closeTabsToRight,
    closeAllTabs,
    clearAllFiles,
    selectFile,
    updateFileStatus,
    updateRichResult,
    updateEditedResult,
    clearEditedResult,
    restoreFromHistory,
  }
})
