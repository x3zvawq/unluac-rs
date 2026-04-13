/**
 * 文件拖拽和选择 composable。
 *
 * 封装拖拽区域的事件处理和文件/文件夹选择逻辑。
 * 生成 FileEntry 对象供 FilesStore 消费。
 *
 * 不过滤文件扩展名——字节码文件可能有任何扩展名甚至没有扩展名。
 * 过滤逻辑由调用方通过 glob 模式在目录选择时提供。
 */

import { shallowRef } from 'vue'
import type { FileEntry } from '@/types/decompiler'

let idCounter = 0
function generateId(): string {
  return `file-${Date.now()}-${++idCounter}`
}

/**
 * 简易 glob 匹配器（仅支持 * 和 ** 通配符）。
 * 将 glob 模式转换为正则表达式进行匹配。
 */
function globToRegex(pattern: string): RegExp {
  let regex = ''
  let i = 0
  while (i < pattern.length) {
    const char = pattern[i]
    if (char === '*') {
      if (pattern[i + 1] === '*') {
        // ** 匹配任意层目录
        if (pattern[i + 2] === '/') {
          regex += '(?:.*\\/)?'
          i += 3
        } else {
          regex += '.*'
          i += 2
        }
      } else {
        // * 匹配当前层中除 / 外的任意字符
        regex += '[^/]*'
        i++
      }
    } else if (char === '?') {
      regex += '[^/]'
      i++
    } else if (char === '.') {
      regex += '\\.'
      i++
    } else {
      regex += char
      i++
    }
  }
  return new RegExp(`^${regex}$`, 'i')
}

/** 判断相对路径是否匹配 glob 模式 */
export function matchGlob(relativePath: string, pattern: string): boolean {
  const re = globToRegex(pattern)
  return re.test(relativePath)
}

async function fileToEntry(file: File, relativePath: string): Promise<FileEntry> {
  const buffer = await file.arrayBuffer()
  return {
    id: generateId(),
    name: file.name,
    relativePath,
    bytes: new Uint8Array(buffer),
    size: file.size,
    status: 'pending',
  }
}

/**
 * 从 DataTransferItemList 递归读取文件（支持文件夹拖拽）。
 */
async function readDataTransferItems(items: DataTransferItemList): Promise<FileEntry[]> {
  const entries: FileSystemEntry[] = []
  for (const item of items) {
    const entry = item.webkitGetAsEntry?.()
    if (entry) entries.push(entry)
  }
  return readEntries(entries, '')
}

/**
 * readEntries 只返回一批条目（通常上限约 100 条），
 * 必须反复调用直到返回空数组才能拿到完整目录内容。
 */
async function readAllDirEntries(reader: FileSystemDirectoryReader): Promise<FileSystemEntry[]> {
  const all: FileSystemEntry[] = []
  while (true) {
    const batch = await new Promise<FileSystemEntry[]>((resolve, reject) => {
      reader.readEntries(resolve, reject)
    })
    if (batch.length === 0) break
    all.push(...batch)
  }
  return all
}

async function readEntries(entries: FileSystemEntry[], basePath: string): Promise<FileEntry[]> {
  const results: FileEntry[] = []

  for (const entry of entries) {
    if (entry.isFile) {
      const fileEntry = entry as FileSystemFileEntry
      const file = await new Promise<File>((resolve, reject) => {
        fileEntry.file(resolve, reject)
      })
      const relativePath = basePath ? `${basePath}/${file.name}` : file.name
      const fe = await fileToEntry(file, relativePath)
      results.push(fe)
    } else if (entry.isDirectory) {
      const dirEntry = entry as FileSystemDirectoryEntry
      const childEntries = await readAllDirEntries(dirEntry.createReader())
      const dirPath = basePath ? `${basePath}/${entry.name}` : entry.name
      const children = await readEntries(childEntries, dirPath)
      results.push(...children)
    }
  }

  return results
}

export function useFileDrop() {
  const isDragging = shallowRef(false)

  async function handleDrop(e: DragEvent): Promise<FileEntry[]> {
    isDragging.value = false
    e.preventDefault()
    if (!e.dataTransfer) return []
    return readDataTransferItems(e.dataTransfer.items)
  }

  function handleDragOver(e: DragEvent) {
    e.preventDefault()
    isDragging.value = true
  }

  function handleDragLeave() {
    isDragging.value = false
  }

  /**
   * 处理 <input type="file"> 选择的文件。
   * 接受 FileList 或 File[]（文件夹选择时需先转为 Array 避免 live FileList 被清空）。
   */
  async function handleFileInput(fileList: FileList | File[]): Promise<FileEntry[]> {
    const entries: FileEntry[] = []
    for (const file of fileList) {
      // webkitRelativePath 在文件夹选择时有值
      const relativePath = (file as any).webkitRelativePath || file.name
      const fe = await fileToEntry(file, relativePath)
      entries.push(fe)
    }
    return entries
  }

  return {
    isDragging,
    handleDrop,
    handleDragOver,
    handleDragLeave,
    handleFileInput,
  }
}
