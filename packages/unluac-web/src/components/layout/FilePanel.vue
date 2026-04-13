<script setup lang="ts">
/**
 * 文件列表面板。
 *
 * 职责：
 * - 提供拖拽区域接收字节码文件
 * - 显示文件列表和每个文件的反编译状态
 * - 提供文件/文件夹选择按钮
 * - 发起反编译请求（通过 inject 的 decompiler）
 *
 * 不直接持有文件数据，通过 filesStore 管理。
 */

import { NInput, useDialog, useMessage } from 'naive-ui'
import {
  computed,
  h,
  inject,
  onMounted,
  onUnmounted,
  type ShallowRef,
  shallowRef,
  useTemplateRef,
  watch,
} from 'vue'
import { useI18n } from 'vue-i18n'
import { getCached, setCache } from '@/composables/useDecompileCache'
import type { useDecompiler } from '@/composables/useDecompiler'
import { matchGlob, useFileDrop } from '@/composables/useFileDrop'
import { useFilesStore } from '@/stores/files'
import { useSettingsStore } from '@/stores/settings'

const { t } = useI18n()
const filesStore = useFilesStore()
const settingsStore = useSettingsStore()
const dialog = useDialog()
const message = useMessage()

const decompiler = inject<ReturnType<typeof useDecompiler>>('decompiler')!
const { isDragging, handleDrop, handleDragOver, handleDragLeave, handleFileInput } = useFileDrop()

// 编码变更时，重新解码所有 skipped（源码）文件
// skipped 文件的 result 是由 TextDecoder 从原始 bytes 按编码解码而来，
// 编码变了就必须重新解码，否则用户看到的是旧编码的结果
watch(
  () => settingsStore.options.parse.stringEncoding,
  (encoding) => {
    for (const file of filesStore.files) {
      if (file.status === 'skipped') {
        const sourceText = new TextDecoder(encoding, { fatal: false }).decode(file.bytes)
        filesStore.updateFileStatus(file.id, 'skipped', sourceText)
      }
    }
  },
)

// 注册快捷键回调
const shortcutActions =
  inject<ShallowRef<Record<string, (() => void) | undefined>>>('shortcutActions')!
shortcutActions.value = { ...shortcutActions.value, openFile: () => openFilePicker() }

const fileInputRef = useTemplateRef<HTMLInputElement>('fileInput')
const folderInputRef = useTemplateRef<HTMLInputElement>('folderInput')

const BATCH_WARNING_THRESHOLD = 50

/** 是否存在带目录结构的文件，决定使用树形或扁平视图 */
const hasNestedFiles = computed(() => filesStore.files.some((f) => f.relativePath.includes('/')))

/** 批量处理进度（正在处理时显示） */
const batchProgress = computed(() => {
  const total = filesStore.files.length
  if (total === 0) return null
  const done = filesStore.files.filter((f) => f.status === 'success' || f.status === 'error').length
  const processing = filesStore.processingCount > 0
  if (!processing && done === total) return null
  return { done, total, percentage: Math.round((done / total) * 100) }
})

/** 批量完成后的统计信息（有错误时显示） */
const showBatchStats = shallowRef(false)
const batchStats = computed(() => {
  const files = filesStore.files
  if (files.length < 2) return null
  const success = files.filter((f) => f.status === 'success').length
  const error = files.filter((f) => f.status === 'error').length
  const processing = files.some((f) => f.status === 'processing' || f.status === 'pending')
  if (processing || error === 0) return null
  return { success, error }
})

// 批量处理完成且有错误时自动弹出统计
watch(batchStats, (stats) => {
  if (stats) showBatchStats.value = true
})

async function processFiles(entries: Awaited<ReturnType<typeof handleFileInput>>) {
  if (entries.length === 0) {
    message.warning(t('filePanel.noFiles'))
    return
  }

  if (entries.length > BATCH_WARNING_THRESHOLD) {
    const confirmed = await new Promise<boolean>((resolve) => {
      dialog.warning({
        title: t('filePanel.batchWarning', { count: entries.length }),
        positiveText: 'OK',
        negativeText: 'Cancel',
        onPositiveClick: () => resolve(true),
        onNegativeClick: () => resolve(false),
        onClose: () => resolve(false),
      })
    })
    if (!confirmed) return
  }

  filesStore.addFiles(entries)

  // 单文件直接选中；批量仅在未选中时选中第一个
  if (entries.length === 1) {
    filesStore.selectFile(entries[0].id)
  } else if (!filesStore.selectedFileId) {
    filesStore.selectFile(entries[0].id)
  }

  // 逐个发起反编译
  for (const entry of entries) {
    decompileFile(entry.id)
  }
}

/**
 * 检测文件是否已经是 Lua 源码（而非字节码）。
 * Lua 字节码以 \x1bLua 开头（标准 Lua），\x1bLJ 开头（LuaJIT），
 * \x00\x06 或包含特定 Luau 签名。
 * 如果不是已知的字节码格式，视为源码文件。
 */
function isLuaSource(bytes: Uint8Array): boolean {
  if (bytes.length < 4) return true
  // 标准 Lua 字节码：\x1bLua
  if (bytes[0] === 0x1b && bytes[1] === 0x4c && bytes[2] === 0x75 && bytes[3] === 0x61) return false
  // LuaJIT 字节码：\x1bLJ
  if (bytes[0] === 0x1b && bytes[1] === 0x4c && bytes[2] === 0x4a) return false
  // Luau 字节码版本 3-6：前两字节为 \x06\x??（version byte + type version）
  // Luau bytecode starts with version byte (2-6) + 0x00 or specific patterns
  if (bytes[0] >= 0x02 && bytes[0] <= 0x06 && bytes[1] === 0x00) return false
  return true
}

async function decompileFile(fileId: string) {
  const file = filesStore.files.find((f) => f.id === fileId)
  if (!file) return

  // 检测是否已经是源码文件
  if (isLuaSource(file.bytes)) {
    // 遵循反编译参数中配置的字符串编码
    const encoding = settingsStore.options.parse.stringEncoding
    const sourceText = new TextDecoder(encoding, { fatal: false }).decode(file.bytes)
    filesStore.updateFileStatus(fileId, 'skipped', sourceText)
    return
  }

  filesStore.updateFileStatus(fileId, 'processing')

  try {
    const currentFile = filesStore.files.find((f) => f.id === fileId)
    if (!currentFile) return

    const bytes = new Uint8Array(currentFile.bytes)
    const options = settingsStore.options

    // 先查询 IndexedDB 缓存
    const cached = await getCached(bytes, options)
    if (cached !== undefined) {
      filesStore.updateFileStatus(fileId, 'success', cached)
      return
    }

    const source = await decompiler.decompile(fileId, bytes, options)
    filesStore.updateFileStatus(fileId, 'success', source)

    // 异步写入缓存（不阻塞 UI）
    setCache(currentFile.bytes, options, source)
  } catch (err) {
    // cancel 引起的拒绝不视为错误
    if (err instanceof Error && err.message === 'Cancelled') return
    console.error(`[decompile] file ${fileId} failed:`, err)
    filesStore.updateFileStatus(
      fileId,
      'error',
      undefined,
      err instanceof Error ? err.message : String(err),
    )
  }
}

async function onDrop(e: DragEvent) {
  const entries = await handleDrop(e)
  processFiles(entries)
}

async function onFileInputChange(e: Event) {
  const input = e.target as HTMLInputElement
  if (!input.files) return
  const entries = await handleFileInput(input.files)
  input.value = '' // 重置以允许再次选择相同文件
  processFiles(entries)
}

/**
 * 文件夹选择后弹出 glob 输入对话框，让用户指定匹配模式。
 * 只有匹配的文件才会被加入列表并反编译。
 */
const folderGlobPattern = shallowRef('**/*.lua')

async function onFolderInputChange(e: Event) {
  const input = e.target as HTMLInputElement
  if (!input.files || input.files.length === 0) {
    input.value = ''
    return
  }
  // FileList 是 live 对象，重置 input.value 后会清空，因此先转为 Array
  const allFiles = Array.from(input.files)
  input.value = ''

  // 让用户输入 glob 匹配模式
  const pattern = await new Promise<string | null>((resolve) => {
    const inputRef = shallowRef(folderGlobPattern.value)
    dialog.create({
      title: t('filePanel.globDialog.title'),
      content: () =>
        h(NInput, {
          value: inputRef.value,
          'onUpdate:value': (v: string) => {
            inputRef.value = v
          },
          placeholder: '**/*.lua',
        }),
      positiveText: 'OK',
      negativeText: t('filePanel.globDialog.cancel'),
      onPositiveClick: () => {
        folderGlobPattern.value = inputRef.value
        resolve(inputRef.value)
      },
      onNegativeClick: () => resolve(null),
      onClose: () => resolve(null),
    })
  })

  if (!pattern) return

  const entries = await handleFileInput(allFiles)
  // 按 glob 模式过滤
  const filtered = entries.filter((entry) => matchGlob(entry.relativePath, pattern))
  processFiles(filtered)
}

function openFilePicker() {
  fileInputRef.value?.click()
}

function openFolderPicker() {
  folderInputRef.value?.click()
}

/** 键盘上下导航文件列表 */
function handleKeyNavigation(e: KeyboardEvent) {
  const files = filesStore.files
  if (files.length === 0) return

  if (e.key === 'ArrowDown' || e.key === 'ArrowUp') {
    e.preventDefault()
    const currentIndex = files.findIndex((f) => f.id === filesStore.selectedFileId)
    let nextIndex: number
    if (e.key === 'ArrowDown') {
      nextIndex = currentIndex < files.length - 1 ? currentIndex + 1 : 0
    } else {
      nextIndex = currentIndex > 0 ? currentIndex - 1 : files.length - 1
    }
    filesStore.selectFile(files[nextIndex].id)
  } else if (e.key === 'Delete' || e.key === 'Backspace') {
    if (filesStore.selectedFileId) {
      filesStore.removeFile(filesStore.selectedFileId)
    }
  }
}

onMounted(async () => {
  document.addEventListener('keydown', handleKeyNavigation)
  // 从 IndexedDB 恢复文件历史并自动反编译
  const restored = await filesStore.restoreFromHistory()
  for (const entry of restored) {
    decompileFile(entry.id)
  }
})

onUnmounted(() => {
  document.removeEventListener('keydown', handleKeyNavigation)
})

/** 设置变更时取消正在进行的任务并重新反编译所有文件 */
watch(
  () => ({ ...settingsStore.options }),
  () => {
    decompiler.cancelAll()
    const filesToRecompile = filesStore.files.filter(
      (f) => f.status === 'success' || f.status === 'error',
    )
    for (const file of filesToRecompile) {
      decompileFile(file.id)
    }
  },
  { deep: true },
)
</script>

<template>
  <aside
    class="flex shrink-0 flex-col"
    style="border-right: 1px solid var(--app-border)"
    @drop="onDrop"
    @dragover="handleDragOver"
    @dragleave="handleDragLeave"
  >
    <!-- 标题栏 -->
    <div class="flex items-center justify-between px-3 py-2" style="border-bottom: 1px solid var(--app-border)">
      <span class="text-sm font-medium">{{ t('filePanel.title') }}</span>
      <div class="flex gap-1">
        <NButton quaternary size="tiny" @click="openFilePicker">
          <template #icon>
            <NIcon>
              <svg xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M13 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V9z"/><polyline points="13 2 13 9 20 9"/></svg>
            </NIcon>
          </template>
        </NButton>
        <NButton quaternary size="tiny" @click="openFolderPicker">
          <template #icon>
            <NIcon>
              <svg xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M22 19a2 2 0 0 1-2 2H4a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h5l2 3h9a2 2 0 0 1 2 2z"/></svg>
            </NIcon>
          </template>
        </NButton>
      </div>
    </div>

    <!-- 批量进度条 -->
    <div v-if="batchProgress" class="px-3 py-1.5">
      <NProgress
        type="line"
        :percentage="batchProgress.percentage"
        :show-indicator="false"
        :height="4"
      />
      <div class="mt-0.5 text-xs" style="color: var(--app-text-secondary)">
        {{ t('filePanel.progress', { done: batchProgress.done, total: batchProgress.total }) }}
      </div>
    </div>

    <!-- 批量错误统计 -->
    <div
      v-if="showBatchStats && batchStats"
      class="flex items-center justify-between border-b border-red-200 bg-red-50 px-3 py-1.5 dark:border-red-900 dark:bg-red-950/30"
    >
      <span class="text-xs text-red-600 dark:text-red-400">
        {{ t('filePanel.batchStats', batchStats) }}
      </span>
      <NButton quaternary size="tiny" @click="showBatchStats = false">
        {{ t('filePanel.dismissStats') }}
      </NButton>
    </div>

    <!-- 文件列表 -->
    <NScrollbar class="flex-1">
      <div
        v-if="filesStore.files.length === 0"
        class="flex h-full flex-col items-center justify-center p-4"
        :class="{ 'bg-indigo-50 dark:bg-indigo-950/30': isDragging }"
      >
        <NEmpty :description="t('filePanel.dropHint')" />
      </div>
      <!-- 有目录结构时使用树形视图 -->
      <FileTreeView
        v-else-if="hasNestedFiles"
        :files="filesStore.files"
        :selected-file-id="filesStore.selectedFileId"
        @select="filesStore.selectFile($event)"
        @remove="(id: string) => { decompiler.cancel(id); filesStore.removeFile(id) }"
        @remove-folder="(path: string) => { filesStore.removeByPrefix(path + '/') }"
        @recompile="decompileFile($event)"
      />
      <!-- 无目录结构时使用扁平列表 -->
      <div v-else class="py-1">
        <FileListItem
          v-for="file in filesStore.files"
          :key="file.id"
          :file="file"
          :selected="file.id === filesStore.selectedFileId"
          @select="filesStore.selectFile(file.id)"
          @remove="decompiler.cancel(file.id); filesStore.removeFile(file.id)"
          @recompile="decompileFile(file.id)"
        />
      </div>
    </NScrollbar>

    <!-- 隐藏的 file inputs -->
    <input
      ref="fileInput"
      type="file"
      multiple
      class="hidden"
      @change="onFileInputChange"
    />
    <input
      ref="folderInput"
      type="file"
      webkitdirectory
      class="hidden"
      @change="onFolderInputChange"
    />
  </aside>
</template>
