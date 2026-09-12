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
  type ShallowRef,
  shallowRef,
  useTemplateRef,
  watch,
} from 'vue'
import { useI18n } from 'vue-i18n'
import { useFileDecompile } from '@/composables/useFileDecompile'
import type { UnluacDialect } from '@/types/decompiler'
import type { useDecompiler } from '@/composables/useDecompiler'
import { matchGlob, useFileDrop } from '@/composables/useFileDrop'
import { useFilesStore } from '@/stores/files'
import { useSettingsStore } from '@/stores/settings'
import { shouldIgnoreDocumentShortcutTarget } from '@/utils/keyboard'

const emit = defineEmits<{ selected: [] }>()
const { t } = useI18n()
const filesStore = useFilesStore()
const settingsStore = useSettingsStore()
const dialog = useDialog()
const message = useMessage()

const decompiler = inject<ReturnType<typeof useDecompiler>>('decompiler')!
const { decompileFile, changeDialect } = useFileDecompile(decompiler)
const { isDragging, handleDrop, handleDragOver, handleDragLeave, handleFileInput } = useFileDrop()

function browserTextEncoding(encoding: string): string {
  return encoding === 'auto' ? 'utf-8' : encoding
}

// 编码变更时，重新解码所有 skipped（源码）文件
// skipped 文件的 result 是由 TextDecoder 从原始 bytes 按编码解码而来，
// 编码变了就必须重新解码，否则用户看到的是旧编码的结果
watch(
  () => settingsStore.options.parse.stringEncoding,
  (encoding) => {
    for (const file of filesStore.files) {
      if (file.status === 'skipped') {
        const sourceText = new TextDecoder(browserTextEncoding(encoding), { fatal: false }).decode(
          file.bytes,
        )
        filesStore.updateFileStatus(file.id, 'skipped', sourceText)
      }
    }
  },
)

// 注册快捷键回调
const shortcutActions =
  inject<ShallowRef<Record<string, (() => void) | undefined>>>('shortcutActions')!
shortcutActions.value = {
  ...shortcutActions.value,
  openFile: openFilePicker,
  openFolder: openFolderPicker,
}

const fileInputRef = useTemplateRef<HTMLInputElement>('fileInput')
const folderInputRef = useTemplateRef<HTMLInputElement>('folderInput')

const BATCH_WARNING_THRESHOLD = 50

/** 是否存在带目录结构的文件，决定使用树形或扁平视图 */
const searchQuery = shallowRef('')
const visibleFiles = computed(() =>
  filesStore.files.filter((file) =>
    file.relativePath.toLowerCase().includes(searchQuery.value.trim().toLowerCase()),
  ),
)
const hasNestedFiles = computed(() => visibleFiles.value.some((f) => f.relativePath.includes('/')))

/** 批量处理进度（正在处理时显示） */
const batchProgress = computed(() => {
  const total = filesStore.files.length
  if (total === 0) return null
  const done = total - filesStore.pendingCount - filesStore.processingCount
  if (done === total) return null
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

  for (const entry of entries) entry.dialect = settingsStore.options.dialect
  searchQuery.value = ''
  const added = filesStore.addFiles(entries)
  if (added.length === 0) return

  // 单文件直接选中；批量仅在未选中时选中第一个
  if (added.length === 1) {
    filesStore.selectFile(added[0].id)
  } else if (!filesStore.selectedFileId) {
    filesStore.selectFile(added[0].id)
  }

  emit('selected')

  // 逐个发起反编译
  for (const entry of added) {
    decompileFile(entry.id)
  }
}

async function onDrop(e: DragEvent) {
  if (!e.dataTransfer?.types.includes('Files')) return
  const entries = await handleDrop(e)
  await processFiles(entries)
}

async function onFileInputChange(e: Event) {
  const input = e.target as HTMLInputElement
  if (!input.files) return
  const entries = await handleFileInput(input.files)
  input.value = '' // 重置以允许再次选择相同文件
  await processFiles(entries)
}

/**
 * 文件夹选择后弹出 glob 输入对话框，让用户指定匹配模式。
 * 只有匹配的文件才会被加入列表并反编译。
 */
const folderGlobPattern = shallowRef('**/*')

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
          placeholder: '**/*',
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

/** 键盘上下导航文件列表，Delete 删除当前选中文件 */
function handleKeyNavigation(e: KeyboardEvent) {
  const target = e.target as HTMLElement
  if (!target.closest('.file-select') && shouldIgnoreDocumentShortcutTarget(e.target)) return

  const files = visibleFiles.value
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
    selectFile(files[nextIndex].id)
  } else if (e.key === 'Delete') {
    if (filesStore.selectedFileId) {
      filesStore.removeFile(filesStore.selectedFileId)
    }
  }
}

onMounted(async () => {
  // 从 IndexedDB 恢复文件历史并自动反编译
  const restored = await filesStore.restoreFromHistory()
  for (const entry of restored) {
    decompileFile(entry.id)
  }
})

/** 非方言设置继续应用到已有文件；方言仅是新导入文件的默认值。 */
watch(
  () => [
    settingsStore.options.parse,
    settingsStore.options.readability,
    settingsStore.options.naming,
    settingsStore.options.generate,
  ],
  () => {
    decompiler.cancelAll()
    const filesToRecompile = filesStore.files.filter((f) => f.status !== 'skipped')
    for (const file of filesToRecompile) {
      decompileFile(file.id)
    }
  },
  { deep: true },
)
function selectFile(id: string) {
  filesStore.selectFile(id)
  emit('selected')
}

defineExpose({ onDrop, isDragging, handleDragOver, handleDragLeave })
</script>

<template>
  <aside class="file-panel" :aria-label="t('filePanel.title')" @keydown="handleKeyNavigation">
    <div class="panel-heading">
      <span>{{ t('workspace.files') }}</span><span class="count-badge">{{ filesStore.files.length }}</span>
    </div>
    <div class="import-actions">
      <NButton type="primary" @click="openFilePicker"><template #icon><i-mdi-plus /></template>{{ t('filePanel.openFile') }}</NButton>
      <NButton secondary :title="t('filePanel.openFolder')" :aria-label="t('filePanel.openFolder')" @click="openFolderPicker"><template #icon><i-mdi-folder-plus-outline /></template></NButton>
    </div>
    <div v-if="filesStore.files.length" class="px-3 pb-3">
      <NInput v-model:value="searchQuery" :placeholder="t('workspace.searchFiles')" :input-props="{ 'aria-label': t('workspace.searchFiles') }" clearable size="small"><template #prefix><i-mdi-magnify /></template></NInput>
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
      <div v-if="filesStore.files.length === 0" class="file-empty">
        <i-mdi-file-document-multiple-outline class="text-3xl" />
        <p>{{ t('filePanel.empty') }}</p>
        <span>{{ t('workspace.fileHint') }}</span>
      </div>
      <div v-else-if="visibleFiles.length === 0" class="file-empty"><p>{{ t('filePanel.noFiles') }}</p></div>
      <!-- 有目录结构时使用树形视图 -->
      <FileTreeView
        v-else-if="hasNestedFiles"
        :files="visibleFiles"
        :selected-file-id="filesStore.selectedFileId"
        @select="selectFile($event)"
        @remove="(id: string) => { decompiler.cancel(id); filesStore.removeFile(id) }"
        @remove-folder="(path: string) => { filesStore.removeByPrefix(path + '/') }"
        @recompile="decompileFile($event)"
        @dialect="(id: string, value: UnluacDialect) => changeDialect(id, value)"
      />
      <!-- 无目录结构时使用扁平列表 -->
      <div v-else class="py-1">
        <FileListItem
          v-for="file in visibleFiles"
          :key="file.id"
          :file="file"
          :selected="file.id === filesStore.selectedFileId"
          @select="selectFile(file.id)"
          @remove="decompiler.cancel(file.id); filesStore.removeFile(file.id)"
          @recompile="decompileFile(file.id)"
          @dialect="changeDialect(file.id, $event)"
        />
      </div>
    </NScrollbar>

    <div class="file-panel-footer"><i-mdi-harddisk class="shrink-0" /><span>{{ t('workspace.history') }}</span></div>
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
