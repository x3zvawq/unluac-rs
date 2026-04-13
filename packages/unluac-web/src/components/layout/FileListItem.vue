<script setup lang="ts">
/**
 * 文件列表中单个文件项。
 *
 * 职责：展示文件名、大小、状态图标，处理选中和右键菜单。
 * 不持有状态，纯展示组件，所有操作通过 emit 通知父组件。
 */

import { computed, inject, shallowRef } from 'vue'
import { useI18n } from 'vue-i18n'
import type { FileEntry } from '@/types/decompiler'

const props = defineProps<{
  file: FileEntry
  selected: boolean
}>()

const emit = defineEmits<{
  select: []
  remove: []
  recompile: []
}>()

const { t } = useI18n()

const startCompare = inject<((fileId: string) => void) | null>('startCompare', null)

const showContextMenu = shallowRef(false)
const contextMenuX = shallowRef(0)
const contextMenuY = shallowRef(0)

const contextMenuOptions = computed(() => [
  { label: t('filePanel.contextMenu.recompile'), key: 'recompile' },
  { label: t('filePanel.contextMenu.download'), key: 'download' },
  { label: t('filePanel.contextMenu.remove'), key: 'remove' },
])

function formatSize(bytes: number): string {
  if (bytes < 1024) return `${bytes} B`
  if (bytes < 1024 * 1024) return `${(bytes / 1024).toFixed(1)} KB`
  return `${(bytes / (1024 * 1024)).toFixed(1)} MB`
}

function handleContextAction(key: string) {
  showContextMenu.value = false
  switch (key) {
    case 'recompile':
      emit('recompile')
      break
    case 'compare':
      startCompare?.(props.file.id)
      break
    case 'download':
      downloadResult()
      break
    case 'remove':
      emit('remove')
      break
  }
}

function openContextMenu(e: MouseEvent) {
  contextMenuX.value = e.clientX
  contextMenuY.value = e.clientY
  showContextMenu.value = true
}

function downloadResult() {
  if (!props.file.result) return
  const blob = new Blob([props.file.result], { type: 'text/x-lua' })
  const url = URL.createObjectURL(blob)
  const a = document.createElement('a')
  a.href = url
  a.download = `${props.file.name.replace(/\.[^.]+$/, '')}.lua`
  a.click()
  URL.revokeObjectURL(url)
}
</script>

<template>
  <!-- NDropdown 使用 x/y 定位时进入 positionManually 模式，不会渲染默认 slot，
       因此必须将菜单与触发元素并列放置，而非让 NDropdown 包裹触发元素 -->
  <div
    class="group flex cursor-pointer items-center gap-2 px-3 py-1.5 text-sm transition-colors"
    :class="[
      selected
        ? 'bg-indigo-100 text-indigo-800 dark:bg-indigo-900/40 dark:text-indigo-200'
        : 'hover:bg-gray-100 dark:hover:bg-gray-800',
    ]"
    @click="emit('select')"
    @contextmenu.prevent="openContextMenu"
  >
    <!-- 状态指示器 -->
    <NIcon :size="14">
      <svg v-if="file.status === 'pending'" xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" class="text-gray-400"><circle cx="12" cy="12" r="10"/></svg>
      <svg v-else-if="file.status === 'processing'" xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" class="animate-spin text-blue-500"><path d="M21 12a9 9 0 1 1-6.219-8.56"/></svg>
      <svg v-else-if="file.status === 'success'" xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" class="text-green-500"><path d="M22 11.08V12a10 10 0 1 1-5.93-9.14"/><polyline points="22 4 12 14.01 9 11.01"/></svg>
      <!-- skipped: 已是源码文件，显示为蓝色文本图标 -->
      <svg v-else-if="file.status === 'skipped'" xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" class="text-amber-500"><path d="M14.5 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V7.5L14.5 2z"/><polyline points="14 2 14 8 20 8"/><line x1="16" y1="13" x2="8" y2="13"/><line x1="16" y1="17" x2="8" y2="17"/></svg>
      <svg v-else xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" class="text-red-500"><circle cx="12" cy="12" r="10"/><line x1="15" y1="9" x2="9" y2="15"/><line x1="9" y1="9" x2="15" y2="15"/></svg>
    </NIcon>

    <!-- 文件信息 -->
    <div class="min-w-0 flex-1">
      <div class="truncate">{{ file.name }}</div>
      <div
        v-if="file.relativePath !== file.name"
        class="truncate text-xs text-gray-400 dark:text-gray-500"
      >
        {{ file.relativePath }}
      </div>
    </div>

    <!-- 文件大小 / hover 时显示操作按钮 -->
    <span class="shrink-0 text-xs text-gray-400 group-hover:hidden dark:text-gray-500">
      {{ formatSize(file.size) }}
    </span>
    <span class="hidden shrink-0 items-center gap-0.5 group-hover:flex">
      <!-- 重新反编译 -->
      <button
        class="rounded p-0.5 text-gray-400 transition-colors hover:bg-gray-200 hover:text-blue-600 dark:text-gray-500 dark:hover:bg-gray-700 dark:hover:text-blue-400"
        :title="t('filePanel.contextMenu.recompile')"
        @click.stop="emit('recompile')"
      >
        <svg xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><polyline points="23 4 23 10 17 10"/><path d="M20.49 15a9 9 0 1 1-2.12-9.36L23 10"/></svg>
      </button>
      <!-- 下载结果 -->
      <button
        class="rounded p-0.5 text-gray-400 transition-colors hover:bg-gray-200 hover:text-green-600 dark:text-gray-500 dark:hover:bg-gray-700 dark:hover:text-green-400"
        :title="t('filePanel.contextMenu.download')"
        @click.stop="downloadResult()"
      >
        <svg xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4"/><polyline points="7 10 12 15 17 10"/><line x1="12" y1="15" x2="12" y2="3"/></svg>
      </button>
      <!-- 移除 -->
      <button
        class="rounded p-0.5 text-gray-400 transition-colors hover:bg-gray-200 hover:text-red-600 dark:text-gray-500 dark:hover:bg-gray-700 dark:hover:text-red-400"
        :title="t('filePanel.contextMenu.remove')"
        @click.stop="emit('remove')"
      >
        <svg xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><line x1="18" y1="6" x2="6" y2="18"/><line x1="6" y1="6" x2="18" y2="18"/></svg>
      </button>
    </span>
  </div>

  <NDropdown
    trigger="manual"
    placement="bottom-start"
    :options="contextMenuOptions"
    :show="showContextMenu"
    :x="contextMenuX"
    :y="contextMenuY"
    @select="handleContextAction"
    @clickoutside="showContextMenu = false"
  />
</template>
