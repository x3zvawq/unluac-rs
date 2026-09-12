<script setup lang="ts">
/**
 * 文件列表中单个文件项。
 *
 * 职责：展示文件名、大小、状态图标，处理选中和右键菜单。
 * 不持有状态，纯展示组件，所有操作通过 emit 通知父组件。
 */

import { computed, shallowRef } from 'vue'
import { useI18n } from 'vue-i18n'
import type { FileEntry, UnluacDialect } from '@/types/decompiler'
import { dialectOptions } from '@/utils/dialects'

const props = defineProps<{
  file: FileEntry
  selected: boolean
}>()

const emit = defineEmits<{
  select: []
  remove: []
  recompile: []
  dialect: [value: UnluacDialect]
}>()

const { t } = useI18n()
const dialectLabel = computed(
  () => dialectOptions.find((option) => option.value === props.file.dialect)?.label,
)
const dialectMenu = dialectOptions.map(({ label, value }) => ({ label, key: value }))

const showContextMenu = shallowRef(false)
const contextMenuX = shallowRef(0)
const contextMenuY = shallowRef(0)

const contextMenuOptions = computed(() => [
  { label: t('filePanel.contextMenu.recompile'), key: 'recompile' },
  {
    label: t('filePanel.contextMenu.download'),
    key: 'download',
    disabled: props.file.result === undefined,
  },
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
  if (props.file.result === undefined) return
  const blob = new Blob([props.file.editedResult ?? props.file.result], { type: 'text/x-lua' })
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
    class="file-row"
    :class="{ selected }"
    :title="file.relativePath"
    @contextmenu.prevent="openContextMenu"
  >
    <button class="file-select" :aria-pressed="selected" @click="emit('select')">
    <!-- 状态指示器 -->
    <NIcon :size="17" :title="t(`filePanel.status.${file.status}`)">
      <svg v-if="file.status === 'pending'" xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" class="text-gray-400"><circle cx="12" cy="12" r="10"/></svg>
      <svg v-else-if="file.status === 'processing'" xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" class="animate-spin text-blue-500"><path d="M21 12a9 9 0 1 1-6.219-8.56"/></svg>
      <svg v-else-if="file.status === 'success'" xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" class="text-green-500"><path d="M22 11.08V12a10 10 0 1 1-5.93-9.14"/><polyline points="22 4 12 14.01 9 11.01"/></svg>
      <!-- skipped: 已是源码文件，显示为蓝色文本图标 -->
      <svg v-else-if="file.status === 'skipped'" xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" class="text-amber-500"><path d="M14.5 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V7.5L14.5 2z"/><polyline points="14 2 14 8 20 8"/><line x1="16" y1="13" x2="8" y2="13"/><line x1="16" y1="17" x2="8" y2="17"/></svg>
      <svg v-else xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" class="text-red-500"><circle cx="12" cy="12" r="10"/><line x1="15" y1="9" x2="9" y2="15"/><line x1="9" y1="9" x2="15" y2="15"/></svg>
    </NIcon>

    <span class="min-w-0 flex-1 text-left">
      <span class="block truncate font-medium">{{ file.name }}</span>
      <span class="file-meta">{{ formatSize(file.size) }} · {{ t(`filePanel.status.${file.status}`) }}</span>
    </span>
    </button>
    <NTag v-if="file.status === 'skipped'" size="small" :bordered="false">
      {{ t('filePanel.sourceTag') }}
    </NTag>
    <NDropdown v-else trigger="click" :options="dialectMenu" @select="(value: UnluacDialect) => emit('dialect', value)">
      <button
        type="button"
        class="dialect-tag"
        :title="t('filePanel.fileDialect')"
        :aria-label="`${file.name}: ${t('filePanel.fileDialect')}`"
        @click.stop
      >{{ dialectLabel }}</button>
    </NDropdown>

    <NDropdown trigger="click" :options="contextMenuOptions" @select="handleContextAction">
      <button type="button" class="file-menu icon-button" :aria-label="`${file.name}: ${t('workspace.fileActions')}`" :title="t('workspace.fileActions')"><i-mdi-dots-vertical /></button>
    </NDropdown>
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
