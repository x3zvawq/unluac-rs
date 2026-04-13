<script setup lang="ts">
/**
 * 文件树中的单个文件夹节点（递归组件）。
 *
 * 渲染文件夹标题行（可点击折叠/展开）和其子节点列表。
 * 子文件夹递归使用自身，子文件委托给 FileListItem。
 * 右键菜单提供"移除目录"操作。
 */

import { computed, shallowRef } from 'vue'
import { useI18n } from 'vue-i18n'

const { t } = useI18n()

const props = defineProps<{
  node: {
    type: 'folder'
    name: string
    path: string
    children: Array<
      | { type: 'folder'; name: string; path: string; children: any[] }
      | { type: 'file'; entry: import('@/types/decompiler').FileEntry }
    >
  }
  depth: number
  collapsed: Map<string, boolean>
  selectedFileId: string | null
}>()

const emit = defineEmits<{
  toggle: [path: string]
  select: [id: string]
  remove: [id: string]
  removeFolder: [path: string]
  recompile: [id: string]
}>()

const isCollapsed = computed(() => props.collapsed.get(props.node.path) ?? false)

/**
 * 递归统计文件夹下的文件总数。
 * 用于在文件夹标题后显示文件计数。
 */
const fileCount = computed(() => {
  function count(children: typeof props.node.children): number {
    let n = 0
    for (const child of children) {
      if (child.type === 'file') n++
      else n += count(child.children)
    }
    return n
  }
  return count(props.node.children)
})

// ── 目录右键菜单 ──
const showContextMenu = shallowRef(false)
const contextMenuX = shallowRef(0)
const contextMenuY = shallowRef(0)

const contextMenuOptions = computed(() => [
  { label: t('filePanel.folderContextMenu.removeFolder'), key: 'removeFolder' },
])

function openContextMenu(e: MouseEvent) {
  e.preventDefault()
  contextMenuX.value = e.clientX
  contextMenuY.value = e.clientY
  showContextMenu.value = true
}

function handleContextAction(key: string) {
  showContextMenu.value = false
  if (key === 'removeFolder') {
    emit('removeFolder', props.node.path)
  }
}
</script>

<template>
  <!-- 文件夹标题行 -->
  <div
    class="group flex cursor-pointer items-center gap-1 px-3 py-1 text-xs font-medium text-gray-500 transition-colors hover:bg-gray-100 dark:text-gray-400 dark:hover:bg-gray-800"
    :style="{ paddingLeft: `${depth * 12 + 12}px` }"
    @click="emit('toggle', node.path)"
    @contextmenu="openContextMenu"
  >
    <!-- 展开/折叠箭头 -->
    <svg
      xmlns="http://www.w3.org/2000/svg"
      width="12"
      height="12"
      viewBox="0 0 24 24"
      fill="currentColor"
      class="shrink-0 transition-transform"
      :class="{ '-rotate-90': isCollapsed }"
    >
      <path d="M7 10l5 5 5-5z" />
    </svg>
    <!-- 文件夹图标 -->
    <svg
      xmlns="http://www.w3.org/2000/svg"
      width="14"
      height="14"
      viewBox="0 0 24 24"
      fill="none"
      stroke="currentColor"
      stroke-width="2"
      stroke-linecap="round"
      stroke-linejoin="round"
      class="shrink-0 text-yellow-500"
    >
      <path d="M22 19a2 2 0 0 1-2 2H4a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h5l2 3h9a2 2 0 0 1 2 2z" />
    </svg>
    <span class="truncate">{{ node.name }}</span>
    <!-- 文件计数 / hover 时显示移除按钮 -->
    <span class="shrink-0 text-gray-400 group-hover:hidden">{{ fileCount }}</span>
    <button
      class="ml-auto hidden shrink-0 rounded p-0.5 text-gray-400 transition-colors hover:bg-gray-200 hover:text-red-600 group-hover:inline-block dark:text-gray-500 dark:hover:bg-gray-700 dark:hover:text-red-400"
      :title="t('filePanel.folderContextMenu.removeFolder')"
      @click.stop="emit('removeFolder', node.path)"
    >
      <svg xmlns="http://www.w3.org/2000/svg" width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><line x1="18" y1="6" x2="6" y2="18"/><line x1="6" y1="6" x2="18" y2="18"/></svg>
    </button>
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

  <!-- 子节点 -->
  <template v-if="!isCollapsed">
    <template v-for="child in node.children" :key="child.type === 'file' ? child.entry.id : child.path">
      <FileTreeFolder
        v-if="child.type === 'folder'"
        :node="child"
        :depth="depth + 1"
        :collapsed="collapsed"
        :selected-file-id="selectedFileId"
        @toggle="(path: string) => emit('toggle', path)"
        @select="(id: string) => emit('select', id)"
        @remove="(id: string) => emit('remove', id)"
        @remove-folder="(path: string) => emit('removeFolder', path)"
        @recompile="(id: string) => emit('recompile', id)"
      />
      <div v-else :style="{ paddingLeft: `${depth * 12}px` }">
        <FileListItem
          :file="child.entry"
          :selected="child.entry.id === selectedFileId"
          @select="emit('select', child.entry.id)"
          @remove="emit('remove', child.entry.id)"
          @recompile="emit('recompile', child.entry.id)"
        />
      </div>
    </template>
  </template>
</template>
