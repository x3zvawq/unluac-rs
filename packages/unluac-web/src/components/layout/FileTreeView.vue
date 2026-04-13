<script setup lang="ts">
/**
 * 树形文件列表视图。
 *
 * 当文件有目录结构（relativePath 含 "/"）时，将扁平的 FileEntry[] 转换为
 * 目录树结构渲染。每个目录节点可折叠/展开，文件节点复用 FileListItem 的展示逻辑。
 *
 * 如果所有文件都在根目录（无嵌套），则退化为普通扁平列表。
 */

import { computed, reactive } from 'vue'
import type { FileEntry } from '@/types/decompiler'

interface TreeFolder {
  type: 'folder'
  name: string
  path: string
  children: TreeNode[]
}

interface TreeFile {
  type: 'file'
  entry: FileEntry
}

type TreeNode = TreeFolder | TreeFile

const props = defineProps<{
  files: FileEntry[]
  selectedFileId: string | null
}>()

const emit = defineEmits<{
  select: [id: string]
  remove: [id: string]
  removeFolder: [path: string]
  recompile: [id: string]
}>()

// 记录每个目录的折叠状态，默认展开
const collapsed = reactive(new Map<string, boolean>())

function toggleFolder(path: string) {
  collapsed.set(path, !collapsed.get(path))
}

/** 将扁平文件列表构建为目录树 */
const tree = computed<TreeNode[]>(() => {
  const root: TreeNode[] = []
  // 用 Map 存储已创建的文件夹节点，避免重复创建
  const folderMap = new Map<string, TreeFolder>()

  function ensureFolder(pathParts: string[]): TreeFolder {
    const fullPath = pathParts.join('/')
    const existing = folderMap.get(fullPath)
    if (existing) return existing

    const folder: TreeFolder = {
      type: 'folder',
      name: pathParts[pathParts.length - 1],
      path: fullPath,
      children: [],
    }
    folderMap.set(fullPath, folder)

    if (pathParts.length === 1) {
      root.push(folder)
    } else {
      const parent = ensureFolder(pathParts.slice(0, -1))
      parent.children.push(folder)
    }

    return folder
  }

  for (const file of props.files) {
    const parts = file.relativePath.split('/')
    if (parts.length === 1) {
      // 根目录文件
      root.push({ type: 'file', entry: file })
    } else {
      // 有目录结构：确保父目录存在，文件放入最近的父目录
      const dirParts = parts.slice(0, -1)
      const parent = ensureFolder(dirParts)
      parent.children.push({ type: 'file', entry: file })
    }
  }

  return root
})
</script>

<template>
  <div class="py-1">
    <template v-for="node in tree" :key="node.type === 'file' ? node.entry.id : node.path">
      <!-- 文件夹递归渲染 -->
      <template v-if="node.type === 'folder'">
        <FileTreeFolder
          :node="node"
          :depth="0"
          :collapsed="collapsed"
          :selected-file-id="selectedFileId"
          @toggle="toggleFolder"
          @select="(id: string) => emit('select', id)"
          @remove="(id: string) => emit('remove', id)"
          @remove-folder="(path: string) => emit('removeFolder', path)"
          @recompile="(id: string) => emit('recompile', id)"
        />
      </template>
      <!-- 根目录文件 -->
      <template v-else>
        <FileListItem
          :file="node.entry"
          :selected="node.entry.id === selectedFileId"
          @select="emit('select', node.entry.id)"
          @remove="emit('remove', node.entry.id)"
          @recompile="emit('recompile', node.entry.id)"
        />
      </template>
    </template>
  </div>
</template>
