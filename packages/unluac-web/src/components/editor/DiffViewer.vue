<script setup lang="ts">
/**
 * 对比查看组件。
 *
 * 使用 @codemirror/merge 提供两个反编译结果的并排 diff 视图。
 * 用户从顶部下拉框选择左右文件，组件自动展示差异。
 * 支持深色/浅色主题切换。
 */

import { StreamLanguage } from '@codemirror/language'
import { lua } from '@codemirror/legacy-modes/mode/lua'
import { MergeView } from '@codemirror/merge'
import { EditorState } from '@codemirror/state'
import { oneDark } from '@codemirror/theme-one-dark'
import { EditorView, lineNumbers } from '@codemirror/view'
import {
  computed,
  inject,
  onUnmounted,
  type ShallowRef,
  shallowRef,
  useTemplateRef,
  watch,
} from 'vue'
import { useI18n } from 'vue-i18n'
import { useTheme } from '@/composables/useTheme'
import { useFilesStore } from '@/stores/files'

const { t } = useI18n()
const filesStore = useFilesStore()
const { isDark } = useTheme()

const containerRef = useTemplateRef<HTMLDivElement>('diffContainer')
let mergeViewInstance: MergeView | null = null

/** 左右选中的文件 id */
const leftFileId = shallowRef<string | null>(null)
const rightFileId = shallowRef<string | null>(null)

/**
 * 外部触发对比时的目标文件 id（由 MainContent provide）。
 * 收到后设为右侧文件。
 */
const compareTargetId = inject<ShallowRef<string | null>>('compareTargetId', shallowRef(null))

watch(
  compareTargetId,
  (id) => {
    if (id) rightFileId.value = id
  },
  { immediate: true },
)

/** 可选文件列表 —— 只列出已反编译成功的文件 */
const fileOptions = computed(() =>
  filesStore.files
    .filter((f) => f.status === 'success' && f.result)
    .map((f) => ({ label: f.name, value: f.id })),
)

const leftContent = computed(
  () => filesStore.files.find((f) => f.id === leftFileId.value)?.result ?? '',
)
const rightContent = computed(
  () => filesStore.files.find((f) => f.id === rightFileId.value)?.result ?? '',
)

/** 两侧都选中有效文件时才渲染 diff */
const canDiff = computed(
  () =>
    leftFileId.value !== null &&
    rightFileId.value !== null &&
    leftContent.value !== '' &&
    rightContent.value !== '',
)

function createExtensions(dark: boolean) {
  const exts = [
    EditorView.editable.of(false),
    EditorState.readOnly.of(true),
    lineNumbers(),
    StreamLanguage.define(lua),
    EditorView.theme({
      '&': { height: '100%' },
      '.cm-scroller': { overflow: 'auto' },
    }),
  ]
  if (dark) exts.push(oneDark)
  return exts
}

function buildMergeView() {
  destroyMergeView()
  if (!containerRef.value || !canDiff.value) return

  const exts = createExtensions(isDark.value)
  mergeViewInstance = new MergeView({
    a: { doc: leftContent.value, extensions: exts },
    b: { doc: rightContent.value, extensions: exts },
    parent: containerRef.value,
    collapseUnchanged: { margin: 3, minSize: 4 },
  })
}

function destroyMergeView() {
  mergeViewInstance?.destroy()
  mergeViewInstance = null
}

// 文件选择或内容变化时重建 diff
watch([leftFileId, rightFileId], () => {
  buildMergeView()
})

// 主题变化时重建
watch(isDark, () => {
  if (canDiff.value) buildMergeView()
})

// 当前选中的文件变化时，自动设定为左侧（方便快速对比）
watch(
  () => filesStore.selectedFileId,
  (id) => {
    if (id && filesStore.files.find((f) => f.id === id)?.status === 'success') {
      leftFileId.value = id
    }
  },
  { immediate: true },
)

onUnmounted(() => {
  destroyMergeView()
})
</script>

<template>
  <div class="flex h-full flex-col">
    <!-- 文件选择器栏 -->
    <div
      class="flex shrink-0 items-center gap-3 border-b border-gray-200 px-3 py-1.5 dark:border-gray-700"
    >
      <div class="flex items-center gap-1.5">
        <span class="text-xs text-gray-500 dark:text-gray-400">{{ t('diff.left') }}:</span>
        <NSelect
          :value="leftFileId"
          :options="fileOptions"
          size="tiny"
          class="w-44"
          clearable
          :placeholder="t('diff.selectFile')"
          @update:value="(v: string | null) => (leftFileId = v)"
        />
      </div>
      <span class="text-xs text-gray-400">↔</span>
      <div class="flex items-center gap-1.5">
        <span class="text-xs text-gray-500 dark:text-gray-400">{{ t('diff.right') }}:</span>
        <NSelect
          :value="rightFileId"
          :options="fileOptions"
          size="tiny"
          class="w-44"
          clearable
          :placeholder="t('diff.selectFile')"
          @update:value="(v: string | null) => (rightFileId = v)"
        />
      </div>
    </div>

    <!-- Diff 视图 -->
    <div class="relative min-h-0 flex-1">
      <div
        v-if="!canDiff"
        class="flex h-full items-center justify-center"
      >
        <NEmpty :description="t('diff.hint')" />
      </div>
      <div
        v-show="canDiff"
        ref="diffContainer"
        class="h-full w-full overflow-hidden text-sm [&_.cm-mergeView]:h-full"
      />
    </div>
  </div>
</template>
