<script setup lang="ts">
/**
 * 对比查看组件。
 *
 * 支持两种模式：
 * 1. 「已修改 vs 原始结果」：对比当前文件的手动编辑与原始反编译源码；
 * 2. 「双文件对比」：对比工作区内任意两个已反编译/源码文件。
 */

import { StreamLanguage } from '@codemirror/language'
import { lua } from '@codemirror/legacy-modes/mode/lua'
import { MergeView } from '@codemirror/merge'
import { EditorState } from '@codemirror/state'
import { EditorView, lineNumbers } from '@codemirror/view'
import { computed, onUnmounted, shallowRef, useTemplateRef, watch } from 'vue'
import { useI18n } from 'vue-i18n'
import { useTheme } from '@/composables/useTheme'
import { useFilesStore } from '@/stores/files'
import { createUnluacEditorTheme } from '@/utils/editorTheme'

const props = defineProps<{
  initialRightFileId?: string | null
}>()

const emit = defineEmits<{
  close: []
}>()

const { t } = useI18n()
const filesStore = useFilesStore()
const { isDark } = useTheme()

const containerRef = useTemplateRef<HTMLDivElement>('diffContainer')
let mergeViewInstance: MergeView | null = null

const diffMode = shallowRef<'files' | 'edits'>('files')
const leftFileId = shallowRef<string | null>(null)
const rightFileId = shallowRef<string | null>(null)

const selectedFile = computed(() => filesStore.selectedFile)
const selectedHasEdits = computed(() => selectedFile.value?.editedResult !== undefined)

const fileOptions = computed(() =>
  filesStore.files
    .filter((f) => (f.status === 'success' || f.status === 'skipped') && f.result !== undefined)
    .map((f) => ({ label: f.relativePath, value: f.id })),
)

const leftContent = computed(() => {
  if (diffMode.value === 'edits') return selectedFile.value?.result ?? ''
  const f = filesStore.files.find((item) => item.id === leftFileId.value)
  return f ? (f.editedResult ?? f.result ?? '') : ''
})

const rightContent = computed(() => {
  if (diffMode.value === 'edits') return selectedFile.value?.editedResult ?? ''
  const f = filesStore.files.find((item) => item.id === rightFileId.value)
  return f ? (f.editedResult ?? f.result ?? '') : ''
})

const canDiff = computed(() => {
  if (diffMode.value === 'edits') {
    return selectedHasEdits.value && selectedFile.value?.result !== undefined
  }
  return leftFileId.value !== null && rightFileId.value !== null
})

function createExtensions(dark: boolean) {
  return [
    EditorView.editable.of(false),
    EditorState.readOnly.of(true),
    lineNumbers(),
    StreamLanguage.define(lua),
    createUnluacEditorTheme(dark),
  ]
}

function destroyMergeView() {
  mergeViewInstance?.destroy()
  mergeViewInstance = null
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

watch(
  [() => props.initialRightFileId, () => filesStore.selectedFileId, fileOptions],
  ([targetRight, selectedId, opts]) => {
    if (targetRight) {
      diffMode.value = 'files'
      rightFileId.value = targetRight
      const other =
        selectedId && selectedId !== targetRight
          ? selectedId
          : (opts.find((o) => o.value !== targetRight)?.value ?? targetRight)
      leftFileId.value = other
      return
    }
    if (selectedHasEdits.value && opts.length < 2) {
      diffMode.value = 'edits'
      return
    }
    if (!leftFileId.value && selectedId && opts.some((o) => o.value === selectedId)) {
      leftFileId.value = selectedId
    }
    if (!rightFileId.value && opts.length >= 2) {
      rightFileId.value = opts.find((o) => o.value !== leftFileId.value)?.value ?? opts[0].value
    } else if (selectedHasEdits.value && !rightFileId.value) {
      diffMode.value = 'edits'
    }
  },
  { immediate: true },
)

watch([diffMode, leftContent, rightContent, isDark], () => {
  buildMergeView()
})

onUnmounted(() => {
  destroyMergeView()
})
</script>

<template>
  <div class="flex h-full flex-col">
    <div
      class="code-toolbar gap-2"
      style="border-bottom: 1px solid var(--app-border); background: var(--app-bg-alt)"
    >
      <div class="segmented-toggle">
        <button
          v-if="selectedHasEdits"
          type="button"
          class="segmented-btn"
          :class="{ active: diffMode === 'edits' }"
          @click="diffMode = 'edits'"
        >
          {{ t('diff.editsVsOriginal') }}
        </button>
        <button
          type="button"
          class="segmented-btn"
          :class="{ active: diffMode === 'files' }"
          @click="diffMode = 'files'"
        >
          {{ t('diff.compareFiles') }}
        </button>
      </div>

      <template v-if="diffMode === 'files'">
        <div class="flex items-center gap-1.5">
          <span class="text-xs" style="color: var(--app-text-secondary)">{{ t('diff.left') }}:</span>
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
        <span class="text-xs" style="color: var(--app-text-dim)">↔</span>
        <div class="flex items-center gap-1.5">
          <span class="text-xs" style="color: var(--app-text-secondary)">{{ t('diff.right') }}:</span>
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
      </template>
      <span v-else class="text-xs" style="color: var(--app-text-secondary)">
        {{ selectedFile?.relativePath }}
      </span>

      <NButton
        quaternary
        size="tiny"
        class="ml-auto"
        :aria-label="t('tabs.contextMenu.close')"
        @click="emit('close')"
      >
        <template #icon><i-mdi-close /></template>
      </NButton>
    </div>

    <div class="relative min-h-0 flex-1">
      <div v-if="!canDiff" class="flex h-full items-center justify-center">
        <NEmpty :description="t('diff.hint')" />
      </div>
      <div
        v-show="canDiff"
        ref="diffContainer"
        class="h-full w-full overflow-hidden text-sm [&_.cm-mergeView]:h-full [&_.cm-mergeViewEditors]:h-full"
      />
    </div>
  </div>
</template>
