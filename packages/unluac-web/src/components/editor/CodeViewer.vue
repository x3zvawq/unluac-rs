<script setup lang="ts">
/**
 * 代码查看/编辑组件。
 *
 * 职责：使用定制融合主题的 CodeMirror 6 展示并编辑反编译后的 Lua 源码，
 * 搭配顶部工具栏（AI 片段复制、Diff 对比、ZIP 打包导出）与底部 28px IDE 状态栏
 * （方言热切换、预设一键切换、诊断状态徽章、行列体积统计、全局搜索入口）。
 */

import { defaultKeymap, history, historyKeymap } from '@codemirror/commands'
import { StreamLanguage } from '@codemirror/language'
import { lua } from '@codemirror/legacy-modes/mode/lua'
import { highlightSelectionMatches, search, searchKeymap } from '@codemirror/search'
import {
  Compartment,
  EditorState,
  type Extension,
  type Range,
  StateEffect,
  StateField,
} from '@codemirror/state'
import {
  Decoration,
  type DecorationSet,
  EditorView,
  highlightActiveLine,
  highlightActiveLineGutter,
  keymap,
  lineNumbers,
} from '@codemirror/view'
import { useDialog } from 'naive-ui'
import {
  computed,
  inject,
  onMounted,
  onUnmounted,
  type ShallowRef,
  shallowRef,
  useTemplateRef,
  watch,
} from 'vue'
import { useI18n } from 'vue-i18n'
import type { useDecompiler } from '@/composables/useDecompiler'
import { useFileDecompile } from '@/composables/useFileDecompile'
import { useTheme } from '@/composables/useTheme'
import { useFilesStore } from '@/stores/files'
import { useSettingsStore } from '@/stores/settings'
import type { SettingsPresetId, UnluacDialect } from '@/types/decompiler'
import { formatCodeForAi } from '@/utils/aiSnippet'
import { dialectOptions } from '@/utils/dialects'
import { createUnluacEditorTheme } from '@/utils/editorTheme'
import { buildZip, resolveLuaExportPaths } from '@/utils/zip'

const emit = defineEmits<{
  'open-diff': []
}>()

const { t } = useI18n()
const filesStore = useFilesStore()
const settingsStore = useSettingsStore()
const decompiler = inject<ReturnType<typeof useDecompiler>>('decompiler')!
const { changeDialect } = useFileDecompile(decompiler)
const { isDark } = useTheme()
const dialog = useDialog()

const highlightRange = inject<
  ShallowRef<{ fileId: string; from: number; to: number; seq: number } | null>
>('highlightLineRange', shallowRef(null))
const jumpToFileLine = inject<((fileId: string, from: number, to?: number) => void) | null>(
  'jumpToFileLine',
  null,
)

// ── CodeMirror 行高亮 StateField ──
const setHighlightEffect = StateEffect.define<{ from: number; to: number } | null>()
const highlightLineMark = Decoration.line({ class: 'cm-highlighted-line' })

const highlightField: Extension = StateField.define<DecorationSet>({
  create() {
    return Decoration.none
  },
  update(decorations, tr) {
    for (const effect of tr.effects) {
      if (effect.is(setHighlightEffect)) {
        if (!effect.value) return Decoration.none
        const { from, to } = effect.value
        const doc = tr.state.doc
        const marks: Range<Decoration>[] = []
        for (let line = from; line <= Math.min(to, doc.lines); line++) {
          marks.push(highlightLineMark.range(doc.line(line).from))
        }
        return Decoration.set(marks)
      }
    }
    return decorations
  },
  provide: (f) => EditorView.decorations.from(f),
})

// 注册快捷键回调
const shortcutActions =
  inject<ShallowRef<Record<string, ((...args: any[]) => void) | undefined>>>('shortcutActions')!
shortcutActions.value = { ...shortcutActions.value, downloadCurrent: () => downloadFile() }

const editorContainer = useTemplateRef<HTMLDivElement>('editorContainer')
let editorView: EditorView | null = null

const copied = shallowRef(false)
const copiedAi = shallowRef(false)
const wrapLines = shallowRef(false)
const wrapCompartment = new Compartment()
const themeCompartment = new Compartment()

const selectedFile = computed(() => filesStore.selectedFile)

const showPlaceholder = computed(
  () => !selectedFile.value || selectedFile.value.status === 'pending',
)
const showError = computed(() => selectedFile.value?.status === 'error')
const showCode = computed(
  () =>
    (selectedFile.value?.status === 'success' || selectedFile.value?.status === 'skipped') &&
    selectedFile.value.result !== undefined,
)

const codeContent = computed(() => {
  const file = selectedFile.value
  if (!file) return ''
  return file.editedResult ?? file.result ?? ''
})

const isModified = computed(() => selectedFile.value?.editedResult !== undefined)

const exportableFiles = computed(() =>
  filesStore.files.filter(
    (f) => (f.status === 'success' || f.status === 'skipped') && f.result !== undefined,
  ),
)

const canOpenDiff = computed(() => isModified.value || exportableFiles.value.length >= 2)

const lineCount = computed(() => {
  const text = codeContent.value
  if (!text) return 0
  let count = 1
  for (let i = 0; i < text.length; i++) {
    if (text.charCodeAt(i) === 10) count++
  }
  return count
})

const formattedSize = computed(() => {
  const bytes = selectedFile.value?.size ?? 0
  if (bytes < 1024) return `${bytes} B`
  if (bytes < 1024 * 1024) return `${(bytes / 1024).toFixed(1)} KB`
  return `${(bytes / (1024 * 1024)).toFixed(1)} MB`
})

const dialectMenu = dialectOptions.map(({ label, value }) => ({ label, key: value }))
const currentDialectLabel = computed(() => {
  const file = selectedFile.value
  if (!file) return ''
  if (file.status === 'skipped') return t('filePanel.sourceTag')
  return dialectOptions.find((o) => o.value === file.dialect)?.label ?? file.dialect
})

const failedProtos = computed(() => selectedFile.value?.richResult?.failedProtos ?? [])
const hasDiagnostics = computed(
  () =>
    selectedFile.value?.richResult?.kind === 'diagnostic-pseudocode' ||
    failedProtos.value.length > 0,
)

const presetItems = computed<{ id: SettingsPresetId; label: string }[]>(() => [
  { id: 'readable', label: t('settings.presets.readable.label') },
  { id: 'exact', label: t('settings.presets.exact.label') },
  { id: 'ai', label: t('settings.presets.ai.label') },
])

let programmaticUpdate = false

function createExtensions(dark: boolean) {
  return [
    lineNumbers(),
    history(),
    keymap.of([...defaultKeymap, ...historyKeymap]),
    wrapCompartment.of(wrapLines.value ? EditorView.lineWrapping : []),
    highlightActiveLine(),
    highlightActiveLineGutter(),
    highlightSelectionMatches(),
    search(),
    keymap.of(searchKeymap),
    StreamLanguage.define(lua),
    highlightField,
    themeCompartment.of(createUnluacEditorTheme(dark)),
    EditorView.updateListener.of((update) => {
      if (!update.docChanged || programmaticUpdate) return
      const fileId = selectedFile.value?.id
      if (!fileId) return
      const newText = update.state.doc.toString()
      if (newText === selectedFile.value?.result) {
        filesStore.clearEditedResult(fileId)
      } else {
        filesStore.updateEditedResult(fileId, newText)
      }
    }),
  ]
}

function applyHighlight(range: { fileId: string; from: number; to: number; seq: number } | null) {
  if (!editorView) return
  if (!range || range.fileId !== selectedFile.value?.id || editorView.state.doc.lines === 0) {
    editorView.dispatch({ effects: setHighlightEffect.of(null) })
    return
  }
  const maxLine = editorView.state.doc.lines
  const from = Math.max(1, Math.min(range.from, maxLine))
  const to = Math.max(from, Math.min(range.to, maxLine))
  const line = editorView.state.doc.line(from)
  editorView.dispatch({
    effects: [
      setHighlightEffect.of({ from, to }),
      EditorView.scrollIntoView(line.from, { y: 'center' }),
    ],
  })
}

function initEditor() {
  if (!editorContainer.value) return
  editorView = new EditorView({
    state: EditorState.create({
      doc: codeContent.value,
      extensions: createExtensions(isDark.value),
    }),
    parent: editorContainer.value,
  })
  applyHighlight(highlightRange.value)
}

watch(
  () => selectedFile.value?.id,
  () => {
    editorView?.setState(
      EditorState.create({ doc: codeContent.value, extensions: createExtensions(isDark.value) }),
    )
    applyHighlight(highlightRange.value)
  },
)

watch(wrapLines, (wrap) =>
  editorView?.dispatch({
    effects: wrapCompartment.reconfigure(wrap ? EditorView.lineWrapping : []),
  }),
)

watch(codeContent, (newCode) => {
  if (!editorView) return
  if (editorView.state.doc.toString() === newCode) return
  programmaticUpdate = true
  editorView.dispatch({
    changes: {
      from: 0,
      to: editorView.state.doc.length,
      insert: newCode,
    },
  })
  programmaticUpdate = false
  applyHighlight(highlightRange.value)
})

watch(isDark, (dark) => {
  if (!editorView) return
  editorView.dispatch({
    effects: themeCompartment.reconfigure(createUnluacEditorTheme(dark)),
  })
})

watch(highlightRange, (range) => {
  applyHighlight(range)
})

onMounted(() => {
  initEditor()
})

onUnmounted(() => {
  editorView?.destroy()
  editorView = null
})

async function writeClipboardText(text: string) {
  try {
    await navigator.clipboard.writeText(text)
  } catch {
    const textarea = document.createElement('textarea')
    textarea.value = text
    document.body.appendChild(textarea)
    textarea.select()
    document.execCommand('copy')
    document.body.removeChild(textarea)
  }
}

async function copyToClipboard() {
  if (!codeContent.value) return
  await writeClipboardText(codeContent.value)
  copiedAi.value = false
  copied.value = true
  setTimeout(() => {
    copied.value = false
  }, 2000)
}

async function copyForAi() {
  const file = selectedFile.value
  if (!file || !codeContent.value) return
  const payload = formatCodeForAi(file, codeContent.value)
  await writeClipboardText(payload)
  copied.value = false
  copiedAi.value = true
  setTimeout(() => {
    copiedAi.value = false
  }, 2000)
}

function downloadFile() {
  if (!codeContent.value || !selectedFile.value) return
  const blob = new Blob([codeContent.value], { type: 'text/x-lua' })
  const url = URL.createObjectURL(blob)
  const a = document.createElement('a')
  a.href = url
  a.download = `${selectedFile.value.name.replace(/\.[^.]+$/, '')}.lua`
  a.click()
  URL.revokeObjectURL(url)
}

function downloadAllZip() {
  const targets = exportableFiles.value
  if (targets.length === 0) return
  if (targets.length === 1) {
    const file = targets[0]
    const blob = new Blob([file.editedResult ?? file.result!], { type: 'text/x-lua' })
    const url = URL.createObjectURL(blob)
    const a = document.createElement('a')
    a.href = url
    a.download = `${file.name.replace(/\.[^.]+$/, '')}.lua`
    a.click()
    URL.revokeObjectURL(url)
    return
  }

  const paths = resolveLuaExportPaths(targets.map((f) => f.relativePath))
  const zipBytes = buildZip(
    targets.map((file, idx) => ({
      path: paths[idx],
      content: file.editedResult ?? file.result!,
    })),
  )
  const blob = new Blob([zipBytes as unknown as BlobPart], { type: 'application/zip' })
  const url = URL.createObjectURL(blob)
  const a = document.createElement('a')
  a.href = url
  a.download = 'unluac-workspace.zip'
  a.click()
  URL.revokeObjectURL(url)
}

function restoreOriginal() {
  const fileId = selectedFile.value?.id
  if (!fileId) return
  dialog.warning({
    title: t('codeView.restoreConfirm'),
    positiveText: 'OK',
    negativeText: t('filePanel.globDialog.cancel'),
    onPositiveClick: () => {
      filesStore.clearEditedResult(fileId)
    },
  })
}

function jumpToFirstDiagnostic() {
  const file = selectedFile.value
  const rich = file?.richResult
  if (!file || !rich) return
  const firstId = failedProtos.value[0]
  if (firstId !== undefined) {
    const proto = rich.protos[firstId]
    const line = proto?.generatedLineStart || proto?.lineStart || 1
    const end = proto?.generatedLineEnd || proto?.lineEnd || line
    jumpToFileLine?.(file.id, line, end)
    return
  }
  const idx = codeContent.value.split('\n').findIndex((l) => l.includes('[unluac error]'))
  if (idx >= 0) jumpToFileLine?.(file.id, idx + 1)
}
</script>

<template>
  <div class="flex h-full flex-col">
    <!-- 工具栏 -->
    <div
      v-if="showCode"
      class="code-toolbar"
      style="border-bottom: 1px solid var(--app-border)"
    >
      <span class="flex-1 truncate text-sm font-medium" style="color: var(--app-text-secondary)">
        {{ t('tabs.code') }} <span class="code-file-path">/ {{ selectedFile?.relativePath }}</span>
      </span>

      <NTooltip>
        <template #trigger>
          <NButton
            quaternary
            size="small"
            :aria-label="t('globalSearch.open')"
            @click="shortcutActions.openGlobalSearch?.()"
          >
            <template #icon><i-mdi-file-search-outline /></template>
          </NButton>
        </template>
        {{ t('globalSearch.openHint') }}
      </NTooltip>

      <NTooltip v-if="canOpenDiff">
        <template #trigger>
          <NButton
            quaternary
            size="small"
            :aria-label="t('tabs.diff')"
            @click="emit('open-diff')"
          >
            <template #icon><i-mdi-file-compare /></template>
          </NButton>
        </template>
        {{ t('diff.openHint') }}
      </NTooltip>

      <NButton
        quaternary
        size="small"
        :aria-label="t('workspace.wrapLines')"
        :title="t('workspace.wrapLines')"
        :aria-pressed="wrapLines"
        @click="wrapLines = !wrapLines"
      >
        <template #icon><i-mdi-wrap /></template>
      </NButton>

      <span v-if="copied || copiedAi" class="copy-feedback" role="status">
        {{ copiedAi ? t('codeView.copiedForAi') : t('codeView.copied') }}
      </span>

      <!-- 已修改警告 -->
      <NTooltip v-if="isModified">
        <template #trigger>
          <span class="flex items-center gap-1 text-xs text-amber-500">
            <svg xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M10.29 3.86L1.82 18a2 2 0 001.71 3h16.94a2 2 0 001.71-3L13.71 3.86a2 2 0 00-3.42 0z"/><line x1="12" y1="9" x2="12" y2="13"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg>
            {{ t('codeView.modified') }}
          </span>
        </template>
        {{ t('codeView.modifiedHint') }}
      </NTooltip>

      <!-- 恢复原始结果 -->
      <NTooltip v-if="isModified">
        <template #trigger>
          <NButton quaternary size="small" :aria-label="t('codeView.restore')" @click="restoreOriginal">
            <template #icon>
              <NIcon>
                <svg xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><polyline points="23 4 23 10 17 10"/><path d="M20.49 15a9 9 0 1 1-2.12-9.36L23 10"/></svg>
              </NIcon>
            </template>
          </NButton>
        </template>
        {{ t('codeView.restore') }}
      </NTooltip>

      <NTooltip>
        <template #trigger>
          <NButton quaternary size="small" :aria-label="t('codeView.copyForAi')" @click="copyForAi">
            <template #icon>
              <NIcon>
                <svg xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M12 3l1.9 5.1L19 10l-5.1 1.9L12 17l-1.9-5.1L5 10l5.1-1.9L12 3z"/><path d="M19 16l.8 2.2L22 19l-2.2.8L19 22l-.8-2.2L16 19l2.2-.8L19 16z"/></svg>
              </NIcon>
            </template>
          </NButton>
        </template>
        {{ copiedAi ? t('codeView.copiedForAi') : t('codeView.copyForAiHint') }}
      </NTooltip>

      <NTooltip>
        <template #trigger>
          <NButton quaternary size="small" :aria-label="t('codeView.copy')" @click="copyToClipboard">
            <template #icon>
              <NIcon>
                <svg xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><rect x="9" y="9" width="13" height="13" rx="2" ry="2"/><path d="M5 15H4a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2h9a2 2 0 0 1 2 2v1"/></svg>
              </NIcon>
            </template>
          </NButton>
        </template>
        {{ copied ? t('codeView.copied') : t('codeView.copy') }}
      </NTooltip>

      <NTooltip>
        <template #trigger>
          <NButton quaternary size="small" :aria-label="t('codeView.download')" @click="downloadFile">
            <template #icon>
              <NIcon>
                <svg xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4"/><polyline points="7 10 12 15 17 10"/><line x1="12" y1="15" x2="12" y2="3"/></svg>
              </NIcon>
            </template>
          </NButton>
        </template>
        {{ t('codeView.download') }}
      </NTooltip>

      <NTooltip v-if="exportableFiles.length > 1">
        <template #trigger>
          <NButton quaternary size="small" :aria-label="t('codeView.downloadAll')" @click="downloadAllZip">
            <template #icon><i-mdi-folder-zip-outline /></template>
          </NButton>
        </template>
        {{ t('codeView.downloadAllZip') }}
      </NTooltip>
    </div>

    <!-- 编辑器区域 -->
    <div class="relative min-h-0 flex-1">
      <div v-if="showPlaceholder" class="flex h-full items-center justify-center">
        <NEmpty :description="t('codeView.placeholder')" />
      </div>

      <div v-else-if="showError" class="flex h-full items-center justify-center p-8">
        <NAlert type="error" :title="t('codeView.error')">
          {{ selectedFile?.error }}
        </NAlert>
      </div>

      <div v-show="showCode" ref="editorContainer" class="h-full" />

      <div
        v-if="selectedFile?.status === 'processing'"
        class="flex h-full items-center justify-center"
      >
        <div class="flex items-center gap-2 text-sm" style="color: var(--app-text-secondary)">
          <svg class="h-4 w-4 animate-spin" xmlns="http://www.w3.org/2000/svg" fill="none" viewBox="0 0 24 24">
            <circle class="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" stroke-width="4" />
            <path class="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
          </svg>
          {{ t('filePanel.status.processing') }}…
        </div>
      </div>
    </div>

    <!-- 底部 28px IDE 状态栏 -->
    <div v-if="showCode && selectedFile" class="ide-status-bar">
      <div class="flex min-w-0 items-center gap-2">
        <NDropdown
          v-if="selectedFile.status === 'success'"
          trigger="click"
          :options="dialectMenu"
          @select="(value: UnluacDialect) => changeDialect(selectedFile!.id, value)"
        >
          <button type="button" class="status-pill status-pill-accent" :title="t('filePanel.fileDialect')">
            {{ currentDialectLabel }}
          </button>
        </NDropdown>
        <span v-else class="status-pill">{{ currentDialectLabel }}</span>

        <button
          v-if="hasDiagnostics"
          type="button"
          class="status-diag-pill"
          :title="t('statusBar.diagnosticHint')"
          @click="jumpToFirstDiagnostic"
        >
          ⚠ {{ failedProtos.length > 0 ? t('statusBar.failedProtos', { count: failedProtos.length }) : t('statusBar.diagnostic') }}
        </button>

        <div class="hidden items-center gap-1 md:flex">
          <button
            v-for="preset in presetItems"
            :key="preset.id"
            type="button"
            class="status-preset-pill"
            :class="{ active: settingsStore.activePreset === preset.id }"
            @click="settingsStore.applyPreset(preset.id)"
          >
            {{ preset.label }}
          </button>
        </div>
      </div>

      <div class="flex shrink-0 items-center gap-2.5">
        <span class="hidden tabular-nums sm:inline">{{ lineCount }} {{ t('statusBar.lines') }} · {{ formattedSize }}</span>
        <span class="hidden uppercase sm:inline">{{ settingsStore.options.parse.stringEncoding }}</span>
        <button
          type="button"
          class="status-pill"
          :title="t('globalSearch.openHint')"
          @click="shortcutActions.openGlobalSearch?.()"
        >
          ⌘⇧F
        </button>
      </div>
    </div>
  </div>
</template>
