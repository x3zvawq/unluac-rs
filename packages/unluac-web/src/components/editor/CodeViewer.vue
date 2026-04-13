<script setup lang="ts">
/**
 * 代码查看/编辑组件。
 *
 * 职责：使用 CodeMirror 6 展示反编译后的 Lua 源码，允许用户编辑。
 * - 可编辑模式，修改后存入 editedResult
 * - 支持深色/浅色主题
 * - 提供复制、下载等工具栏操作
 * - 修改后在工具栏显示黄色警告标记和 Refresh 恢复按钮
 *
 * 选择 CodeMirror 6 而非 Monaco 的原因：
 * - 体积小约 10 倍（~130KB vs ~2MB gzip）
 * - 移动端表现更好
 */

import { defaultHighlightStyle, StreamLanguage, syntaxHighlighting } from '@codemirror/language'
import { lua } from '@codemirror/legacy-modes/mode/lua'
import { highlightSelectionMatches, search, searchKeymap } from '@codemirror/search'
import { Compartment, EditorState, type Extension, type Range, StateEffect, StateField } from '@codemirror/state'
import { oneDark } from '@codemirror/theme-one-dark'
import {
  Decoration,
  type DecorationSet,
  EditorView,
  highlightActiveLine,
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
import { useTheme } from '@/composables/useTheme'
import { useFilesStore } from '@/stores/files'

const { t } = useI18n()
const filesStore = useFilesStore()
const { isDark } = useTheme()
const dialog = useDialog()

/**
 * 行范围高亮 —— 由外部（MainContent）通过 provide/inject 传入。
 * 格式 { from: 行号, to: 行号 }（1-based），null 表示清除高亮。
 */
const highlightRange = inject<ShallowRef<{ from: number; to: number } | null>>(
  'highlightLineRange',
  shallowRef(null),
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

/** 高亮行的背景色样式 */
const highlightLineTheme = EditorView.baseTheme({
  '.cm-highlighted-line': {
    backgroundColor: 'rgba(99, 102, 241, 0.12)',
  },
})

// 注册快捷键回调
const shortcutActions =
  inject<ShallowRef<Record<string, (() => void) | undefined>>>('shortcutActions')!
shortcutActions.value = { ...shortcutActions.value, downloadCurrent: () => downloadFile() }

const editorContainer = useTemplateRef<HTMLDivElement>('editorContainer')
let editorView: EditorView | null = null

const copied = shallowRef(false)

const selectedFile = computed(() => filesStore.selectedFile)

const showPlaceholder = computed(
  () => !selectedFile.value || selectedFile.value.status === 'pending',
)

const showError = computed(() => selectedFile.value?.status === 'error')

const showCode = computed(
  () =>
    (selectedFile.value?.status === 'success' || selectedFile.value?.status === 'skipped') &&
    selectedFile.value.result,
)

const codeContent = computed(() => {
  const file = selectedFile.value
  if (!file) return ''
  // 如果有手动编辑结果则展示编辑版本
  return file.editedResult ?? file.result ?? ''
})

/** 当前文件是否被用户修改过 */
const isModified = computed(() => selectedFile.value?.editedResult !== undefined)

/**
 * 内部标记：正在由程序替换文档内容（文件切换 / 恢复原始版本），
 * 此时 updateListener 不应将变更写入 editedResult。
 */
let programmaticUpdate = false

/** 用 Compartment 管理主题扩展，切换时只重配置而非重建编辑器 */
const themeCompartment = new Compartment()

function themeExtension(dark: boolean): Extension {
  return dark ? oneDark : syntaxHighlighting(defaultHighlightStyle)
}

function createExtensions(dark: boolean) {
  const extensions = [
    lineNumbers(),
    highlightActiveLine(),
    highlightSelectionMatches(),
    search(),
    keymap.of(searchKeymap),
    StreamLanguage.define(lua),
    highlightField,
    highlightLineTheme,
    EditorView.theme({
      '&': { height: '100%' },
      '.cm-scroller': { overflow: 'auto' },
    }),
    themeCompartment.of(themeExtension(dark)),
    // 用户编辑时将变更存入 editedResult
    EditorView.updateListener.of((update) => {
      if (!update.docChanged || programmaticUpdate) return
      const fileId = selectedFile.value?.id
      if (!fileId) return
      const newText = update.state.doc.toString()
      // 如果编辑后的内容与原始结果一致，清除 editedResult
      if (newText === selectedFile.value?.result) {
        filesStore.clearEditedResult(fileId)
      } else {
        filesStore.updateEditedResult(fileId, newText)
      }
    }),
  ]
  return extensions
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
}

// 代码内容变化时更新编辑器（文件切换触发）
watch(codeContent, (newCode) => {
  if (!editorView) return
  // 如果编辑器当前内容已经一致则跳过
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
})

// 主题变化时通过 Compartment 热切换，保留滚动位置和编辑状态
watch(isDark, (dark) => {
  if (!editorView) return
  editorView.dispatch({
    effects: themeCompartment.reconfigure(themeExtension(dark)),
  })
})

// 外部高亮行范围变化时更新编辑器装饰 + 滚动到目标行
watch(highlightRange, (range) => {
  if (!editorView) return
  editorView.dispatch({ effects: setHighlightEffect.of(range) })
  if (range) {
    const line = editorView.state.doc.line(Math.min(range.from, editorView.state.doc.lines))
    editorView.dispatch({
      effects: EditorView.scrollIntoView(line.from, { y: 'start', yMargin: 40 }),
    })
  }
})

onMounted(() => {
  initEditor()
})

onUnmounted(() => {
  editorView?.destroy()
  editorView = null
})

async function copyToClipboard() {
  if (!codeContent.value) return
  try {
    await navigator.clipboard.writeText(codeContent.value)
    copied.value = true
    setTimeout(() => {
      copied.value = false
    }, 2000)
  } catch {
    // fallback
    const textarea = document.createElement('textarea')
    textarea.value = codeContent.value
    document.body.appendChild(textarea)
    textarea.select()
    document.execCommand('copy')
    document.body.removeChild(textarea)
    copied.value = true
    setTimeout(() => {
      copied.value = false
    }, 2000)
  }
}

function downloadFile() {
  if (!codeContent.value) return
  // 下载当前展示的内容（可能是编辑后的）
  const blob = new Blob([codeContent.value], { type: 'text/x-lua' })
  const url = URL.createObjectURL(blob)
  const a = document.createElement('a')
  a.href = url
  a.download = `${selectedFile.value!.name.replace(/\.[^.]+$/, '')}.lua`
  a.click()
  URL.revokeObjectURL(url)
}

function downloadAll() {
  const successFiles = filesStore.files.filter((f) => f.status === 'success' && f.result)
  if (successFiles.length === 0) return

  // 单文件直接下载
  if (successFiles.length === 1) {
    const file = successFiles[0]
    const blob = new Blob([file.result!], { type: 'text/x-lua' })
    const url = URL.createObjectURL(blob)
    const a = document.createElement('a')
    a.href = url
    a.download = `${file.name.replace(/\.[^.]+$/, '')}.lua`
    a.click()
    URL.revokeObjectURL(url)
    return
  }

  // 多文件：逐个下载（后续可替换为 zip 打包）
  for (const file of successFiles) {
    const blob = new Blob([file.result!], { type: 'text/x-lua' })
    const url = URL.createObjectURL(blob)
    const a = document.createElement('a')
    a.href = url
    a.download = `${file.name.replace(/\.[^.]+$/, '')}.lua`
    a.click()
    URL.revokeObjectURL(url)
  }
}

/** 恢复原始反编译结果（二次确认） */
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
</script>

<template>
  <div class="flex h-full flex-col">
    <!-- 工具栏 -->
    <div
      v-if="showCode"
      class="flex shrink-0 items-center gap-1 px-3 py-1.5"
      style="border-bottom: 1px solid var(--app-border)"
    >
      <span class="flex-1 truncate text-sm" style="color: var(--app-text-secondary)">
        {{ selectedFile?.name }}
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
          <NButton quaternary size="tiny" @click="restoreOriginal">
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
          <NButton quaternary size="tiny" @click="copyToClipboard">
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
          <NButton quaternary size="tiny" @click="downloadFile">
            <template #icon>
              <NIcon>
                <svg xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4"/><polyline points="7 10 12 15 17 10"/><line x1="12" y1="15" x2="12" y2="3"/></svg>
              </NIcon>
            </template>
          </NButton>
        </template>
        {{ t('codeView.download') }}
      </NTooltip>

      <NTooltip v-if="filesStore.files.filter(f => f.status === 'success').length > 1">
        <template #trigger>
          <NButton quaternary size="tiny" @click="downloadAll">
            <template #icon>
              <NIcon>
                <svg xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4"/><polyline points="7 10 12 15 17 10"/><line x1="12" y1="15" x2="12" y2="3"/><line x1="3" y1="21" x2="21" y2="21"/></svg>
              </NIcon>
            </template>
          </NButton>
        </template>
        {{ t('codeView.downloadAll') }}
      </NTooltip>
    </div>

    <!-- 编辑器区域 -->
    <div class="relative min-h-0 flex-1">
      <!-- 占位符 -->
      <div
        v-if="showPlaceholder"
        class="flex h-full items-center justify-center"
      >
        <NEmpty :description="t('codeView.placeholder')" />
      </div>

      <!-- 错误展示 -->
      <div
        v-else-if="showError"
        class="flex h-full items-center justify-center p-8"
      >
        <NAlert type="error" :title="t('codeView.error')">
          {{ selectedFile?.error }}
        </NAlert>
      </div>

      <!-- CodeMirror -->
      <div
        v-show="showCode"
        ref="editorContainer"
        class="h-full"
      />

      <!-- 加载中 -->
      <div
        v-if="selectedFile?.status === 'processing'"
        class="flex h-full items-center justify-center"
      >
        <div class="flex items-center gap-2 text-sm text-gray-500">
          <svg class="h-4 w-4 animate-spin" xmlns="http://www.w3.org/2000/svg" fill="none" viewBox="0 0 24 24">
            <circle class="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" stroke-width="4" />
            <path class="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4z" />
          </svg>
          Decompiling...
        </div>
      </div>
    </div>
  </div>
</template>
