<script setup lang="ts">
/**
 * 主内容区容器——上下双栏布局。
 *
 * 上栏：VS Code 风格文件标签栏 + CodeViewer / DiffViewer。
 * 下栏：结构分析面板，支持「函数大纲（Outline）」与「Proto 引用图（Graph）」无缝切换，
 *       点击进入任意 proto 的 CFG 视图，并始终使用精确生成的行号定位源码。
 */

import { computed, defineAsyncComponent, inject, type ShallowRef, shallowRef, watch } from 'vue'
import { useI18n } from 'vue-i18n'

const ProtoGraph = defineAsyncComponent(() => import('@/components/analysis/ProtoGraph.vue'))
const ProtoOutline = defineAsyncComponent(() => import('@/components/analysis/ProtoOutline.vue'))
const CfgViewer = defineAsyncComponent(() => import('@/components/analysis/CfgViewer.vue'))
const CodeViewer = defineAsyncComponent(() => import('@/components/editor/CodeViewer.vue'))
const DiffViewer = defineAsyncComponent(() => import('@/components/editor/DiffViewer.vue'))

import type { useDecompiler } from '@/composables/useDecompiler'
import { useResizable } from '@/composables/useResizable'
import { useFilesStore } from '@/stores/files'
import type { ProtoConstant } from '@/types/decompiler'

const LARGE_PROTO_GRAPH_THRESHOLD = 120

const { t } = useI18n()
const filesStore = useFilesStore()
const decompiler = inject<ReturnType<typeof useDecompiler>>('decompiler')!
const shortcutActions =
  inject<ShallowRef<Record<string, ((...args: any[]) => void) | undefined>>>('shortcutActions')!

const isMobile = inject<ShallowRef<boolean>>('isMobile')!
const analysisOpen = shallowRef(!isMobile.value)
const constantsOpen = shallowRef(false)
const analyzing = shallowRef(false)
const analysisError = shallowRef<string | null>(null)
const selectedProtoId = shallowRef<number | null>(null)

/** 上栏视图：源码编辑或并排 Diff 对比 */
const showDiff = shallowRef(false)
const diffRightFileId = shallowRef<string | null>(null)

function openCompare(targetFileId?: string) {
  diffRightFileId.value = targetFileId ?? null
  showDiff.value = true
}

shortcutActions.value = {
  ...shortcutActions.value,
  openCompare,
}

// ── 文件标签栏右键菜单 ──
const tabContextShow = shallowRef(false)
const tabContextX = shallowRef(0)
const tabContextY = shallowRef(0)
const tabContextFileId = shallowRef<string | null>(null)

const tabContextOptions = computed(() => [
  { label: t('tabs.contextMenu.close'), key: 'close' },
  { label: t('tabs.contextMenu.closeOthers'), key: 'closeOthers' },
  { label: t('tabs.contextMenu.closeRight'), key: 'closeRight' },
  { type: 'divider', key: 'd1' },
  { label: t('tabs.contextMenu.closeAll'), key: 'closeAll' },
])

function openTabContextMenu(e: MouseEvent, fileId: string) {
  e.preventDefault()
  tabContextFileId.value = fileId
  tabContextX.value = e.clientX
  tabContextY.value = e.clientY
  tabContextShow.value = true
}

function handleTabContextAction(key: string) {
  tabContextShow.value = false
  const targetId = tabContextFileId.value
  if (!targetId) return
  switch (key) {
    case 'close':
      filesStore.closeTab(targetId)
      break
    case 'closeOthers':
      filesStore.closeOtherTabs(targetId)
      break
    case 'closeRight':
      filesStore.closeTabsToRight(targetId)
      break
    case 'closeAll':
      filesStore.closeAllTabs()
      break
  }
}

const {
  size: bottomHeight,
  dragging: bottomDragging,
  onPointerDown: onBottomPointerDown,
} = useResizable({
  direction: 'vertical',
  initialSize: 300,
  minSize: 100,
  maxSize: 800,
  reverse: true,
  storageKey: 'unluac-bottom-height',
})

/** 下栏视图：'protos'（支持 graph / outline 切换）或 'cfg' */
const analysisView = shallowRef<'protos' | 'cfg'>('protos')
const protoDisplayMode = shallowRef<'graph' | 'outline'>('graph')

const {
  size: constantsPanelWidth,
  dragging: constantsDragging,
  onPointerDown: onConstantsPointerDown,
} = useResizable({
  direction: 'horizontal',
  initialSize: 268,
  minSize: 170,
  maxSize: 500,
  storageKey: 'unluac-constants-width',
})

const activeProtoForConstants = computed(() => {
  if (!richResult.value || richResult.value.protos.length === 0) return null
  if (selectedProtoId.value !== null) {
    return richResult.value.protos[selectedProtoId.value] ?? null
  }
  return richResult.value.protos[0]
})

const constantsList = computed<ProtoConstant[]>(
  () => activeProtoForConstants.value?.constants ?? [],
)

const constantsProtoName = computed(() => {
  const proto = activeProtoForConstants.value
  if (!proto) return ''
  return (
    proto.name ?? (proto.id === 0 ? `${t('analysis.protoGraph.root')} #0` : `Proto #${proto.id}`)
  )
})

const instrMode = shallowRef<'low-ir' | 'bytecode'>('low-ir')

const highlightLineRange = inject<
  ShallowRef<{ fileId: string; from: number; to: number; seq: number } | null>
>('highlightLineRange', shallowRef(null))
const jumpToFileLine = inject<((fileId: string, from: number, to?: number) => void) | null>(
  'jumpToFileLine',
  null,
)

const selectedFile = computed(() => filesStore.selectedFile)
const richResult = computed(() => selectedFile.value?.richResult ?? null)

const selectedCfg = computed(() => {
  if (selectedProtoId.value === null || !richResult.value) return null
  return richResult.value.cfgs[selectedProtoId.value] ?? null
})

const hasAnalysisData = computed(
  () => richResult.value !== null && richResult.value.protos.length > 0,
)

const openFiles = computed(() => filesStore.openFiles)

watch(
  () => {
    const file = selectedFile.value
    return analysisOpen.value && file?.status === 'success' && !file.richResult
      ? `${file.id}:${file.revision}`
      : null
  },
  async (key, _, onCleanup) => {
    analyzing.value = false
    analysisError.value = null
    const file = selectedFile.value
    if (!key || !file?.resultOptions) return
    const controller = new AbortController()
    onCleanup(() => controller.abort())
    analyzing.value = true
    try {
      const bytes = new Uint8Array(file.bytes)
      const result = await decompiler.decompileRich(
        file.id,
        bytes,
        file.resultOptions,
        controller.signal,
      )
      if (!controller.signal.aborted && filesStore.isCurrent(file.id, file.revision)) {
        filesStore.updateRichResult(file.id, result)
        // 超大 proto 树自动切到大纲视图，避免一次性布局数百上千节点造成卡顿
        protoDisplayMode.value =
          result.protos.length > LARGE_PROTO_GRAPH_THRESHOLD ? 'outline' : 'graph'
      }
    } catch (err) {
      if (!controller.signal.aborted) {
        analysisError.value = err instanceof Error ? err.message : String(err)
      }
    } finally {
      if (!controller.signal.aborted) analyzing.value = false
    }
  },
  { immediate: true },
)

function onSelectProto(protoId: number) {
  selectedProtoId.value = protoId
  analysisView.value = 'cfg'
}

/** 跳转到生成源码的精确起止行（优先 generatedLineStart/End，兼容 stripped 字节码） */
function onJumpToSource(protoId: number) {
  const file = selectedFile.value
  const proto = richResult.value?.protos[protoId]
  if (!file || !proto) return
  showDiff.value = false
  const start =
    proto.generatedLineStart && proto.generatedLineStart > 0
      ? proto.generatedLineStart
      : proto.lineStart
  const end =
    proto.generatedLineStart && proto.generatedLineStart > 0
      ? (proto.generatedLineEnd ?? start)
      : proto.lineEnd || start
  if (start > 0) {
    if (jumpToFileLine) {
      jumpToFileLine(file.id, start, end)
    } else {
      highlightLineRange.value = {
        fileId: file.id,
        from: start,
        to: end,
        seq: Date.now(),
      }
    }
  }
}

function backToProtos() {
  analysisView.value = 'protos'
  selectedProtoId.value = null
}

watch(
  () => `${selectedFile.value?.id}:${selectedFile.value?.revision}`,
  () => {
    selectedProtoId.value = null
    if (highlightLineRange.value?.fileId !== selectedFile.value?.id) {
      highlightLineRange.value = null
    }
    analysisView.value = 'protos'
    analysisError.value = null
    const protosLen = selectedFile.value?.richResult?.protos.length ?? 0
    protoDisplayMode.value = protosLen > LARGE_PROTO_GRAPH_THRESHOLD ? 'outline' : 'graph'
    if (!selectedFile.value) showDiff.value = false
  },
)
</script>

<template>
  <main class="main-content flex min-w-0 flex-1 flex-col">
    <!-- ═══ 上栏：文件标签 + 源码 / Diff ═══ -->
    <div class="flex min-h-0 flex-1 flex-col">
      <div
        v-if="openFiles.length"
        class="file-tabs"
        :aria-label="t('filePanel.title')"
        style="border-bottom: 1px solid var(--app-border); background: var(--app-bg-alt)"
      >
        <div
          v-for="file in openFiles"
          :key="file.id"
          class="file-tab"
          :class="{ active: file.id === filesStore.selectedFileId }"
          @contextmenu.prevent="openTabContextMenu($event, file.id)"
        >
          <button
            class="tab-select"
            :aria-pressed="file.id === filesStore.selectedFileId"
            @click="showDiff = false; filesStore.selectFile(file.id)"
          >
            <i-mdi-code-braces />
            <span class="max-w-40 truncate">{{ file.name }}</span>
            <span v-if="file.editedResult !== undefined" class="modified-dot" />
          </button>
          <button
            class="tab-close icon-button"
            :aria-label="`${t('tabs.contextMenu.close')}: ${file.name}`"
            @click="filesStore.closeTab(file.id)"
          >
            <i-mdi-close />
          </button>
        </div>
      </div>

      <NDropdown
        trigger="manual"
        placement="bottom-start"
        :options="tabContextOptions"
        :show="tabContextShow"
        :x="tabContextX"
        :y="tabContextY"
        @select="handleTabContextAction"
        @clickoutside="tabContextShow = false"
      />

      <div class="min-h-0 flex-1">
        <WelcomeView v-if="!selectedFile" />
        <DiffViewer
          v-else-if="showDiff"
          :initial-right-file-id="diffRightFileId"
          @close="showDiff = false"
        />
        <CodeViewer v-else @open-diff="openCompare()" />
      </div>
    </div>

    <template v-if="selectedFile?.status === 'success'">
      <div
        v-if="analysisOpen"
        class="resize-handle shrink-0 cursor-row-resize"
        :class="{ 'bg-indigo-400/40': bottomDragging }"
        :style="{ height: '4px', borderTop: '1px solid var(--app-border)' }"
        @pointerdown="onBottomPointerDown"
      />

      <!-- ═══ 下栏：分析面板 ═══ -->
      <div
        class="flex shrink-0 flex-col"
        :style="{ height: analysisOpen ? `min(${bottomHeight}px, 55dvh)` : '44px' }"
      >
        <div class="analysis-toolbar" style="border-bottom: 1px solid var(--app-border)">
          <button
            class="analysis-toggle"
            :aria-expanded="analysisOpen"
            @click="analysisOpen = !analysisOpen"
          >
            <i-mdi-chevron-down v-if="analysisOpen" />
            <i-mdi-chevron-up v-else />
            {{ t('workspace.analysis') }}
          </button>
          <NButton
            v-if="isMobile && analysisOpen && hasAnalysisData"
            quaternary
            size="tiny"
            :aria-pressed="constantsOpen"
            @click="constantsOpen = !constantsOpen"
          >
            {{ t('analysis.constants.title') }}
          </NButton>

          <template v-if="analysisOpen && analysisView === 'cfg'">
            <NButton quaternary size="tiny" :aria-label="t('tabs.protos')" @click="backToProtos">
              <template #icon>
                <NIcon size="14">
                  <svg xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><polyline points="15 18 9 12 15 6" /></svg>
                </NIcon>
              </template>
            </NButton>
            <span class="text-xs font-medium" style="color: var(--app-text-secondary)">
              {{ t('tabs.cfg') }}
              <template v-if="selectedCfg">
                —
                {{
                  richResult?.protos[selectedProtoId!]?.name ??
                  (selectedProtoId === 0
                    ? `${t('analysis.protoGraph.root')} #0`
                    : `Proto #${selectedProtoId}`)
                }}
              </template>
            </span>
            <span v-if="selectedCfg" class="hidden text-xs sm:inline" style="color: var(--app-text-dim)">
              {{ t('analysis.cfgViewer.blocks') }}: {{ selectedCfg.blocks.length }} ·
              {{ t('analysis.cfgViewer.edges') }}: {{ selectedCfg.edges.length }}
            </span>
            <span class="segmented-toggle ml-auto">
              <button
                type="button"
                class="segmented-btn"
                :class="{ active: instrMode === 'low-ir' }"
                @click="instrMode = 'low-ir'"
              >
                Low-IR
              </button>
              <button
                type="button"
                class="segmented-btn"
                :class="{ active: instrMode === 'bytecode' }"
                @click="instrMode = 'bytecode'"
              >
                {{ t('analysis.cfgViewer.bytecode') }}
              </button>
            </span>
          </template>

          <template v-else-if="analysisOpen">
            <span class="text-xs font-medium" style="color: var(--app-text-secondary)">
              {{ t('tabs.protos') }}
              <span v-if="hasAnalysisData" class="count-badge ml-1">
                {{ richResult!.protos.length }}
              </span>
            </span>
            <span v-if="hasAnalysisData" class="segmented-toggle ml-auto">
              <button
                type="button"
                class="segmented-btn"
                :class="{ active: protoDisplayMode === 'graph' }"
                @click="protoDisplayMode = 'graph'"
              >
                {{ t('analysis.outline.graphView') }}
              </button>
              <button
                type="button"
                class="segmented-btn"
                :class="{ active: protoDisplayMode === 'outline' }"
                @click="protoDisplayMode = 'outline'"
              >
                {{ t('analysis.outline.listView') }}
              </button>
            </span>
          </template>
        </div>

        <div v-if="analysisOpen" class="flex min-h-0 flex-1">
          <template v-if="hasAnalysisData && (!isMobile || constantsOpen)">
            <div
              class="shrink-0 overflow-hidden"
              :style="{
                width: isMobile ? '100%' : `${constantsPanelWidth}px`,
                borderRight: '1px solid var(--app-border)',
              }"
            >
              <ConstantsPanel :constants="constantsList" :proto-name="constantsProtoName" />
            </div>
            <div
              v-if="!isMobile"
              class="resize-handle shrink-0 cursor-col-resize"
              :class="{ 'bg-indigo-400/40': constantsDragging }"
              :style="{ width: '4px' }"
              @pointerdown="onConstantsPointerDown"
            />
          </template>

          <div v-show="!isMobile || !constantsOpen" class="min-w-0 flex-1">
            <div v-if="analyzing" class="flex h-full items-center justify-center">
              <NSpin :description="t('analysis.loading')" />
            </div>
            <div
              v-else-if="analysisError"
              class="flex h-full flex-col items-center justify-center gap-2 p-4"
            >
              <NAlert type="error" :title="t('analysis.error')">
                {{ analysisError }}
              </NAlert>
            </div>
            <div v-else-if="!hasAnalysisData" class="flex h-full items-center justify-center">
              <NEmpty :description="t('analysis.noData')" />
            </div>
            <ProtoOutline
              v-else-if="analysisView === 'protos' && protoDisplayMode === 'outline'"
              :protos="richResult!.protos"
              :failed-protos="richResult!.failedProtos"
              :selected-proto-id="selectedProtoId"
              @select-proto="onSelectProto"
              @jump-to-source="onJumpToSource"
            />
            <ProtoGraph
              v-else-if="analysisView === 'protos'"
              :protos="richResult!.protos"
              :failed-protos="richResult!.failedProtos"
              @select-proto="onSelectProto"
              @jump-to-source="onJumpToSource"
            />
            <CfgViewer
              v-else-if="analysisView === 'cfg'"
              :cfg="selectedCfg"
              :instr-mode="instrMode"
            />
          </div>
        </div>
      </div>
    </template>
  </main>
</template>
