<script setup lang="ts">
/**
 * 主内容区容器——上下双栏布局。
 *
 * 上栏：VS Code 风格文件标签栏 + CodeViewer，显示反编译后的源码。
 * 下栏：分析面板，默认显示 ProtoGraph；点击某个 proto 进入该 proto 的 CFG 视图，
 *       左上角提供返回按钮回到 ProtoGraph。
 *
 * 分析面板展开后按需获取 richResult，缓存于 FileEntry 上。
 * 编辑器和图视图按需加载，无文件时只显示导入引导。
 */

import {
  computed,
  defineAsyncComponent,
  inject,
  provide,
  shallowRef,
  watch,
  type ShallowRef,
} from 'vue'
import { useI18n } from 'vue-i18n'

const ProtoGraph = defineAsyncComponent(() => import('@/components/analysis/ProtoGraph.vue'))
const CfgViewer = defineAsyncComponent(() => import('@/components/analysis/CfgViewer.vue'))
const CodeViewer = defineAsyncComponent(() => import('@/components/editor/CodeViewer.vue'))

import { useResizable } from '@/composables/useResizable'
import { useFilesStore } from '@/stores/files'
import type { useDecompiler } from '@/composables/useDecompiler'
import type { ProtoConstant } from '@/types/decompiler'

const { t } = useI18n()
const filesStore = useFilesStore()
const decompiler = inject<ReturnType<typeof useDecompiler>>('decompiler')!

const isMobile = inject<ShallowRef<boolean>>('isMobile')!
const analysisOpen = shallowRef(!isMobile.value)
const constantsOpen = shallowRef(false)
const analyzing = shallowRef(false)
const analysisError = shallowRef<string | null>(null)
const selectedProtoId = shallowRef<number | null>(null)

// ── 文件标签栏右键菜单 ──
const tabContextShow = shallowRef(false)
const tabContextX = shallowRef(0)
const tabContextY = shallowRef(0)
/** 右键点击的目标文件 ID */
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

/** 下栏可拖拽调整高度（存储的是下栏高度） */
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

/** 下栏视图：'protos' 展示 ProtoGraph，'cfg' 展示 CfgViewer */
const analysisView = shallowRef<'protos' | 'cfg'>('protos')

/** 常量面板可拖拽宽度 */
const {
  size: constantsPanelWidth,
  dragging: constantsDragging,
  onPointerDown: onConstantsPointerDown,
} = useResizable({
  direction: 'horizontal',
  initialSize: 260,
  minSize: 160,
  maxSize: 500,
  storageKey: 'unluac-constants-width',
})

/** 当前应展示常量的 proto：有选中就用选中的，否则用 proto#0 */
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
  return proto.name ?? `Proto #${proto.id}`
})

/** CFG 指令显示模式：Low-IR 或原始字节码 */
const instrMode = shallowRef<'low-ir' | 'bytecode'>('low-ir')

/** 行范围高亮状态，提供给 CodeViewer 消费 */
const highlightLineRange = shallowRef<{ from: number; to: number } | null>(null)
provide('highlightLineRange', highlightLineRange)

const selectedFile = computed(() => filesStore.selectedFile)
const richResult = computed(() => selectedFile.value?.richResult ?? null)

/** 选中 proto 对应的 CFG */
const selectedCfg = computed(() => {
  if (selectedProtoId.value === null || !richResult.value) return null
  return richResult.value.cfgs[selectedProtoId.value] ?? null
})

const hasAnalysisData = computed(
  () => richResult.value !== null && richResult.value.protos.length > 0,
)

/** 标签栏文件列表直接取 store 的 openFiles */
const openFiles = computed(() => filesStore.openFiles)

/**
 * 文件选中后按需获取 richResult。
 */
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

/** 从 ProtoGraph 点击节点→进入 CFG 视图 */
function onSelectProto(protoId: number) {
  selectedProtoId.value = protoId
  analysisView.value = 'cfg'
}

/** 从 ProtoGraph 双击节点→跳转到源码行范围高亮 */
function onJumpToSource(protoId: number) {
  const proto = richResult.value?.protos[protoId]
  if (proto && proto.lineStart > 0) {
    highlightLineRange.value = { from: proto.lineStart, to: proto.lineEnd }
  }
}

/** 返回 ProtoGraph */
function backToProtos() {
  analysisView.value = 'protos'
  selectedProtoId.value = null
}

/** 文件切换时重置分析状态 */
watch(
  () => `${selectedFile.value?.id}:${selectedFile.value?.revision}`,
  () => {
    selectedProtoId.value = null
    highlightLineRange.value = null
    analysisView.value = 'protos'
    analysisError.value = null
  },
)
</script>

<template>
  <main class="main-content flex min-w-0 flex-1 flex-col">
    <!-- ═══ 上栏：文件标签 + 源码 ═══ -->
    <div class="flex min-h-0 flex-1 flex-col">
      <!-- 文件标签栏 -->
      <div
        v-if="openFiles.length" class="file-tabs" :aria-label="t('filePanel.title')"
        style="border-bottom: 1px solid var(--app-border); background: var(--app-bg-alt)"
      >
        <div v-for="file in openFiles" :key="file.id" class="file-tab" :class="{ active: file.id === filesStore.selectedFileId }" @contextmenu.prevent="openTabContextMenu($event, file.id)">
          <button class="tab-select" :aria-pressed="file.id === filesStore.selectedFileId" @click="filesStore.selectFile(file.id)"><i-mdi-code-braces /><span class="max-w-40 truncate">{{ file.name }}</span><span v-if="file.editedResult !== undefined" class="modified-dot" /></button>
          <button class="tab-close icon-button" :aria-label="`${t('tabs.contextMenu.close')}: ${file.name}`" @click="filesStore.closeTab(file.id)"><i-mdi-close /></button>
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
      <!-- 源码查看器 -->
      <div class="min-h-0 flex-1">
        <WelcomeView v-if="!selectedFile" />
        <CodeViewer v-else />
      </div>
    </div>

    <template v-if="selectedFile?.status === 'success'">
    <!-- ═══ 分割条 ═══ -->
    <div
      v-if="analysisOpen" class="resize-handle shrink-0 cursor-row-resize"
      :class="{ 'bg-indigo-400/40': bottomDragging }"
      :style="{ height: '4px', borderTop: '1px solid var(--app-border)' }"
      @pointerdown="onBottomPointerDown"
    />

    <!-- ═══ 下栏：分析面板 ═══ -->
    <div
      class="flex shrink-0 flex-col"
      :style="{ height: analysisOpen ? `min(${bottomHeight}px, 55dvh)` : '44px' }"
    >
      <!-- 分析面板标题栏 -->
      <div
        class="analysis-toolbar"
        style="border-bottom: 1px solid var(--app-border)"
      >
        <button class="analysis-toggle" :aria-expanded="analysisOpen" @click="analysisOpen = !analysisOpen"><i-mdi-chevron-down v-if="analysisOpen" /><i-mdi-chevron-up v-else />{{ t('workspace.analysis') }}</button>
        <NButton v-if="isMobile && analysisOpen && hasAnalysisData" quaternary size="tiny" :aria-pressed="constantsOpen" @click="constantsOpen = !constantsOpen">{{ t('analysis.constants.title') }}</NButton>
        <template v-if="analysisOpen && analysisView === 'cfg'">
          <NButton quaternary size="tiny" :aria-label="t('tabs.protos')" @click="backToProtos">
            <template #icon>
              <NIcon size="14">
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
                >
                  <polyline points="15 18 9 12 15 6" />
                </svg>
              </NIcon>
            </template>
          </NButton>
          <span class="text-xs font-medium" style="color: var(--app-text-secondary)">
            {{ t('tabs.cfg') }}
            <template v-if="selectedCfg">
              —
              {{
                richResult?.protos[selectedProtoId!]?.name
                  ?? `Proto #${selectedProtoId}`
              }}
            </template>
          </span>
          <span v-if="selectedCfg" class="hidden text-xs sm:inline" style="color: var(--app-text-dim)">
            {{ t('analysis.cfgViewer.blocks') }}: {{ selectedCfg.blocks.length }}
            · {{ t('analysis.cfgViewer.edges') }}: {{ selectedCfg.edges.length }}
          </span>
          <!-- 右侧：指令模式切换 -->
          <span class="ml-auto flex items-center gap-1">
            <button
              class="rounded px-2 py-0.5 text-xs transition-colors"
              :class="instrMode === 'low-ir'
                ? 'bg-blue-100 text-blue-700 dark:bg-blue-900 dark:text-blue-300'
                : 'hover:bg-gray-100 dark:hover:bg-gray-800'"
              :style="instrMode !== 'low-ir' ? 'color: var(--app-text-dim)' : undefined"
              @click="instrMode = 'low-ir'"
            >
              Low-IR
            </button>
            <button
              class="rounded px-2 py-0.5 text-xs transition-colors"
              :class="instrMode === 'bytecode'
                ? 'bg-blue-100 text-blue-700 dark:bg-blue-900 dark:text-blue-300'
                : 'hover:bg-gray-100 dark:hover:bg-gray-800'"
              :style="instrMode !== 'bytecode' ? 'color: var(--app-text-dim)' : undefined"
              @click="instrMode = 'bytecode'"
            >
              {{ t('analysis.cfgViewer.bytecode') }}
            </button>
          </span>
        </template>
        <template v-else-if="analysisOpen">
          <span class="text-xs font-medium" style="color: var(--app-text-secondary)">
            {{ t('tabs.protos') }}
          </span>
        </template>
      </div>

      <!-- 分析内容（左：常量表，右：视图） -->
      <div v-if="analysisOpen" class="flex min-h-0 flex-1">
        <!-- 常量表面板（仅在有分析数据时显示） -->
        <template v-if="hasAnalysisData && (!isMobile || constantsOpen)">
          <div
            class="shrink-0 overflow-hidden"
            :style="{ width: isMobile ? '100%' : `${constantsPanelWidth}px`, borderRight: '1px solid var(--app-border)' }"
          >
            <ConstantsPanel :constants="constantsList" :proto-name="constantsProtoName" />
          </div>
          <div
            v-if="!isMobile" class="resize-handle shrink-0 cursor-col-resize"
            :class="{ 'bg-indigo-400/40': constantsDragging }"
            :style="{ width: '4px' }"
            @pointerdown="onConstantsPointerDown"
          />
        </template>
        <!-- 主内容区 -->
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
          <div
            v-else-if="!hasAnalysisData"
            class="flex h-full items-center justify-center"
          >
            <NEmpty :description="t('analysis.noData')" />
          </div>
          <!-- ProtoGraph 视图 -->
          <ProtoGraph
            v-else-if="analysisView === 'protos'"
            :protos="richResult!.protos"
            @select-proto="onSelectProto"
            @jump-to-source="onJumpToSource"
          />
          <!-- CFG 视图 -->
          <CfgViewer v-else-if="analysisView === 'cfg'" :cfg="selectedCfg" :instr-mode="instrMode" />
        </div>
      </div>
    </div>
    </template>
  </main>
</template>
