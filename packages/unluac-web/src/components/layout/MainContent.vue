<script setup lang="ts">
/**
 * 主内容区容器——上下双栏布局。
 *
 * 上栏：VS Code 风格文件标签栏 + CodeViewer，显示反编译后的源码。
 * 下栏：分析面板，默认显示 ProtoGraph；点击某个 proto 进入该 proto 的 CFG 视图，
 *       左上角提供返回按钮回到 ProtoGraph。
 *
 * 文件切换后自动按需获取 richResult（结构化分析数据），缓存于 FileEntry 上。
 * ProtoGraph / CfgViewer 通过 defineAsyncComponent 懒加载，首屏仅下载 CodeViewer。
 */

import { computed, defineAsyncComponent, inject, provide, shallowRef, watch } from 'vue'
import { useI18n } from 'vue-i18n'

const ProtoGraph = defineAsyncComponent(() => import('@/components/analysis/ProtoGraph.vue'))
const CfgViewer = defineAsyncComponent(() => import('@/components/analysis/CfgViewer.vue'))

import ConstantsPanel from '@/components/analysis/ConstantsPanel.vue'

import { useResizable } from '@/composables/useResizable'
import { useFilesStore } from '@/stores/files'
import { useSettingsStore } from '@/stores/settings'
import type { ProtoConstant, RichDecompileResult } from '@/types/decompiler'

const { t } = useI18n()
const filesStore = useFilesStore()
const settingsStore = useSettingsStore()
const decompiler = inject<{
  decompileRich: (fileId: string, bytes: Uint8Array, options: any) => Promise<RichDecompileResult>
}>('decompiler')!

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
    return richResult.value.protos.find((p) => p.id === selectedProtoId.value) ?? null
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
  return richResult.value.cfgs.find((c) => c.protoId === selectedProtoId.value) ?? null
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
  selectedFile,
  async (file) => {
    if (!file || (file.status !== 'success' && file.status !== 'skipped') || file.richResult) return
    // skipped 文件（已是源码）不做 richResult 分析
    if (file.status === 'skipped') return

    analyzing.value = true
    analysisError.value = null
    try {
      const bytes = new Uint8Array(file.bytes)
      const result = await decompiler.decompileRich(file.id, bytes, settingsStore.options)
      filesStore.updateRichResult(file.id, result)
    } catch (err) {
      console.error(`[analysis] richResult for ${file.id} failed:`, err)
      analysisError.value = err instanceof Error ? err.message : String(err)
    } finally {
      analyzing.value = false
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
  const proto = richResult.value?.protos.find((p) => p.id === protoId)
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
  () => selectedFile.value?.id,
  () => {
    selectedProtoId.value = null
    highlightLineRange.value = null
    analysisView.value = 'protos'
    analysisError.value = null
  },
)
</script>

<template>
  <main class="flex min-w-0 flex-1 flex-col">
    <!-- ═══ 上栏：文件标签 + 源码 ═══ -->
    <div class="flex min-h-0 flex-1 flex-col">
      <!-- 文件标签栏 -->
      <div
        class="flex shrink-0 items-center gap-0 overflow-x-auto"
        style="border-bottom: 1px solid var(--app-border); background: var(--app-bg-alt)"
      >
        <button
          v-for="file in openFiles"
          :key="file.id"
          class="group flex shrink-0 items-center gap-1.5 px-3 py-1.5 text-xs transition-colors"
          :style="{
            borderRight: '1px solid var(--app-border)',
            background: file.id === filesStore.selectedFileId ? 'var(--app-bg)' : undefined,
            color: file.id === filesStore.selectedFileId ? 'var(--app-text)' : 'var(--app-text-secondary)',
          }"
          @click="filesStore.selectFile(file.id)"
          @contextmenu.prevent="openTabContextMenu($event, file.id)"
        >
          <span class="max-w-40 truncate">{{ file.name }}</span>
          <span
            class="ml-1 hidden rounded-sm group-hover:inline-block"
            style="color: var(--app-text-dim)"
            @click.stop="filesStore.closeTab(file.id)"
          >
            ×
          </span>
        </button>
        <div v-if="openFiles.length === 0" class="px-3 py-1.5 text-xs text-gray-400">
          {{ t('analysis.noFile') }}
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
        <CodeViewer />
      </div>
    </div>

    <!-- ═══ 分割条 ═══ -->
    <div
      class="shrink-0 cursor-row-resize transition-colors hover:bg-indigo-400/40"
      :class="{ 'bg-indigo-400/40': bottomDragging }"
      :style="{ height: '4px', borderTop: '1px solid var(--app-border)' }"
      @pointerdown="onBottomPointerDown"
    />

    <!-- ═══ 下栏：分析面板 ═══ -->
    <div
      class="flex shrink-0 flex-col"
      :style="{ height: `${bottomHeight}px` }"
    >
      <!-- 分析面板标题栏 -->
      <div
        class="flex shrink-0 items-center gap-2 px-3 py-1"
        style="border-bottom: 1px solid var(--app-border)"
      >
        <template v-if="analysisView === 'cfg'">
          <NButton quaternary size="tiny" @click="backToProtos">
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
                richResult?.protos.find((p) => p.id === selectedProtoId)?.name
                  ?? `Proto #${selectedProtoId}`
              }}
            </template>
          </span>
          <span v-if="selectedCfg" class="text-xs" style="color: var(--app-text-dim)">
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
        <template v-else>
          <span class="text-xs font-medium" style="color: var(--app-text-secondary)">
            {{ t('tabs.protos') }}
          </span>
        </template>
      </div>

      <!-- 分析内容（左：常量表，右：视图） -->
      <div class="flex min-h-0 flex-1">
        <!-- 常量表面板（仅在有分析数据时显示） -->
        <template v-if="hasAnalysisData">
          <div
            class="shrink-0 overflow-hidden"
            :style="{ width: `${constantsPanelWidth}px`, borderRight: '1px solid var(--app-border)' }"
          >
            <ConstantsPanel :constants="constantsList" :proto-name="constantsProtoName" />
          </div>
          <div
            class="shrink-0 cursor-col-resize transition-colors hover:bg-indigo-400/40"
            :class="{ 'bg-indigo-400/40': constantsDragging }"
            :style="{ width: '4px' }"
            @pointerdown="onConstantsPointerDown"
          />
        </template>
        <!-- 主内容区 -->
        <div class="min-w-0 flex-1">
          <div v-if="analyzing" class="flex h-full items-center justify-center">
            <NSpin :description="t('analysis.loading')" />
          </div>
          <div
            v-else-if="!selectedFile || (selectedFile.status !== 'success' && selectedFile.status !== 'skipped')"
            class="flex h-full items-center justify-center"
          >
            <NEmpty :description="t('analysis.noFile')" />
          </div>
          <div
            v-else-if="selectedFile.status === 'skipped'"
            class="flex h-full items-center justify-center"
          >
            <NEmpty :description="t('analysis.sourceFile')" />
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
  </main>
</template>
