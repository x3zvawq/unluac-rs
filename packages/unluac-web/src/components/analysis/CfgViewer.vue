<script setup lang="ts">
/**
 * CFG 可视化组件。
 *
 * 将选中 proto 的控制流图以有向图形式展示。
 * 每个 BasicBlock 渲染为节点（内含 Low-IR 指令列表），
 * 每条边标注类型并用颜色区分（正常灰 / 回边红 / 分支蓝绿）。
 *
 * 布局使用 dagre 自动计算 DAG 布局位置。
 *
 * 性能优化：
 * - only-render-visible-elements：视口外节点/边不渲染 DOM
 * - 缩放感知降级：zoom < 0.4 时节点只显示块 ID，不渲染指令列表
 */

import dagre from '@dagrejs/dagre'
// biome-ignore lint/correctness/noUnusedImports: used in template
import { MiniMap } from '@vue-flow/minimap'
import '@vue-flow/minimap/dist/style.css'
// biome-ignore lint/correctness/noUnusedImports: used in template
import { Background } from '@vue-flow/background'
// biome-ignore lint/correctness/noUnusedImports: used in template
import { useVueFlow, VueFlow } from '@vue-flow/core'
import '@vue-flow/core/dist/style.css'
import '@vue-flow/core/dist/theme-default.css'
// biome-ignore lint/correctness/noUnusedImports: used in template
import { Controls } from '@vue-flow/controls'
import '@vue-flow/controls/dist/style.css'
import { computed, h, shallowRef, watch } from 'vue'
import { useI18n } from 'vue-i18n'
import type { CfgBlock, ProtoCfg } from '@/types/decompiler'

const props = defineProps<{
  cfg: ProtoCfg | null
  instrMode: 'low-ir' | 'bytecode'
}>()

const { t } = useI18n()
const { fitView, viewport } = useVueFlow()

/** 聚焦到某个块的 N 层邻居，null 表示显示全图 */
const focusBlockId = shallowRef<number | null>(null)
const FOCUS_HOPS = 3

/** zoom 低于此阈值时节点内容简化为只显示块 ID（减少 DOM 开销） */
const ZOOM_DETAIL_THRESHOLD = 0.4

const NODE_WIDTH = 280
const INSTR_LINE_HEIGHT = 18
const NODE_PADDING = 32

/** 边类型对应的颜色 */
const EDGE_COLORS: Record<string, string> = {
  fallthrough: '#9ca3af',
  jump: '#6b7280',
  'branch-true': '#22c55e',
  'branch-false': '#ef4444',
  'loop-body': '#f59e0b',
  'loop-exit': '#ef4444',
  return: '#8b5cf6',
  'tail-call': '#06b6d4',
}

function estimateNodeHeight(block: CfgBlock): number {
  const lines = props.instrMode === 'bytecode' ? block.rawInstructions : block.instructions
  return NODE_PADDING + Math.max(lines.length, 1) * INSTR_LINE_HEIGHT
}

/**
 * 从 centerId 出发，BFS 收集 N 跳内可达的所有块 id（双向）。
 */
function collectNHopNeighbors(cfg: ProtoCfg, centerId: number, hops: number): Set<number> {
  const neighbors = new Set<number>([centerId])
  // 构建双向邻接表
  const adj = new Map<number, number[]>()
  for (const block of cfg.blocks) {
    adj.set(block.id, [])
  }
  for (const edge of cfg.edges) {
    adj.get(edge.from)?.push(edge.to)
    adj.get(edge.to)?.push(edge.from)
  }
  let frontier = [centerId]
  for (let i = 0; i < hops && frontier.length > 0; i++) {
    const next: number[] = []
    for (const id of frontier) {
      for (const nb of adj.get(id) ?? []) {
        if (!neighbors.has(nb)) {
          neighbors.add(nb)
          next.push(nb)
        }
      }
    }
    frontier = next
  }
  return neighbors
}

/**
 * 使用 dagre 计算 DAG 布局。
 * 返回节点位置 map。
 */
function computeDagreLayout(cfg: ProtoCfg): Map<number, { x: number; y: number }> {
  const g = new dagre.graphlib.Graph()
  g.setGraph({ rankdir: 'TB', ranksep: 60, nodesep: 40 })
  g.setDefaultEdgeLabel(() => ({}))

  for (const block of cfg.blocks) {
    g.setNode(String(block.id), {
      width: NODE_WIDTH,
      height: estimateNodeHeight(block),
    })
  }

  for (const edge of cfg.edges) {
    g.setEdge(String(edge.from), String(edge.to))
  }

  dagre.layout(g)

  const positions = new Map<number, { x: number; y: number }>()
  for (const block of cfg.blocks) {
    const node = g.node(String(block.id))
    if (node) {
      // dagre 返回中心点，转换为左上角
      positions.set(block.id, {
        x: node.x - NODE_WIDTH / 2,
        y: node.y - estimateNodeHeight(block) / 2,
      })
    }
  }
  return positions
}

const graphData = computed(() => {
  const cfg = props.cfg
  if (!cfg) return { nodes: [], edges: [] }

  const positions = computeDagreLayout(cfg)

  // 聚焦模式：只显示 N 跳邻居
  const visibleIds =
    focusBlockId.value !== null ? collectNHopNeighbors(cfg, focusBlockId.value, FOCUS_HOPS) : null

  const filteredBlocks = visibleIds ? cfg.blocks.filter((b) => visibleIds.has(b.id)) : cfg.blocks
  const filteredEdges = visibleIds
    ? cfg.edges.filter((e) => visibleIds.has(e.from) && visibleIds.has(e.to))
    : cfg.edges

  const nodes = filteredBlocks.map((block) => {
    const pos = positions.get(block.id) ?? { x: 0, y: 0 }
    return {
      id: String(block.id),
      position: pos,
      data: {
        block,
        isEntry: block.id === cfg.entryBlock,
        isExit: block.id === cfg.exitBlock,
        isFocusCenter: block.id === focusBlockId.value,
      },
      type: 'cfgBlock',
      style: { width: `${NODE_WIDTH}px` },
    }
  })

  const edges = filteredEdges.map((edge, i) => ({
    id: `e${i}-${edge.from}-${edge.to}`,
    source: String(edge.from),
    target: String(edge.to),
    label: edge.kind,
    animated: edge.kind === 'loop-body',
    style: { stroke: EDGE_COLORS[edge.kind] ?? '#9ca3af' },
    labelStyle: { fontSize: '10px', fill: EDGE_COLORS[edge.kind] ?? '#9ca3af' },
  }))

  return { nodes, edges }
})

watch(
  () => graphData.value,
  () => {
    setTimeout(() => fitView({ padding: 0.2 }), 50)
  },
)

/** cfg 切换时重置聚焦状态 */
watch(
  () => props.cfg,
  () => {
    focusBlockId.value = null
  },
)

/** 双击节点聚焦子图，再次双击同一节点取消聚焦 */
function onNodeDoubleClick({ node }: { node: { id: string } }) {
  const blockId = Number(node.id)
  focusBlockId.value = focusBlockId.value === blockId ? null : blockId
}

function clearFocus() {
  focusBlockId.value = null
}

/**
 * 自定义 CFG 基本块节点渲染。
 * 显示块 ID、类型标签和指令列表。
 */
function CfgBlockNode(nodeProps: {
  data: { block: CfgBlock; isEntry: boolean; isExit: boolean; isFocusCenter: boolean }
}) {
  const { block, isEntry, isExit, isFocusCenter } = nodeProps.data
  const isDetailView = viewport.value.zoom >= ZOOM_DETAIL_THRESHOLD
  const lines = props.instrMode === 'bytecode' ? block.rawInstructions : block.instructions

  // 边框颜色：聚焦中心橙/入口绿/出口紫/普通灰
  const borderClass = isFocusCenter
    ? 'border-amber-500 dark:border-amber-400 ring-2 ring-amber-300/50'
    : isEntry
      ? 'border-green-500 dark:border-green-400'
      : isExit
        ? 'border-purple-500 dark:border-purple-400'
        : 'border-gray-300 dark:border-gray-600'

  const badge = isEntry
    ? h(
        'span',
        { class: 'rounded bg-green-100 px-1 text-green-700 dark:bg-green-900 dark:text-green-300' },
        t('analysis.cfgViewer.entry'),
      )
    : isExit
      ? h(
          'span',
          {
            class:
              'rounded bg-purple-100 px-1 text-purple-700 dark:bg-purple-900 dark:text-purple-300',
          },
          t('analysis.cfgViewer.exit'),
        )
      : null

  const kindLabel =
    block.kind !== 'normal'
      ? h(
          'span',
          { class: 'rounded bg-gray-100 px-1 text-gray-600 dark:bg-gray-700 dark:text-gray-300' },
          block.kind,
        )
      : null

  return h(
    'div',
    {
      class: `rounded-lg border-2 bg-white px-2 py-1.5 shadow-sm dark:bg-gray-800 text-xs font-mono ${borderClass}`,
    },
    [
      h('div', { class: 'flex items-center gap-1 mb-1 font-sans' }, [
        h('span', { class: 'font-semibold' }, `B${block.id}`),
        badge,
        kindLabel,
        // 缩放过小时显示指令数量提示
        !isDetailView && block.instructions.length > 0
          ? h('span', { class: 'text-gray-400 ml-auto' }, `${block.instructions.length} instrs`)
          : null,
      ]),
      // 仅在 zoom >= 阈值时渲染完整指令列表
      isDetailView
        ? block.instructions.length > 0
          ? h(
              'div',
              {
                class:
                  'cfg-node-scroll space-y-0 text-gray-700 dark:text-gray-300 max-h-48 overflow-y-auto',
                // 阻止滚轮事件冒泡到 VueFlow，使节点内容可独立滚动
                onWheel: (e: WheelEvent) => e.stopPropagation(),
              },
              lines.map((instr, i) =>
                h(
                  'div',
                  {
                    key: i,
                    class: 'truncate hover:text-clip leading-[18px]',
                    title: instr,
                  },
                  instr,
                ),
              ),
            )
          : h('div', { class: 'text-gray-400 italic' }, '(empty)')
        : null,
    ],
  )
}
</script>

<template>
  <!-- 外层容器使用 flex-col 确保 toolbar 不挤占 VueFlow 空间 -->
  <div class="flex h-full w-full flex-col">
    <div v-if="!cfg" class="flex h-full items-center justify-center">
      <NEmpty :description="t('analysis.selectProto')" />
    </div>
    <template v-else>
      <!-- 聚焦模式提示条 -->
      <div
        v-if="focusBlockId !== null"
        class="flex shrink-0 items-center gap-2 border-b border-amber-200 bg-amber-50 px-3 py-1 text-xs dark:border-amber-800 dark:bg-amber-950"
      >
        <span class="text-amber-700 dark:text-amber-300">
          {{ t('analysis.cfgViewer.focusHint', { block: `B${focusBlockId}`, hops: FOCUS_HOPS }) }}
        </span>
        <button
          class="rounded px-1.5 py-0.5 text-amber-600 hover:bg-amber-100 dark:text-amber-400 dark:hover:bg-amber-900"
          @click="clearFocus"
        >
          {{ t('analysis.cfgViewer.clearFocus') }}
        </button>
      </div>
      <div class="min-h-0 flex-1">
      <VueFlow
        :nodes="graphData.nodes"
        :edges="graphData.edges"
        :default-viewport="{ zoom: 1, x: 0, y: 0 }"
        :min-zoom="0.05"
        :max-zoom="3"
        only-render-visible-elements
        fit-view-on-init
        @node-double-click="onNodeDoubleClick"
      >
        <template #node-cfgBlock="nodeProps">
          <CfgBlockNode :data="nodeProps.data" />
        </template>
        <Background />
        <Controls />
        <MiniMap />
      </VueFlow>
      </div>
    </template>
  </div>
</template>


