<script setup lang="ts">
/**
 * CFG 可视化组件。
 *
 * 将选中 proto 的控制流图以有向图形式展示。
 * 对超大 CFG（> 220 基本块）自动聚焦入口邻域，并在全图超过 300 块时使用轻量网格兜底，
 * 避免 dagre 布局卡死主线程。
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

const focusBlockId = shallowRef<number | null>(null)
const FOCUS_HOPS = 3
const AUTO_FOCUS_THRESHOLD = 220
const DAGRE_MAX_BLOCKS = 300
const ZOOM_DETAIL_THRESHOLD = 0.4

const NODE_WIDTH = 280
const INSTR_LINE_HEIGHT = 18
const NODE_PADDING = 32

const EDGE_COLORS: Record<string, string> = {
  fallthrough: '#8795b0',
  jump: '#64748b',
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

function collectNHopNeighbors(cfg: ProtoCfg, centerId: number, hops: number): Set<number> {
  const neighbors = new Set<number>([centerId])
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

function computeGridFallbackLayout(blocks: CfgBlock[]): Map<number, { x: number; y: number }> {
  const positions = new Map<number, { x: number; y: number }>()
  const cols = Math.max(1, Math.ceil(Math.sqrt(blocks.length)))
  for (let i = 0; i < blocks.length; i++) {
    const col = i % cols
    const row = Math.floor(i / cols)
    positions.set(blocks[i].id, {
      x: col * (NODE_WIDTH + 48),
      y: row * 240,
    })
  }
  return positions
}

function computeDagreLayout(
  blocks: CfgBlock[],
  edges: ProtoCfg['edges'],
): Map<number, { x: number; y: number }> {
  if (blocks.length > DAGRE_MAX_BLOCKS) {
    return computeGridFallbackLayout(blocks)
  }

  const g = new dagre.graphlib.Graph()
  g.setGraph({ rankdir: 'TB', ranksep: 56, nodesep: 36 })
  g.setDefaultEdgeLabel(() => ({}))

  for (const block of blocks) {
    g.setNode(String(block.id), {
      width: NODE_WIDTH,
      height: estimateNodeHeight(block),
    })
  }

  for (const edge of edges) {
    g.setEdge(String(edge.from), String(edge.to))
  }

  dagre.layout(g)

  const positions = new Map<number, { x: number; y: number }>()
  for (const block of blocks) {
    const node = g.node(String(block.id))
    if (node) {
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

  const visibleIds =
    focusBlockId.value !== null ? collectNHopNeighbors(cfg, focusBlockId.value, FOCUS_HOPS) : null

  const filteredBlocks = visibleIds ? cfg.blocks.filter((b) => visibleIds.has(b.id)) : cfg.blocks
  const filteredEdges = visibleIds
    ? cfg.edges.filter((e) => visibleIds.has(e.from) && visibleIds.has(e.to))
    : cfg.edges

  const positions = computeDagreLayout(filteredBlocks, filteredEdges)

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
    style: { stroke: EDGE_COLORS[edge.kind] ?? '#8795b0', strokeWidth: 1.5 },
    labelStyle: { fontSize: '10px', fill: EDGE_COLORS[edge.kind] ?? '#8795b0' },
  }))

  return { nodes, edges }
})

watch(
  () => graphData.value,
  () => {
    setTimeout(() => fitView({ padding: 0.2 }), 50)
  },
)

/** cfg 切换时重置聚焦状态；超大 CFG 默认自动聚焦入口块，避免布局阻塞 */
watch(
  () => props.cfg,
  (cfg) => {
    focusBlockId.value = cfg && cfg.blocks.length > AUTO_FOCUS_THRESHOLD ? cfg.entryBlock : null
  },
  { immediate: true },
)

function onNodeDoubleClick({ node }: { node: { id: string } }) {
  const blockId = Number(node.id)
  focusBlockId.value = focusBlockId.value === blockId ? null : blockId
}

function clearFocus() {
  focusBlockId.value = null
}

function CfgBlockNode(nodeProps: {
  data: { block: CfgBlock; isEntry: boolean; isExit: boolean; isFocusCenter: boolean }
}) {
  const { block, isEntry, isExit, isFocusCenter } = nodeProps.data
  const isDetailView = viewport.value.zoom >= ZOOM_DETAIL_THRESHOLD
  const lines = props.instrMode === 'bytecode' ? block.rawInstructions : block.instructions

  const accentColor = isFocusCenter
    ? '#f59e0b'
    : isEntry
      ? 'var(--app-accent)'
      : isExit
        ? '#8b5cf6'
        : 'var(--app-border)'

  const badge = isEntry
    ? h(
        'span',
        {
          class: 'rounded px-1.5 py-0.2 text-[10px] font-medium',
          style: { background: 'var(--app-accent-soft)', color: 'var(--app-accent)' },
        },
        t('analysis.cfgViewer.entry'),
      )
    : isExit
      ? h(
          'span',
          {
            class:
              'rounded bg-purple-100 px-1.5 py-0.2 text-[10px] font-medium text-purple-700 dark:bg-purple-900/50 dark:text-purple-300',
          },
          t('analysis.cfgViewer.exit'),
        )
      : null

  const kindLabel =
    block.kind !== 'normal'
      ? h(
          'span',
          {
            class: 'rounded px-1 text-[10px]',
            style: { background: 'var(--app-bg-hover)', color: 'var(--app-text-secondary)' },
          },
          block.kind,
        )
      : null

  return h(
    'div',
    {
      class: 'rounded-lg border px-2.5 py-2 font-mono text-xs shadow-sm',
      style: {
        background: 'var(--app-bg)',
        color: 'var(--app-text)',
        borderColor: accentColor,
        borderTopWidth: isEntry || isExit || isFocusCenter ? '3px' : '1px',
      },
    },
    [
      h('div', { class: 'mb-1.5 flex items-center gap-1.5 font-sans' }, [
        h('span', { class: 'font-semibold' }, `B${block.id}`),
        badge,
        kindLabel,
        !isDetailView && block.instructions.length > 0
          ? h(
              'span',
              { class: 'ml-auto text-[10px]', style: { color: 'var(--app-text-dim)' } },
              `${block.instructions.length} instrs`,
            )
          : null,
      ]),
      isDetailView
        ? block.instructions.length > 0
          ? h(
              'div',
              {
                class: 'cfg-node-scroll max-h-48 space-y-0 overflow-y-auto',
                style: { color: 'var(--app-text-secondary)' },
                onWheel: (e: WheelEvent) => e.stopPropagation(),
              },
              lines.map((instr, i) =>
                h(
                  'div',
                  {
                    key: i,
                    class: 'truncate leading-[18px] hover:text-clip',
                    title: instr,
                  },
                  instr,
                ),
              ),
            )
          : h('div', { class: 'italic', style: { color: 'var(--app-text-dim)' } }, '(empty)')
        : null,
    ],
  )
}
</script>

<template>
  <div class="flex h-full w-full flex-col">
    <div v-if="!cfg" class="flex h-full items-center justify-center">
      <NEmpty :description="t('analysis.selectProto')" />
    </div>
    <template v-else>
      <div
        v-if="focusBlockId !== null"
        class="flex shrink-0 items-center gap-2 border-b border-amber-200 bg-amber-50 px-3 py-1 text-xs dark:border-amber-800/60 dark:bg-amber-950/40"
      >
        <span class="text-amber-700 dark:text-amber-300">
          {{ t('analysis.cfgViewer.focusHint', { block: `B${focusBlockId}`, hops: FOCUS_HOPS }) }}
        </span>
        <button
          type="button"
          class="rounded px-1.5 py-0.5 text-amber-700 hover:bg-amber-100 dark:text-amber-300 dark:hover:bg-amber-900/60"
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
          <Background :gap="20" :size="1" />
          <Controls />
          <MiniMap />
        </VueFlow>
      </div>
    </template>
  </div>
</template>
