<script setup lang="ts">
/**
 * Proto 引用图组件。
 *
 * 将反编译结果中的 proto 树以有向图形式展示。
 * 每个 proto 渲染为节点（显示 id、名称、行号、参数签名），
 * 父子关系渲染为有向边。
 *
 * 布局算法：简单的层次树布局（BFS 按深度分层），
 * 不依赖 dagre，因为 proto 关系是严格的树结构。
 *
 * 性能优化：
 * - only-render-visible-elements：视口外节点/边不渲染 DOM
 * - 缩放感知降级：zoom < 0.5 时节点只显示名称，省略详细信息
 */

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
import type { NodeMouseEvent } from '@vue-flow/core'
import { computed, h, watch } from 'vue'
import { useI18n } from 'vue-i18n'
import type { ProtoMeta } from '@/types/decompiler'

const props = defineProps<{
  protos: ProtoMeta[]
}>()

const emit = defineEmits<{
  'select-proto': [protoId: number]
  'jump-to-source': [protoId: number]
}>()

const { t } = useI18n()
const { fitView, viewport } = useVueFlow()

/** zoom 低于此阈值时节点简化为只显示名称 */
const ZOOM_DETAIL_THRESHOLD = 0.5

const NODE_WIDTH = 220
const NODE_HEIGHT = 120
const H_GAP = 40
const V_GAP = 60

/** 按深度层级分配的色板（HSL，从蓝到绿到橙渐变） */
const DEPTH_COLORS = [
  '#6366f1', // 0 - indigo  (根)
  '#3b82f6', // 1 - blue
  '#0ea5e9', // 2 - sky
  '#14b8a6', // 3 - teal
  '#22c55e', // 4 - green
  '#eab308', // 5 - yellow
  '#f97316', // 6 - orange
  '#ef4444', // 7+ - red
]

function depthColor(depth: number): string {
  return DEPTH_COLORS[Math.min(depth, DEPTH_COLORS.length - 1)]
}

interface TreeLayoutResult {
  positions: Map<number, { x: number; y: number }>
  depths: Map<number, number>
}

/**
 * 层次树布局：BFS 分层，同层节点等间距水平排列。
 * 同时记录每个节点的深度，用于颜色编码。
 */
function computeTreeLayout(protos: ProtoMeta[]): TreeLayoutResult {
  const positions = new Map<number, { x: number; y: number }>()
  const depths = new Map<number, number>()
  if (protos.length === 0) return { positions, depths }

  // 找出所有被引用为 children 的 id
  const childSet = new Set(protos.flatMap((p) => p.children))
  // 根节点：不是任何 proto 的 child
  const roots = protos.filter((p) => !childSet.has(p.id))
  if (roots.length === 0 && protos.length > 0) {
    // fallback: 使用第一个 proto 作为根
    roots.push(protos[0])
  }

  const protoMap = new Map(protos.map((p) => [p.id, p]))

  // BFS 分层
  const layers: number[][] = []
  const visited = new Set<number>()
  let queue = roots.map((r) => r.id)
  for (const id of queue) visited.add(id)

  while (queue.length > 0) {
    layers.push(queue)
    const next: number[] = []
    for (const id of queue) {
      const proto = protoMap.get(id)
      if (!proto) continue
      for (const childId of proto.children) {
        if (!visited.has(childId)) {
          visited.add(childId)
          next.push(childId)
        }
      }
    }
    queue = next
  }

  // 计算位置和深度
  for (let layer = 0; layer < layers.length; layer++) {
    const ids = layers[layer]
    const totalWidth = ids.length * NODE_WIDTH + (ids.length - 1) * H_GAP
    const startX = -totalWidth / 2
    for (let i = 0; i < ids.length; i++) {
      positions.set(ids[i], {
        x: startX + i * (NODE_WIDTH + H_GAP),
        y: layer * (NODE_HEIGHT + V_GAP),
      })
      depths.set(ids[i], layer)
    }
  }

  return { positions, depths }
}

const graphData = computed(() => {
  const protos = props.protos
  if (protos.length === 0) return { nodes: [], edges: [] }

  const { positions, depths } = computeTreeLayout(protos)

  const nodes = protos.map((proto) => {
    const pos = positions.get(proto.id) ?? { x: 0, y: 0 }
    const depth = depths.get(proto.id) ?? 0
    return {
      id: String(proto.id),
      position: pos,
      data: { proto, depth },
      type: 'proto',
      style: { width: `${NODE_WIDTH}px` },
    }
  })

  const edges = protos.flatMap((proto) => {
    const parentDepth = depths.get(proto.id) ?? 0
    return proto.children.map((childId) => ({
      id: `e${proto.id}-${childId}`,
      source: String(proto.id),
      target: String(childId),
      animated: false,
      style: { stroke: depthColor(parentDepth) },
    }))
  })

  return { nodes, edges }
})

watch(
  () => graphData.value,
  () => {
    // 数据变化后自动 fitView
    setTimeout(() => fitView({ padding: 0.2 }), 50)
  },
)

function onNodeClick({ node }: NodeMouseEvent) {
  emit('select-proto', Number(node.id))
}

function onNodeDoubleClick({ node }: NodeMouseEvent) {
  emit('jump-to-source', Number(node.id))
}

/**
 * 自定义 proto 节点渲染函数。
 * 使用 render function 避免为单一用途创建独立 SFC。
 */
function ProtoNode(nodeProps: { data: { proto: ProtoMeta; depth: number } }) {
  const { proto, depth } = nodeProps.data
  const color = depthColor(depth)
  const name = proto.name ?? `${t('analysis.protoGraph.root')} #${proto.id}`
  const isDetailView = viewport.value.zoom >= ZOOM_DETAIL_THRESHOLD
  const lineInfo =
    proto.lineStart > 0
      ? `${t('analysis.protoGraph.lines')} ${proto.lineStart}-${proto.lineEnd}`
      : ''

  return h(
    'div',
    {
      class:
        'rounded-lg border bg-white px-3 py-2 shadow-sm transition-colors hover:shadow-md dark:bg-gray-800 cursor-pointer text-xs',
      style: { borderColor: color, borderLeftWidth: '3px' },
    },
    [
      h('div', { class: 'font-semibold text-sm truncate mb-1', style: { color } }, name),
      // 仅在 zoom >= 阈值时渲染详细信息
      ...(isDetailView
        ? [
            lineInfo ? h('div', { class: 'text-gray-500 dark:text-gray-400' }, lineInfo) : null,
            h('div', { class: 'text-gray-500 dark:text-gray-400' }, [
              `${t('analysis.protoGraph.params')}: ${proto.numParams}`,
              proto.isVararg ? ` (${t('analysis.protoGraph.vararg')})` : '',
            ]),
            h('div', { class: 'text-gray-500 dark:text-gray-400 flex gap-2' }, [
              h('span', null, `↑${proto.numUpvalues}`),
              h('span', null, `C${proto.numConstants}`),
              h('span', null, `I${proto.numInstructions}`),
            ]),
          ]
        : []),
    ],
  )
}
</script>

<template>
  <div class="h-full w-full">
    <VueFlow
      :nodes="graphData.nodes"
      :edges="graphData.edges"
      :default-viewport="{ zoom: 1, x: 0, y: 0 }"
      :min-zoom="0.1"
      :max-zoom="3"
      only-render-visible-elements
      fit-view-on-init
      @node-click="onNodeClick"
      @node-double-click="onNodeDoubleClick"
    >
      <template #node-proto="nodeProps">
        <ProtoNode :data="nodeProps.data" />
      </template>
      <Background />
      <Controls />
      <MiniMap />
    </VueFlow>
  </div>
</template>
