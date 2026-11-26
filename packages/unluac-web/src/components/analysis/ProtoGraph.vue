<script setup lang="ts">
/**
 * Proto 引用图组件。
 *
 * 将反编译结果中的 proto 树以有向图形式展示。
 * 单击节点进入该 proto 的 CFG 视图；点击节点右上角的行号跳转按钮直接定位到源码。
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
  failedProtos?: number[]
}>()

const emit = defineEmits<{
  'select-proto': [protoId: number]
  'jump-to-source': [protoId: number]
}>()

const { t } = useI18n()
const { fitView, viewport } = useVueFlow()

const ZOOM_DETAIL_THRESHOLD = 0.5
const NODE_WIDTH = 232
const NODE_HEIGHT = 118
const H_GAP = 36
const V_GAP = 56

const DEPTH_COLORS = [
  '#14b8a6', // 0 - teal (root)
  '#3b82f6', // 1 - blue
  '#6366f1', // 2 - indigo
  '#8b5cf6', // 3 - violet
  '#ec4899', // 4 - pink
  '#f59e0b', // 5 - amber
  '#f97316', // 6 - orange
  '#ef4444', // 7+ - red
]

const failedSet = computed(() => new Set(props.failedProtos ?? []))

function depthColor(depth: number): string {
  return DEPTH_COLORS[Math.min(depth, DEPTH_COLORS.length - 1)]
}

function protoDisplayName(proto: ProtoMeta): string {
  if (proto.name) return proto.name
  return proto.id === 0 ? `${t('analysis.protoGraph.root')} #0` : `Proto #${proto.id}`
}

function protoLineRange(proto: ProtoMeta): [number, number] | null {
  if (proto.generatedLineStart && proto.generatedLineStart > 0) {
    return [proto.generatedLineStart, proto.generatedLineEnd ?? proto.generatedLineStart]
  }
  if (proto.lineStart > 0) {
    return [proto.lineStart, proto.lineEnd || proto.lineStart]
  }
  return null
}

interface TreeLayoutResult {
  positions: Map<number, { x: number; y: number }>
  depths: Map<number, number>
}

function computeTreeLayout(protos: ProtoMeta[]): TreeLayoutResult {
  const positions = new Map<number, { x: number; y: number }>()
  const depths = new Map<number, number>()
  if (protos.length === 0) return { positions, depths }

  const layers: number[][] = []
  depths.set(0, 0)
  for (const proto of protos) {
    const depth = depths.get(proto.id) ?? 0
    layers[depth] ??= []
    layers[depth].push(proto.id)
    for (const childId of proto.children) depths.set(childId, depth + 1)
  }

  for (let layer = 0; layer < layers.length; layer++) {
    const ids = layers[layer]
    const totalWidth = ids.length * NODE_WIDTH + (ids.length - 1) * H_GAP
    const startX = -totalWidth / 2
    for (let i = 0; i < ids.length; i++) {
      positions.set(ids[i], {
        x: startX + i * (NODE_WIDTH + H_GAP),
        y: layer * (NODE_HEIGHT + V_GAP),
      })
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
      style: { stroke: depthColor(parentDepth), strokeWidth: 1.5, opacity: 0.7 },
    }))
  })

  return { nodes, edges }
})

watch(
  () => graphData.value,
  () => {
    setTimeout(() => fitView({ padding: 0.2 }), 50)
  },
)

function onNodeClick({ node }: NodeMouseEvent) {
  emit('select-proto', Number(node.id))
}

function ProtoNode(nodeProps: { data: { proto: ProtoMeta; depth: number } }) {
  const { proto, depth } = nodeProps.data
  const isFailed = failedSet.value.has(proto.id)
  const color = isFailed ? '#ef4444' : depthColor(depth)
  const name = protoDisplayName(proto)
  const isDetailView = viewport.value.zoom >= ZOOM_DETAIL_THRESHOLD
  const range = protoLineRange(proto)
  const lineText = range
    ? range[0] === range[1]
      ? `L${range[0]}`
      : `L${range[0]}-${range[1]}`
    : ''

  return h(
    'div',
    {
      class: 'proto-node-card cursor-pointer rounded-lg border px-3 py-2 text-xs transition-all',
      style: {
        borderColor: isFailed ? '#ef4444' : 'var(--app-border)',
        borderLeftColor: color,
        borderLeftWidth: '3px',
        background: 'var(--app-bg)',
        color: 'var(--app-text)',
      },
    },
    [
      h('div', { class: 'mb-1 flex items-center gap-1.5' }, [
        h(
          'span',
          {
            class: 'min-w-0 flex-1 truncate font-mono text-[12px] font-semibold',
            style: { color },
            title: `${name} (#${proto.id})`,
          },
          name,
        ),
        range
          ? h(
              'button',
              {
                type: 'button',
                class:
                  'proto-jump-btn shrink-0 rounded px-1.5 py-0.5 font-mono text-[10px] transition-colors',
                title: t('analysis.protoGraph.jumpToSource'),
                onClick: (e: MouseEvent) => {
                  e.stopPropagation()
                  emit('jump-to-source', proto.id)
                },
              },
              lineText,
            )
          : null,
      ]),
      ...(isDetailView
        ? [
            h(
              'div',
              {
                class: 'flex items-center gap-2 text-[11px]',
                style: { color: 'var(--app-text-secondary)' },
              },
              [
                h('span', null, `#${proto.id}`),
                h(
                  'span',
                  null,
                  `${t('analysis.protoGraph.params')}: ${proto.numParams}${proto.isVararg ? '+' : ''}`,
                ),
              ],
            ),
            h(
              'div',
              {
                class: 'mt-1 flex items-center gap-2.5 font-mono text-[10px]',
                style: { color: 'var(--app-text-dim)' },
              },
              [
                h('span', { title: t('analysis.protoGraph.upvalues') }, `↑${proto.numUpvalues}`),
                h('span', { title: t('analysis.protoGraph.constants') }, `K${proto.numConstants}`),
                h(
                  'span',
                  { title: t('analysis.protoGraph.instructions') },
                  `I${proto.numInstructions}`,
                ),
              ],
            ),
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
    >
      <template #node-proto="nodeProps">
        <ProtoNode :data="nodeProps.data" />
      </template>
      <Background :gap="20" :size="1" />
      <Controls />
      <MiniMap />
    </VueFlow>
  </div>
</template>
