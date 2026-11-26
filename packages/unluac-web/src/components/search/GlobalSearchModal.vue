<script setup lang="ts">
/**
 * 跨文件全文搜索弹窗（Ctrl/Cmd+Shift+F）。
 *
 * 在工作区所有已反编译文件（以及已加载的常量池）中搜索文本或正则，
 * 点击任意命中项直接切换到目标文件并滚动高亮到对应源码行。
 */

import type { InputInst } from 'naive-ui'
import { computed, nextTick, onUnmounted, shallowRef, useTemplateRef, watch } from 'vue'
import { useI18n } from 'vue-i18n'
import { useFilesStore } from '@/stores/files'
import { searchWorkspaceFiles, type WorkspaceSearchMatch } from '@/utils/workspaceSearch'

const props = defineProps<{
  show: boolean
}>()

const emit = defineEmits<{
  'update:show': [value: boolean]
  select: [match: WorkspaceSearchMatch]
}>()

const { t } = useI18n()
const filesStore = useFilesStore()

const inputRef = useTemplateRef<InputInst>('searchInput')
const query = shallowRef('')
const debouncedQuery = shallowRef('')
const caseSensitive = shallowRef(false)
const useRegex = shallowRef(false)
const activeIndex = shallowRef(0)

let debounceTimer: ReturnType<typeof setTimeout> | null = null
watch(query, (val) => {
  if (debounceTimer) clearTimeout(debounceTimer)
  if (!val.trim()) {
    debouncedQuery.value = ''
    return
  }
  debounceTimer = setTimeout(() => {
    debouncedQuery.value = val
  }, 150)
})

onUnmounted(() => {
  if (debounceTimer) clearTimeout(debounceTimer)
})

const searchableFileCount = computed(
  () =>
    filesStore.files.filter(
      (f) => (f.status === 'success' || f.status === 'skipped') && f.result !== undefined,
    ).length,
)

const searchResult = computed(() =>
  searchWorkspaceFiles(filesStore.files, debouncedQuery.value, {
    caseSensitive: caseSensitive.value,
    useRegex: useRegex.value,
  }),
)

const flatMatches = computed(() => searchResult.value.groups.flatMap((group) => group.matches))

watch(
  () => props.show,
  async (open) => {
    if (!open) return
    activeIndex.value = 0
    await nextTick()
    inputRef.value?.focus()
    inputRef.value?.select()
  },
)

watch([query, caseSensitive, useRegex], () => {
  activeIndex.value = 0
})

function chooseMatch(match: WorkspaceSearchMatch) {
  emit('select', match)
  emit('update:show', false)
}

function handleKeydown(e: KeyboardEvent) {
  const total = flatMatches.value.length
  if (total === 0) return

  if (e.key === 'ArrowDown') {
    e.preventDefault()
    activeIndex.value = (activeIndex.value + 1) % total
  } else if (e.key === 'ArrowUp') {
    e.preventDefault()
    activeIndex.value = (activeIndex.value - 1 + total) % total
  } else if (e.key === 'Enter') {
    e.preventDefault()
    const match = flatMatches.value[activeIndex.value]
    if (match) chooseMatch(match)
  }
}

function matchFlatIndex(groupIndex: number, matchIndex: number): number {
  let offset = 0
  for (let i = 0; i < groupIndex; i++) {
    offset += searchResult.value.groups[i].matches.length
  }
  return offset + matchIndex
}
</script>

<template>
  <NModal
    :show="show"
    preset="card"
    :title="t('globalSearch.title')"
    :style="{ width: 'min(720px, 94vw)' }"
    :content-style="{ padding: '12px 16px 16px' }"
    :bordered="false"
    @update:show="emit('update:show', $event)"
  >
    <div class="flex flex-col gap-3" @keydown="handleKeydown">
      <!-- 搜索输入与开关 -->
      <div class="flex items-center gap-2">
        <NInput
          ref="searchInput"
          v-model:value="query"
          :placeholder="t('globalSearch.placeholder')"
          clearable
          size="medium"
        >
          <template #prefix>
            <i-mdi-magnify />
          </template>
        </NInput>
        <NTooltip>
          <template #trigger>
            <NButton
              size="medium"
              :type="caseSensitive ? 'primary' : 'default'"
              :secondary="caseSensitive"
              :quaternary="!caseSensitive"
              :aria-pressed="caseSensitive"
              :aria-label="t('globalSearch.caseSensitive')"
              @click="caseSensitive = !caseSensitive"
            >
              Aa
            </NButton>
          </template>
          {{ t('globalSearch.caseSensitive') }}
        </NTooltip>
        <NTooltip>
          <template #trigger>
            <NButton
              size="medium"
              :type="useRegex ? 'primary' : 'default'"
              :secondary="useRegex"
              :quaternary="!useRegex"
              :aria-pressed="useRegex"
              :aria-label="t('globalSearch.regex')"
              @click="useRegex = !useRegex"
            >
              .*
            </NButton>
          </template>
          {{ t('globalSearch.regex') }}
        </NTooltip>
      </div>

      <!-- 状态提示 -->
      <div
        v-if="searchResult.regexError"
        class="rounded-md border border-red-300 bg-red-50 px-3 py-2 text-xs text-red-600 dark:border-red-900 dark:bg-red-950/30 dark:text-red-400"
      >
        {{ t('globalSearch.invalidRegex') }}: {{ searchResult.regexError }}
      </div>
      <div
        v-else-if="query.trim()"
        class="flex items-center justify-between text-xs"
        style="color: var(--app-text-secondary)"
      >
        <span>
          {{
            t('globalSearch.summary', {
              matches: searchResult.totalMatches,
              files: searchResult.groups.length,
            })
          }}
        </span>
        <span v-if="searchResult.truncated" class="opacity-80">
          {{ t('globalSearch.truncated') }}
        </span>
      </div>

      <!-- 结果列表 -->
      <div
        class="max-h-[55vh] overflow-y-auto rounded-lg border"
        style="border-color: var(--app-border); background: var(--app-bg-alt)"
      >
        <div
          v-if="searchableFileCount === 0"
          class="px-4 py-10 text-center text-xs"
          style="color: var(--app-text-dim)"
        >
          {{ t('globalSearch.noSearchableFiles') }}
        </div>
        <div
          v-else-if="!query.trim()"
          class="px-4 py-10 text-center text-xs"
          style="color: var(--app-text-dim)"
        >
          {{ t('globalSearch.hint', { count: searchableFileCount }) }}
        </div>
        <div
          v-else-if="searchResult.groups.length === 0 && !searchResult.regexError"
          class="px-4 py-10 text-center text-xs"
          style="color: var(--app-text-dim)"
        >
          {{ t('globalSearch.noResults') }}
        </div>
        <div v-else class="divide-y" style="border-color: var(--app-border)">
          <div
            v-for="(group, groupIndex) in searchResult.groups"
            :key="group.fileId"
            class="py-1.5"
          >
            <div
              class="flex items-center justify-between px-3 py-1 text-xs font-semibold"
              style="color: var(--app-text-secondary)"
            >
              <span class="truncate">{{ group.relativePath }}</span>
              <span class="count-badge ml-2 shrink-0">{{ group.matches.length }}</span>
            </div>
            <button
              v-for="(match, matchIndex) in group.matches"
              :key="`${match.source}:${match.line}:${match.column}:${matchIndex}`"
              type="button"
              class="flex w-full items-baseline gap-2 px-3 py-1.5 text-left font-mono text-xs transition-colors"
              :style="{
                background:
                  matchFlatIndex(groupIndex, matchIndex) === activeIndex
                    ? 'var(--app-selected)'
                    : 'transparent',
              }"
              @mouseenter="activeIndex = matchFlatIndex(groupIndex, matchIndex)"
              @click="chooseMatch(match)"
            >
              <span
                class="w-12 shrink-0 text-right tabular-nums"
                style="color: var(--app-text-dim)"
              >
                L{{ match.line }}
              </span>
              <span
                v-if="match.source === 'constant'"
                class="shrink-0 rounded px-1 py-0.2 text-[10px]"
                style="background: var(--app-accent-soft); color: var(--app-accent)"
              >
                {{ t('globalSearch.constantBadge') }}
              </span>
              <span class="min-w-0 flex-1 truncate" style="color: var(--app-text)">
                <span>{{ match.preview.slice(0, match.matchStart) }}</span>
                <mark
                  class="rounded-sm px-0.5 font-semibold"
                  style="background: var(--app-accent-soft); color: var(--app-accent)"
                >{{ match.preview.slice(match.matchStart, match.matchEnd) }}</mark>
                <span>{{ match.preview.slice(match.matchEnd) }}</span>
              </span>
            </button>
          </div>
        </div>
      </div>
    </div>
  </NModal>
</template>
