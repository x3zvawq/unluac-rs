/**
 * 跨文件全文与常量搜索。
 *
 * 保持纯函数实现，既供全局搜索弹窗实时消费，也便于在 Node 单测里直接覆盖。
 */

import type { FileEntry } from '@/types/decompiler'

export interface WorkspaceSearchMatch {
  fileId: string
  fileName: string
  relativePath: string
  source: 'code' | 'constant'
  /** 1-based line number in decompiled source (0 when unavailable). */
  line: number
  /** 1-based column within the matched line. */
  column: number
  preview: string
  matchStart: number
  matchEnd: number
  protoName?: string
}

export interface WorkspaceSearchFileGroup {
  fileId: string
  fileName: string
  relativePath: string
  matches: WorkspaceSearchMatch[]
  truncated: boolean
}

export interface WorkspaceSearchOptions {
  caseSensitive?: boolean
  useRegex?: boolean
  maxMatchesPerFile?: number
  maxTotalMatches?: number
}

export interface WorkspaceSearchResult {
  groups: WorkspaceSearchFileGroup[]
  totalMatches: number
  truncated: boolean
  regexError?: string
}

const PREVIEW_MAX_LENGTH = 140
const PREVIEW_CONTEXT_BEFORE = 42

function escapeRegExp(text: string): string {
  return text.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')
}

function buildPreview(lineText: string, rawStart: number, rawEnd: number) {
  const leadingTrim = lineText.length - lineText.trimStart().length
  const trimmed = lineText.trim()
  const adjStart = Math.max(0, rawStart - leadingTrim)
  const adjEnd = Math.max(adjStart, Math.min(trimmed.length, rawEnd - leadingTrim))

  if (trimmed.length <= PREVIEW_MAX_LENGTH) {
    return {
      preview: trimmed,
      matchStart: adjStart,
      matchEnd: adjEnd,
    }
  }

  const sliceStart = Math.max(0, adjStart - PREVIEW_CONTEXT_BEFORE)
  const sliceEnd = Math.min(trimmed.length, sliceStart + PREVIEW_MAX_LENGTH)
  const prefix = sliceStart > 0 ? '…' : ''
  const suffix = sliceEnd < trimmed.length ? '…' : ''
  const preview = `${prefix}${trimmed.slice(sliceStart, sliceEnd)}${suffix}`
  const offset = sliceStart - prefix.length
  return {
    preview,
    matchStart: Math.max(0, adjStart - offset),
    matchEnd: Math.min(preview.length, adjEnd - offset),
  }
}

function findFirstMatchInLine(
  text: string,
  matcher: RegExp,
): { start: number; end: number } | null {
  matcher.lastIndex = 0
  const hit = matcher.exec(text)
  if (!hit || hit[0].length === 0) return null
  return { start: hit.index, end: hit.index + hit[0].length }
}

export function searchWorkspaceFiles(
  files: readonly FileEntry[],
  rawQuery: string,
  options: WorkspaceSearchOptions = {},
): WorkspaceSearchResult {
  // 保留有意义的空格（如 ` = ` 或 `return `），仅忽略纯空白输入
  if (rawQuery.trim().length === 0) {
    return { groups: [], totalMatches: 0, truncated: false }
  }
  const query = rawQuery

  const caseSensitive = options.caseSensitive ?? false
  const useRegex = options.useRegex ?? false
  const maxPerFile = options.maxMatchesPerFile ?? 50
  const maxTotal = options.maxTotalMatches ?? 300

  let matcher: RegExp
  try {
    // 统一使用 RegExp 匹配原始字符串，避免 Unicode 大小写折叠改变索引偏移导致高亮错位
    matcher = new RegExp(useRegex ? query : escapeRegExp(query), caseSensitive ? 'gu' : 'giu')
  } catch (error) {
    return {
      groups: [],
      totalMatches: 0,
      truncated: false,
      regexError: error instanceof Error ? error.message : String(error),
    }
  }

  const groups: WorkspaceSearchFileGroup[] = []
  let totalMatches = 0
  let truncated = false

  for (const file of files) {
    if (file.status !== 'success' && file.status !== 'skipped') continue
    const code = file.editedResult ?? file.result
    if (code === undefined) continue

    const matches: WorkspaceSearchMatch[] = []
    let fileTruncated = false
    const matchedCodeTexts = new Set<string>()
    const lines = code.split(/\r?\n/)

    for (let i = 0; i < lines.length; i++) {
      const lineText = lines[i]
      const hit = findFirstMatchInLine(lineText, matcher)
      if (!hit) continue

      if (matches.length >= maxPerFile || totalMatches >= maxTotal) {
        fileTruncated = true
        truncated = true
        break
      }

      const { preview, matchStart, matchEnd } = buildPreview(lineText, hit.start, hit.end)
      matches.push({
        fileId: file.id,
        fileName: file.name,
        relativePath: file.relativePath,
        source: 'code',
        line: i + 1,
        column: hit.start + 1,
        preview,
        matchStart,
        matchEnd,
      })
      matchedCodeTexts.add(lineText)
      totalMatches++
    }

    // 补充搜索已加载的常量池（常用于查找被转义或未直接出现在当前行片段里的字符串常量）
    if (!fileTruncated && file.richResult) {
      const seenConstants = new Set<string>()
      for (const proto of file.richResult.protos) {
        if (fileTruncated) break
        for (const constant of proto.constants) {
          const hit = findFirstMatchInLine(constant.display, matcher)
          if (!hit) continue
          const dedupKey = `${proto.id}:${constant.display}`
          if (seenConstants.has(dedupKey)) continue
          seenConstants.add(dedupKey)
          let alreadyInCode = false
          for (const codeLine of matchedCodeTexts) {
            if (codeLine.includes(constant.display)) {
              alreadyInCode = true
              break
            }
          }
          if (alreadyInCode) continue

          if (matches.length >= maxPerFile || totalMatches >= maxTotal) {
            fileTruncated = true
            truncated = true
            break
          }

          const { preview, matchStart, matchEnd } = buildPreview(
            constant.display,
            hit.start,
            hit.end,
          )
          const targetLine =
            proto.generatedLineStart && proto.generatedLineStart > 0
              ? proto.generatedLineStart
              : proto.lineStart > 0
                ? proto.lineStart
                : 1
          matches.push({
            fileId: file.id,
            fileName: file.name,
            relativePath: file.relativePath,
            source: 'constant',
            line: targetLine,
            column: 1,
            preview,
            matchStart,
            matchEnd,
            protoName: proto.name ?? `Proto #${proto.id}`,
          })
          totalMatches++
        }
      }
    }

    if (matches.length > 0) {
      groups.push({
        fileId: file.id,
        fileName: file.name,
        relativePath: file.relativePath,
        matches,
        truncated: fileTruncated,
      })
    }

    if (totalMatches >= maxTotal) {
      truncated = true
      break
    }
  }

  return { groups, totalMatches, truncated }
}
