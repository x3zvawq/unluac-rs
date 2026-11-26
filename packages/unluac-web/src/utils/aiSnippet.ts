/**
 * 生成适合直接粘贴给 AI 分析的精简代码片段。
 *
 * 去掉大段冗长的 proto 统计头、重复文件头注释与行尾 proto/lines 注释，
 * 保留核心 Lua 源码与简明的文件/方言上下文。
 */

import type { FileStatus, UnluacDialect } from '@/types/decompiler'
import { dialectOptions } from '@/utils/dialects'

const HEADER_BANNER_RE = /^--\s*decompiled by unluac-rs\b.*$/i
const HEADER_META_RE = /^--\s*(?:file|source|dialect|encoding)\s*[:=].*$/i
const STANDALONE_PROTO_COMMENT_RE = /^\s*--\s*proto#\d+\b.*$/
const TRAILING_PROTO_OR_LINES_RE = /\s+--\s*(?:proto#\d+\b.*|lines=\d+-\d+)$/

function dialectLabel(dialect: UnluacDialect): string {
  return dialectOptions.find((option) => option.value === dialect)?.label ?? dialect
}

export function stripVerboseDecompilerComments(code: string): string {
  const lines = code.split(/\r?\n/)
  const out: string[] = []
  let inLeadingHeader = true

  for (const line of lines) {
    const trimmed = line.trim()
    if (inLeadingHeader) {
      if (trimmed === '' && out.length === 0) continue
      if (HEADER_BANNER_RE.test(trimmed) || HEADER_META_RE.test(trimmed)) continue
      inLeadingHeader = false
    }
    if (STANDALONE_PROTO_COMMENT_RE.test(line)) continue
    out.push(line.replace(TRAILING_PROTO_OR_LINES_RE, ''))
  }

  return out
    .join('\n')
    .replace(/\n{3,}/g, '\n\n')
    .trim()
}

export function formatCodeForAi(
  file: { relativePath: string; dialect: UnluacDialect; status: FileStatus },
  code: string,
): string {
  const cleaned = stripVerboseDecompilerComments(code)
  const meta =
    file.status === 'skipped' || file.dialect === 'auto' ? '' : ` (${dialectLabel(file.dialect)})`
  return `File: \`${file.relativePath}\`${meta}\n\`\`\`lua\n${cleaned}\n\`\`\``
}
