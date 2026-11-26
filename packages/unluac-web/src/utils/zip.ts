/**
 * 零依赖标准 ZIP（Store / 无压缩）打包器，用于客户端一键导出多文件工作区。
 *
 * 保留目录层级并自动消解同名碰撞（例如 foo.luac 与 foo.lua 同存时保留 foo.luac.lua）。
 */

export interface ZipInputEntry {
  path: string
  content: string | Uint8Array
}

const CRC32_TABLE = (() => {
  const table = new Uint32Array(256)
  for (let i = 0; i < 256; i++) {
    let c = i
    for (let j = 0; j < 8; j++) {
      c = (c & 1) !== 0 ? 0xedb88320 ^ (c >>> 1) : c >>> 1
    }
    table[i] = c >>> 0
  }
  return table
})()

function crc32(bytes: Uint8Array): number {
  let c = 0xffffffff
  for (let i = 0; i < bytes.length; i++) {
    c = CRC32_TABLE[(c ^ bytes[i]) & 0xff] ^ (c >>> 8)
  }
  return (c ^ 0xffffffff) >>> 0
}

/** 为一批工作区相对路径计算无碰撞的 `.lua` 导出路径 */
export function resolveLuaExportPaths(relativePaths: readonly string[]): string[] {
  const normalized = relativePaths.map(
    (raw) =>
      raw
        .replace(/\\/g, '/')
        .replace(/^\/+/, '')
        .split('/')
        .filter((seg) => seg && seg !== '.' && seg !== '..')
        .join('/') || 'output',
  )

  const stemCounts = new Map<string, number>()
  const baseTargets = normalized.map((p) => {
    const slash = p.lastIndexOf('/')
    const dir = slash >= 0 ? p.slice(0, slash + 1) : ''
    const file = slash >= 0 ? p.slice(slash + 1) : p
    const stem = file.replace(/\.[^.]+$/, '')
    const candidate = `${dir}${stem}.lua`
    stemCounts.set(candidate, (stemCounts.get(candidate) ?? 0) + 1)
    return { orig: p, candidate }
  })

  const used = new Set<string>()
  return baseTargets.map(({ orig, candidate }) => {
    let chosen =
      (stemCounts.get(candidate) ?? 0) > 1 && !orig.endsWith('.lua') ? `${orig}.lua` : candidate
    if (used.has(chosen)) {
      const base = chosen.replace(/\.lua$/, '')
      let idx = 2
      while (used.has(`${base}_${idx}.lua`)) idx++
      chosen = `${base}_${idx}.lua`
    }
    used.add(chosen)
    return chosen
  })
}

export function buildZip(entries: readonly ZipInputEntry[]): Uint8Array {
  const encoder = new TextEncoder()
  const now = new Date()
  const dosTime =
    ((now.getHours() & 0x1f) << 11) |
    ((now.getMinutes() & 0x3f) << 5) |
    ((now.getSeconds() >> 1) & 0x1f)
  const dosDate =
    (((Math.max(1980, now.getFullYear()) - 1980) & 0x7f) << 9) |
    (((now.getMonth() + 1) & 0x0f) << 5) |
    (now.getDate() & 0x1f)

  const localParts: Uint8Array[] = []
  const centralParts: Uint8Array[] = []
  let offset = 0

  for (const entry of entries) {
    const nameBytes = encoder.encode(entry.path)
    const dataBytes =
      typeof entry.content === 'string' ? encoder.encode(entry.content) : entry.content
    const checksum = crc32(dataBytes)

    // Local file header (30 bytes + filename + data)
    const localHeader = new Uint8Array(30 + nameBytes.length)
    const lv = new DataView(localHeader.buffer)
    lv.setUint32(0, 0x04034b50, true)
    lv.setUint16(4, 20, true) // version needed: 2.0
    lv.setUint16(6, 0x0800, true) // UTF-8 filename flag
    lv.setUint16(8, 0, true) // method: store
    lv.setUint16(10, dosTime, true)
    lv.setUint16(12, dosDate, true)
    lv.setUint32(14, checksum, true)
    lv.setUint32(18, dataBytes.length, true)
    lv.setUint32(22, dataBytes.length, true)
    lv.setUint16(26, nameBytes.length, true)
    lv.setUint16(28, 0, true)
    localHeader.set(nameBytes, 30)

    localParts.push(localHeader, dataBytes)

    // Central directory header (46 bytes + filename)
    const central = new Uint8Array(46 + nameBytes.length)
    const cv = new DataView(central.buffer)
    cv.setUint32(0, 0x02014b50, true)
    cv.setUint16(4, 20, true)
    cv.setUint16(6, 20, true)
    cv.setUint16(8, 0x0800, true)
    cv.setUint16(10, 0, true)
    cv.setUint16(12, dosTime, true)
    cv.setUint16(14, dosDate, true)
    cv.setUint32(16, checksum, true)
    cv.setUint32(20, dataBytes.length, true)
    cv.setUint32(24, dataBytes.length, true)
    cv.setUint16(28, nameBytes.length, true)
    cv.setUint16(30, 0, true)
    cv.setUint16(32, 0, true)
    cv.setUint16(34, 0, true)
    cv.setUint16(36, 0, true)
    cv.setUint32(38, 0, true)
    cv.setUint32(42, offset, true)
    central.set(nameBytes, 46)
    centralParts.push(central)

    offset += localHeader.length + dataBytes.length
  }

  let centralSize = 0
  for (const part of centralParts) centralSize += part.length

  // End of central directory (22 bytes)
  const eocd = new Uint8Array(22)
  const ev = new DataView(eocd.buffer)
  ev.setUint32(0, 0x06054b50, true)
  ev.setUint16(4, 0, true)
  ev.setUint16(6, 0, true)
  ev.setUint16(8, entries.length, true)
  ev.setUint16(10, entries.length, true)
  ev.setUint32(12, centralSize, true)
  ev.setUint32(16, offset, true)
  ev.setUint16(20, 0, true)

  const total = offset + centralSize + eocd.length
  const out = new Uint8Array(total)
  let cursor = 0
  for (const part of localParts) {
    out.set(part, cursor)
    cursor += part.length
  }
  for (const part of centralParts) {
    out.set(part, cursor)
    cursor += part.length
  }
  out.set(eocd, cursor)
  return out
}
