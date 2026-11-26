/**
 * 轻量二进制嗅探：区分纯文本 Lua 源码与明显非字节码的二进制资产（如 PNG、ZIP、加密包）。
 *
 * 空文件（0 字节）视为合法空源码，兼容空 .lua 文件导入。
 */

const SNIFF_LIMIT = 4096

export function looksLikeBinaryFile(bytes: Uint8Array): boolean {
  if (bytes.length === 0) return false
  const len = Math.min(bytes.length, SNIFF_LIMIT)
  let controlCount = 0

  for (let i = 0; i < len; i++) {
    const b = bytes[i]
    // NUL 字节几乎不会出现在普通 Lua 源码文本中
    if (b === 0) return true
    // 允许常见空白/控制字符：\t(9), \n(10), \x0c(12), \r(13), ESC(27)
    if (b < 0x09 || (b >= 0x0e && b <= 0x1f && b !== 0x1b)) {
      controlCount++
    }
  }

  return controlCount / len > 0.1
}
