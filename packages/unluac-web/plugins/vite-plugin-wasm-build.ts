/**
 * Vite 插件：在 dev/build 启动前自动构建 WASM 并同步 glue 文件。
 *
 * 避免 WASM 二进制与 JS glue 不同步导致的 LinkError。
 * 构建产物（.js / .d.ts / .wasm）均由 wasm-pack 生成，从 target/wasm-out
 * 复制到 src/wasm/，全部为生成物，不应入库。
 *
 * 额外对 unluac_wasm.js 注入 @ts-self-types 指令，使 TypeScript
 * 在不依赖 moduleResolution bundler 的场景下也能找到类型声明。
 */

import { execSync } from 'node:child_process'
import { copyFileSync, existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs'
import { resolve } from 'node:path'
import type { Plugin } from 'vite'

const WASM_CRATE = 'packages/unluac-wasm'
const WASM_OUT = 'target/wasm-out'

export function wasmBuildPlugin(): Plugin {
  return {
    name: 'unluac-wasm-build',
    // buildStart 在 dev 和 build 模式下都会触发
    buildStart() {
      // plugins/ -> unluac-web/ -> packages/ -> 仓库根
      const root = resolve(__dirname, '../../..')
      const outDir = resolve(root, WASM_OUT)
      const wasmDest = resolve(__dirname, '../src/wasm')

      try {
        console.log('[wasm] Building unluac-wasm...')
        execSync(
          `wasm-pack build ${WASM_CRATE} --target web --out-dir ../../${WASM_OUT}`,
          { cwd: root, stdio: 'inherit' },
        )

        // src/wasm/ 在 fresh clone 后不存在（所有产物均 gitignore），需先创建
        mkdirSync(wasmDest, { recursive: true })

        // 同步产物：全部覆盖，均为生成物
        const filesToCopy: [string, string][] = [
          ['unluac_wasm_bg.wasm', 'unluac_wasm_bg.wasm'],
          ['unluac_wasm_bg.wasm.d.ts', 'unluac_wasm_bg.wasm.d.ts'],
          ['unluac_wasm.d.ts', 'unluac_wasm.d.ts'],
          ['unluac_wasm.js', 'unluac_wasm.js'],
        ]
        for (const [src, dest] of filesToCopy) {
          const srcPath = resolve(outDir, src)
          if (existsSync(srcPath)) {
            copyFileSync(srcPath, resolve(wasmDest, dest))
          }
        }

        // wasm-pack 生成的 .js 不含 @ts-self-types 指令，手动注入
        // 让 TypeScript 在不依赖 bundler moduleResolution 时也能定位类型
        const jsDest = resolve(wasmDest, 'unluac_wasm.js')
        if (existsSync(jsDest)) {
          const content = readFileSync(jsDest, 'utf-8')
          if (!content.startsWith('/* @ts-self-types')) {
            writeFileSync(jsDest, `/* @ts-self-types="./unluac_wasm.d.ts" */\n\n${content}`)
          }
        }

        console.log('[wasm] WASM build and sync complete.')
      } catch (e) {
        console.error('[wasm] WASM build failed:', e)
        // 构建失败时不阻塞 dev server（可能 wasm-pack 未安装），但 build 模式应该阻塞
        if (process.env.NODE_ENV === 'production') {
          throw e
        }
      }
    },
  }
}
