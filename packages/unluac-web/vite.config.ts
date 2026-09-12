import { resolve } from 'node:path'
import tailwindcss from '@tailwindcss/vite'
import vue from '@vitejs/plugin-vue'
import AutoImport from 'unplugin-auto-import/vite'
import IconsResolver from 'unplugin-icons/resolver'
import Icons from 'unplugin-icons/vite'
import { NaiveUiResolver } from 'unplugin-vue-components/resolvers'
import Components from 'unplugin-vue-components/vite'
import { defineConfig } from 'vite'
import packageJson from './package.json'
import { wasmBuildPlugin } from './plugins/vite-plugin-wasm-build'
import { seoPlugin } from './plugins/vite-plugin-seo'

export default defineConfig({
  plugins: [
    seoPlugin(),
    wasmBuildPlugin(),
    vue(),
    tailwindcss(),
    AutoImport({
      imports: [
        'vue',
        'vue-router',
        'pinia',
        {
          'naive-ui': ['useDialog', 'useMessage', 'useNotification', 'useLoadingBar'],
        },
      ],
      resolvers: [IconsResolver({ prefix: 'i' })],
      dts: 'types/auto-imports.d.ts',
    }),
    Components({
      resolvers: [IconsResolver({ prefix: 'i' }), NaiveUiResolver()],
      dts: 'types/components.d.ts',
    }),
    Icons({
      autoInstall: true,
    }),
  ],
  resolve: {
    alias: {
      '@': resolve(__dirname, 'src'),
      '@logo': resolve(__dirname, '../../logo.svg'),
    },
  },
  define: {
    __APP_VERSION__: JSON.stringify(packageJson.version),
  },
  build: {
    target: 'esnext',
    chunkSizeWarningLimit: 800,
  },
  worker: {
    format: 'es',
  },
})
