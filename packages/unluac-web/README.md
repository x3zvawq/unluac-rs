# unluac-web

`unluac-rs` 的浏览器端工作区（Vue 3 + TypeScript + Pinia + Naive UI + CodeMirror 6 + WebAssembly）。

## 本地开发

前置环境：Rust（含 `wasm32-unknown-unknown` target）、`wasm-pack` 与 Node.js 24+。

```bash
npm ci
npm run dev      # 启动本地开发服务器（自动编译并同步 WASM）
npm run build    # 构建 WASM + Vite 生产包 + vue-tsc 类型检查
npm run preview  # 本地预览生产构建
```

> `plugins/vite-plugin-wasm-build.ts` 会在启动与构建时自动编译 `packages/unluac-wasm` 并复制到 `src/wasm/`（已加入 `.gitignore`，无需手动提交）。

## 工作区功能概览

- **多文件 / 文件夹导入与打包导出**：支持整页拖拽或文件/目录选择器，基于魔数嗅探自动跳过非字节码文件并识别 7 种 Lua 方言；每个文件独立保存方言设置与 IndexedDB 缓存，支持一键本地打包下载 `.zip`（零第三方依赖）。
- **跨文件全文搜索（`Ctrl/Cmd + Shift + F`）**：同时搜索所有已反编译源码与常量池，支持大小写/正则开关和键盘上下跳转，点击直接定位到目标文件与行号。
- **场景预设与完整设置**：设置抽屉顶部提供「推荐阅读 / 精确还原 / 给 AI 分析」三个一键预设，并开放完整的命名、注释（`minimal` / `full` / `none`）和表格对齐选项，支持一键导出分享链接与对应 CLI 参数。
- **IDE 级源码编辑、对比与 AI 复制**：定制深色/浅色编辑器主题与 28px 底部状态栏（方言、输出状态、行数、proto 数、反编译耗时）；内置 CodeMirror 6 编辑器、`DiffViewer`（对比本地编辑与原始输出，或任意两文件对比）以及「复制给 AI」一键生成精简 Markdown 代码块。
- **结构分析面板**：按需拉取 `decompileRich` 数据，提供**函数大纲（ProtoOutline）/ 调用树（ProtoGraph）双视图切换**（点击函数直接跳转高亮源码区间）、带实时过滤与一键复制的**常量表（ConstantsPanel）**以及**控制流图（CfgViewer，支持 Low-IR / 原始字节码切换）**。

## 测试与检查

```bash
# Node 单元测试（覆盖 7 方言真实 WASM、二进制嗅探、ZIP 生成、Worker 调度/缓存、设置预设、全文搜索与 AI 复制）
npm test

# 代码格式与 lint 检查
npm run check

# Playwright 端到端浏览器测试（需先执行 npm run build 并准备好 lua/build 下编译器）
npx playwright install chromium
npm run test:browser
```

浏览器测试的截图和失败追踪会保存在仓库根目录的 `tmp/web-ui-tests/` 下；可设置 `PLAYWRIGHT_CHANNEL=msedge` 使用本机 Edge，或通过 `WEB_TEST_URL` 指向正在运行的开发服务。

## 目录结构速查

- `src/components/layout/`：`AppHeader`、`FilePanel`、`MainContent`、`WelcomeView`
- `src/components/editor/`：`CodeViewer`（CodeMirror 6 + 定制主题 + 行/区间高亮 + 复制给 AI）、`DiffViewer`（编辑对比与双文件对比）
- `src/components/search/`：`GlobalSearchModal`（跨文件全文与常量搜索）
- `src/components/settings/`：`SettingsDrawer`（场景预设、完整选项、分享链接与 CLI 参数生成）
- `src/components/analysis/`：`ProtoOutline`（函数大纲）、`ProtoGraph`（调用树）、`CfgViewer`（控制流图）、`ConstantsPanel`（常量过滤与复制）
- `src/stores/`：`files.ts`（文件历史与标签状态）、`settings.ts`（选项持久化与预设）
- `src/utils/`：`binarySniff.ts`、`editorTheme.ts`、`zip.ts`、`aiSnippet.ts`、`workspaceSearch.ts`、`keyboard.ts`、`dialects.ts`
- `src/workers/decompile.worker.ts`：WASM 后台反编译 Worker（空工作区不启动，首个文件请求时才按需初始化）
- `src/i18n/`：10 套界面语言包（新增文案需同步维护）
- `src/content/`：首页无 JS 可读的产品介绍 HTML（`product.en.html` / `product.zh.html`）与站点元数据（`site.ts`）

修改 Logo 或品牌文案后，可重新生成分享卡片图 `public/social-card.png`：

```bash
node scripts/generate-social-card.mjs
```

## 部署（Vercel）

线上的构建与发布由 `.github/workflows/deploy-web.yml` 统一完成：Actions 中先编译 Rust/WASM 与前端 `dist`，再上传至 Vercel。`vercel.json` 刻意关闭了 Vercel 自身的 Git 自动构建（避免缺 Rust 工具链报错），Vercel 项目的 Root Directory 设为 `packages/unluac-web` 即可。
