# Web 开发与验证

在仓库中准备好 Rust、`wasm-pack` 和 Node.js 24 后，从此目录启动：

```sh
npm ci
npm run dev
```

生产构建和本地预览：

```sh
npm run build
npm run preview
```

页面与 favicon 共享仓库根目录的 `logo.svg`，Vite 会将它作为同一个带内容标识的资源发布。
主题颜色集中在 `src/styles/main.css` 与 `App.vue` 的 Naive UI 主题配置。新增界面文案需同步
`src/i18n/` 的语言资源；动画应遵守 `prefers-reduced-motion`。

工作区支持整页拖入、文件搜索、独立方言标签、源码编辑与下载，以及可折叠的结构分析。
移动端在文件列表与源码之间切换，保持同一个文件面板实例；结构分析默认收起，常量与图视图
分开显示以保留阅读空间。文件历史保存原始字节与方言，手动编辑需下载保存。

## 回归验证

`npm run build` 构建当前核心的 WASM、同步 glue 和引擎身份，再执行 Vite 与 Vue 类型检查。
需要仓库 Rust 工具链与 `wasm-pack`。`npm test` 使用 Node 24 和现有 TypeScript/Vue
依赖，直接加载生产模块验证 Worker 请求、取消、缓存、文件代次与持久化；真实 WASM 测试
还需要先完成 build，并按仓库测试协议初始化 `lua/build` 下的官方 Lua 工具链。

`npm run test:browser` 使用 Playwright 验证生产构建中的导入、混合方言、搜索、设置隔离、
结构分析、编辑撤销、导出和移动端布局。先完成 `npm run build` 并准备 Lua 5.1 / 5.4 编译器：

```sh
npx playwright install chromium
npm run test:browser
```

测试自动启动本地预览服务，截图和失败追踪写入仓库 `tmp/web-ui-tests/`。
可设置 `PLAYWRIGHT_CHANNEL=msedge` 使用本机 Edge，或设置 `WEB_TEST_URL` 验证正在运行的开发服务。

## 搜索与公开内容

`plugins/vite-plugin-seo.ts` 在开发与构建时将 `src/content/product.en.html` 写入首页原始 HTML。
这份正文也由 Vue 欢迎页使用；简体中文界面使用对应的 `product.zh.html`。无需 JavaScript
即可阅读产品介绍、使用方式和常见问题，正常工作区不会为爬虫提供不同的隐藏内容。
空工作区只显示产品内容，首个文件识别请求才创建 Worker 并加载 WASM；历史文件恢复时仍按需处理。
产品正文来自仓库内的静态 HTML，不能将上传内容或外部输入传给这里的 `v-html`。

标题、摘要、canonical、Open Graph、Twitter Card 与 JSON-LD 的公开身份集中在
`src/content/site.ts`。JSON-LD 描述 `WebSite` 与 `SoftwareSourceCode`，不包含虚构评分。
当前只有一个公开页面 URL；浏览器内切换界面语言不会生成独立语言页面，因此不声明虚假的
`hreflang` 页面。`robots.txt` 与 sitemap 允许发现首页；不为参数分享链接重复创建索引条目，
也不使用每次构建都刷新的假 `lastmod`。

`public/social-card.png` 是 1200×630 的分享预览图。修改 Logo 或品牌文案后，在安装
Playwright 浏览器的开发环境中重新生成并提交图片：

```sh
node scripts/generate-social-card.mjs
```

浏览器回归同时检查禁用 JavaScript 的内容与链接、metadata、结构化数据、sitemap、分享图，
以及静态正文与 Vue 页面正文的一致性。

### Google Search Console

代码满足抓取条件并不代表 Google 已经收录。首次接入时：

1. 在 [Search Console](https://search.google.com/search-console/welcome) 添加资源并完成所有权验证。
   域名验证需要将 Google 实际提供的 TXT 记录加入 DNS；URL 前缀验证也可将提供的 HTML
   验证文件原样放到 `public/` 后发布。验证码来自账户，不能在仓库中预先编造。
2. 发布新版后，提交 `https://unluac.x3zvawq.com/sitemap.xml`。
3. 用“网址检查”检查 `https://unluac.x3zvawq.com/`，执行实时测试，确认可抓取后请求编入索引。
   后续依据该工具显示的具体原因处理问题；重复请求并不会加快抓取，也不能保证收录或排名。

Google 的 [JavaScript SEO 说明](https://developers.google.com/search/docs/crawling-indexing/javascript/javascript-seo-basics)
解释了预渲染的作用；[重新抓取说明](https://developers.google.com/search/docs/crawling-indexing/ask-google-to-recrawl)
说明了网址检查、sitemap 与收录边界。

## Vercel 发布

`.github/workflows/deploy-web.yml` 负责安装 Rust/WASM 工具链、构建 `dist`，再通过 Actions
上传到 Vercel。`vercel.json` 的空 `buildCommand` 表示 Vercel 消费已构建产物。

`git.deploymentEnabled: false` 关闭同一仓库的 Vercel Git 自动部署，避免从没有 `dist` 的新
checkout 再启动另一条构建路径；它不关闭 Actions/API 发布。配置含义见
[Vercel 官方说明](https://vercel.com/docs/project-configuration/git-configuration#git.deploymentenabled)。
Vercel 项目的 Root Directory 应指向 `packages/unluac-web`，以便 Git 集成读取这份配置。
若仍出现额外失败部署，检查它的触发来源、项目 Root Directory 和实际构建日志；不要将其他
项目或不同触发器的失败混同为 Actions 构建失败。

## 文件与结果的状态边界

文件方言属于 `FileEntry`，随历史记录保存；导入时从全局默认值取得初始选择，Auto 由核心
Parser 识别后冻结。全局默认方言变化不使旧结果失效，单文件标签修改只重跑该文件。
非方言选项仍触发已有文件重跑，新的结果代次冻结对应参数；rich 分析使用同一个快照。

Worker requestId 与文件 ID、结果 revision 各自承担不同职责。请求 ID 贯穿消息协议，文件 ID
用于归属/取消，revision 验证跨识别、缓存等待和反编译的提交有效性。缓存 key 从实际发布的
WASM 字节、输入文件和参数快照生成一次，写回复用该 key；引擎变化不能命中旧结果。
