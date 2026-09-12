import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'
import type { Plugin } from 'vite'
import { site } from '../src/content/site'

/** 静态 HTML 和 Vue 欢迎页复用产品正文，让抓取不依赖 JS / WASM 初始化。 */
export function seoPlugin(): Plugin {
  const contentPath = resolve(__dirname, '../src/content/product.en.html')
  return {
    name: 'unluac-seo',
    transformIndexHtml: {
      order: 'pre',
      handler(html) {
        const graph = {
          '@context': 'https://schema.org',
          '@graph': [
            {
              '@type': 'WebSite', '@id': `${site.url}#website`,
              name: site.name, alternateName: 'unluac-rs Lua Decompiler', url: site.url,
            },
            {
              '@type': 'SoftwareSourceCode', '@id': `${site.url}#software`,
              name: site.name, url: site.url, description: site.description,
              codeRepository: site.repository,
              programmingLanguage: ['Rust', 'TypeScript'],
              runtimePlatform: ['Rust', 'WebAssembly'],
              license: `${site.repository}/blob/main/LICENSE.txt`,
              isAccessibleForFree: true,
              sameAs: [site.repository, 'https://crates.io/crates/unluac', 'https://www.npmjs.com/package/unluac-js'],
            },
          ],
        }
        return {
          html: html.replace('<!-- product-overview -->', readFileSync(contentPath, 'utf8')),
          tags: [
            { tag: 'title', children: site.title },
            { tag: 'meta', attrs: { name: 'description', content: site.description } },
            { tag: 'link', attrs: { rel: 'canonical', href: site.url } },
            ...Object.entries({
              'og:type': 'website', 'og:url': site.url, 'og:title': site.title,
              'og:description': site.description, 'og:site_name': site.name,
              'og:locale': 'en_US', 'og:image': site.image,
              'og:image:type': 'image/png', 'og:image:width': '1200', 'og:image:height': '630',
              'og:image:alt': 'unluac-rs — Lua bytecode, made readable. Lua 5.1–5.5, LuaJIT and Luau.',
            }).map(([property, content]) => ({ tag: 'meta', attrs: { property, content } })),
            ...Object.entries({
              'twitter:card': 'summary_large_image', 'twitter:title': site.title,
              'twitter:description': site.description, 'twitter:image': site.image,
              'twitter:image:alt': 'unluac-rs Lua decompiler',
            }).map(([name, content]) => ({ tag: 'meta', attrs: { name, content } })),
            { tag: 'script', attrs: { type: 'application/ld+json' }, children: JSON.stringify(graph).replace(/</g, '\\u003c') },
          ],
        }
      },
    },
  }
}
