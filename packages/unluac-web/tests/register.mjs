// Load production TypeScript directly for Node's browser-boundary tests.
import { registerHooks } from 'node:module'
import { readFileSync, existsSync } from 'node:fs'
import { fileURLToPath, pathToFileURL } from 'node:url'
import ts from 'typescript'

registerHooks({
  resolve(specifier, context, next) {
    let url
    if (specifier.startsWith('@/')) url = new URL(`../src/${specifier.slice(2)}`, import.meta.url)
    else if (specifier.startsWith('.') && context.parentURL?.endsWith('.ts')) url = new URL(specifier, context.parentURL)
    if (url && !existsSync(url) && existsSync(`${fileURLToPath(url)}.ts`)) url = pathToFileURL(`${fileURLToPath(url)}.ts`)
    return next(url?.href ?? specifier, context)
  },
  load(url, context, next) {
    if (!url.endsWith('.ts')) return next(url, context)
    return { format: 'module', shortCircuit: true, source: ts.transpileModule(readFileSync(new URL(url), 'utf8'), {
      compilerOptions: { target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ESNext },
    }).outputText }
  },
})
