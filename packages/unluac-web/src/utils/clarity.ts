/**
 * Microsoft Clarity 接入。
 *
 * 条件注入 Clarity 脚本，仅在用户 opt-in（默认开启，可在设置中关闭）时加载。
 * 不在开发环境加载。
 */

const CLARITY_PROJECT_ID = import.meta.env.VITE_CLARITY_ID ?? ''

let injected = false

export function injectClarity() {
  if (injected || !CLARITY_PROJECT_ID || import.meta.env.DEV) return
  injected = true

  const script = document.createElement('script')
  script.type = 'text/javascript'
  // Clarity 官方嵌入片段
  script.textContent = `
    (function(c,l,a,r,i,t,y){
      c[a]=c[a]||function(){(c[a].q=c[a].q||[]).push(arguments)};
      t=l.createElement(r);t.async=1;t.src="https://www.clarity.ms/tag/"+i;
      y=l.getElementsByTagName(r)[0];y.parentNode.insertBefore(t,y);
    })(window, document, "clarity", "script", "${CLARITY_PROJECT_ID}");
  `
  document.head.appendChild(script)
}

export function removeClarity() {
  // Clarity 没有官方卸载 API，只能阻止后续数据收集
  // 移除脚本标签不会停止已注入的跟踪，但可以作为最低限度的信号
  const scripts = document.querySelectorAll('script[src*="clarity.ms"]')
  for (const s of scripts) {
    s.remove()
  }
}
