# 审计问题与交接清单

> 更新时间：2026-08-24
> 审计起点：`main@ce3ad8e`
> 当前复核：`tmp/test/02_control_flow.lua` 的终态 fixed nil pack 已收敛；跨方言 common_11/common_05 与 regress_258 原始比较布尔壳已收敛；本轮新增收回
> fresh 构造器中的标量/布尔字段 producer、相邻单值终态 return alias 与多值 return 中可证明的
> 布尔比较 alias、单值 return 短路前缀中的必达布尔 alias、终态查表短路尾 alias，以及有界短路链展示 alias；抽样仍确认 PUC/Luau/LuaJIT
> 的物理槽、闭包、字段快照、构造器逃逸与 repeat 作用域 residual 没有越过现有安全证明；本轮再收回
> 已由 `literal-fold` 证明为 `Boolean` 的常量 if 外壳（保留 local/诊断/跳转边界）
> 本文件只保留尚未完成、需要后续决策或仍需安全证明的事项；完成项应立即删除。

## Numeric-for capture binding owner

`tests/regress-case/regress_329_closure_self_capture.lua` 在 Lua 5.4 下仍会把 numeric-for body
binding 与同槽 reference capture 分配成两个 `LocalId`：LIR 已正确表达
`closure r4 captures ref(r3); move r3 <- r4`，但
`src/hir/analyze/bindings/captured_slots.rs` 没有把 numeric loop slot 登记为 loop-owned，capture
先得到 `l0`，numeric binding 随后得到 `l1`，最终生成 `assign l1 / capture ref(l0)`。后续应在
captured-slot 的 numeric loop owner 与 per-iteration close epoch 建模中统一身份，不能恢复
`closure-self-capture` simplify pass 兜底。

## Luau self-by-value capture snapshot

Luau VM 明确定义 `NEWCLOSURE rX; CAPTURE VAL rX`：closure 在处理 capture 前已经写入 `rX`，
因此 upvalue 保存 closure 自身的值快照。若后续 bytecode 再覆盖 `rX`，生成源码不能让 child
closure 改为引用同一个可变 local。当前 HIR lowering 会把 self capture 与 fixed target 投影到
同一 `LocalId`，而 AST build 只记录 captured binding、不编码 `HirCaptureMode::ByValue`，存在把
快照变成引用的缺口。后续应为 self-by-value 物化独立稳定 binding，再把 closure result 赋给
真实 target；不能由已删除的 `closure-self-capture` simplify pass 按后续赋值目标猜测。
