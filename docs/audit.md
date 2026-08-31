# 审计问题与交接清单

> 更新时间：2026-08-24
> 审计起点：`main@ce3ad8e`
> 当前复核：`tmp/test/02_control_flow.lua` 的终态 fixed nil pack 已收敛；跨方言 common_11/common_05 与 regress_258 原始比较布尔壳已收敛；本轮新增收回
> fresh 构造器中的标量/布尔字段 producer、相邻单值终态 return alias 与多值 return 中可证明的
> 布尔比较 alias、单值 return 短路前缀中的必达布尔 alias、终态查表短路尾 alias，以及有界短路链展示 alias；抽样仍确认 PUC/Luau/LuaJIT
> 的物理槽、闭包、字段快照、构造器逃逸与 repeat 作用域 residual 没有越过现有安全证明；本轮再收回
> 已由 `literal-fold` 证明为 `Boolean` 的常量 if 外壳（保留 local/诊断/跳转边界）
> 本文件只保留尚未完成、需要后续决策或仍需安全证明的事项；完成项应立即删除。
