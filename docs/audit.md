# 审计问题与交接清单

> 更新时间：2026-08-24
> 审计起点：`main@ce3ad8e`
> 当前复核：跨方言 common_11/common_05 与 regress_258 原始比较布尔壳已收敛；本轮新增收回
> fresh 构造器中的标量/布尔字段 producer、相邻单值终态 return alias 与多值 return 中可证明的
> 布尔比较 alias、单值 return 短路前缀中的必达布尔 alias，以及终态查表短路尾 alias；抽样仍确认 PUC/Luau/LuaJIT
> 的物理槽、闭包、字段快照、构造器逃逸与 repeat 作用域 residual 没有越过现有安全证明
> 本文件只保留尚未完成、需要后续决策或仍需安全证明的事项；完成项应立即删除。

## 审计规则

1. **宽松生成必须保留**：结构恢复不完整时，用户仍应看到尽可能多的逻辑。宽松模式允许保留必要的 `goto` / `label` 和 `unluac error` 占位；严格模式要求目标方言可重新编译。
2. **诊断写入输出，不写 stderr**：诊断伪源码由首行 `unluac error` 注释和 `GeneratedChunkKind::DiagnosticPseudocode` 标识，不额外打印目标方言警告。
3. **错误注释不能删除**：它保留其余可读逻辑，也让用户能定位反编译器缺口。
4. **安全证明优先于形状断言**：任何内联、构造器折叠、binding 合并或 root 缩短，都必须同时证明求值顺序、词法身份、GC 存活和目标方言语义；无法证明时保留机械形状或返回诊断。

## 待处理问题

当前没有待处理项。已经证明属于 VM/源码表达边界或精确语义证据的数据结构不再作为可读性
优化缺口登记；只有出现新的等价性证明或真实错误复现时才重新立项。本轮抽样确认的
call-result logical self-update、`common_11` 的调用结果短路壳、`regress_282` 长 `or` 链、
call→field、闭包/字段快照与构造器 wiring 都保留原形：其中长链首值已由 HIR 标为 `PhysicalRoot`，不能按普通
`Recovered` alias 缩短。构造器字段 write 不再被错误计作独立 producer，但调用/查表/闭包
字段仍由 region evaluator 和 root/follow-up gate 保留；跨运行时执行差异（例如用 PUC Lua
执行 Luau 产物）不作为 Luau correctness 证据。本轮还抽样复核了 Luau O0/O1/O2 中
`local comparison; assert(alias)`、循环/分支状态 alias 与长短路值合流：直接调用可覆盖的
全局 `assert` 会改变 global lookup 与比较元方法的相对时点，循环项会改变重复求值或写回，
合流项则缺少稳定 HIR owner；这些形状继续保留机械 local，不再作为可读性待办。
另外，`regress_20` 的 `local lookup; return lookup or literal` 已证明可在同一终态表达式中
安全收回：只允许 stripped/recovered binding 与无事件短路尾，调用尾、debug local、物理根
和多返回/其它 return 位点仍保留，因此不把 call→field 等 residual 扩大到这条规则。

本轮抽样（2026-08-24）再复核了所有 PUC Lua 5.1–5.5、LuaJIT 与 Luau 的
`common_02#2`、`common_13#4`，以及 LuaJIT `luajit_01#2/#4` 和 Lua 5.4
`lua54_01_close` 的直接赋值别名。`common_02#2` 的 `local carried = seed` 是
while 到 numeric-for 的 loop-carried owner 交接；虽然该样例的常量路径最终只产生数值，
当前 HIR 仍未向 AST 暴露可复用的 `(home slot, close epoch)` 与源码 binding 生命周期证明，
AST 不能凭文本把两个 owner 合并。`common_13#4` 的 `call-result = closure` 以及
LuaJIT 两例的 `match/tonumber` 结果覆盖则会改变旧调用结果的物理 root 存活期；若调用被
替换为可返回带 `__gc` 的 userdata，删除覆盖即可让后续 `collectgarbage` 观察到不同的
finalizer 时点。Lua 5.4 的 `collectgarbage`/字段快照同样受全局查找和 producer 求值顺序
保护。另抽查 `regress_279` 的 `local r1_2 = r1_1`：别名跨嵌套 repeat，且后续
`until` 查表和外层 break 共同决定写回时点；即使当前样例初值为数值，也不能用普通
stable-copy 规则缩短。上述形状因此确认为预期 residual，不新增待办，也不再按普通
alias 规则尝试。

随后抽查新加入的 `regress_318`–`regress_321`：`regress_318` 的恒真 guard 已收敛为最小
`while true`/`break` 结构，`regress_321` 的右结合共享 fallback 已恢复为单一短路表达式；
`regress_319` 的 Luau diamond 仍需保留各闭包 occurrence 的 identity/capture 证据，不能
按函数体相似度合并；`regress_320` 的 300 层嵌套 proto 是输入本身的 lexical scope，输出
换行只是结构化排版，没有可安全压平的绑定变换。因此这批样例也没有新增可证明安全的可读性
改写项。

## 当前验证基线

- `cargo fmt --all -- --check`：通过。
- `cargo clippy --workspace --all-targets --all-features --locked -- -D warnings`：通过。
- `cargo test --workspace --all-targets --locked`：通过。
- `cargo unit-test --suite all --recompile-rounds 2 --jobs 8 --progress off`：1271/1271 entries
  通过，`timed_out=0`；1748/1748 proto 通过。
