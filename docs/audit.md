# 审计问题与交接清单

> 更新时间：2026-08-24
> 审计起点：`main@ce3ad8e`
> 当前复核：`tmp/test/02_control_flow.lua` 的终态 fixed nil pack 已收敛；跨方言 common_11/common_05 与 regress_258 原始比较布尔壳已收敛；本轮新增收回
> fresh 构造器中的标量/布尔字段 producer、相邻单值终态 return alias 与多值 return 中可证明的
> 布尔比较 alias、单值 return 短路前缀中的必达布尔 alias、终态查表短路尾 alias，以及有界短路链展示 alias；抽样仍确认 PUC/Luau/LuaJIT
> 的物理槽、闭包、字段快照、构造器逃逸与 repeat 作用域 residual 没有越过现有安全证明；本轮再收回
> 已由 `literal-fold` 证明为 `Boolean` 的常量 if 外壳（保留 local/诊断/跳转边界）
> 本文件只保留尚未完成、需要后续决策或仍需安全证明的事项；完成项应立即删除。

## 本轮审计归档（2026-08-24）

- `tmp/test/02_control_flow.lua` / `regress_323_terminal_nil_return_pack`：`first_positive` 的
  终态 `Temp, Temp = nil, nil; return Temp, Temp` 已由 HIR `temp-inline` 收回为 `return nil, nil`。
  证明限制为同 block 紧邻 fixed return、临时目标唯一读取、trusted home 不冲突且无 debug/capture；
  proto 有 `<close>`/`Close` 资源事实或 home compaction 时整条规则停用。nil 只清空内部槽并返回
  固定宽度，不移动任何 call/lookup/global/metamethod、短路、循环或多返回 tail 事件；PUC Lua
  5.1–5.5、LuaJIT 与 Luau 回归及 round-trip 均通过。`until #values < index` 仍保留：字节码
  只给出比较谓词/寄存器顺序，无法唯一证明原始 `>` 拼写；当前条件两侧已是 producer 快照，
  不再为该展示差异添加文本特判。

- `regress_127_puc54_metamethod_operand_flip`：`inline-exprs` 原先只按整棵 AST
  复杂度拒绝终态 `local value = E; return value`。HIR/AST 已证明它是 recovered、唯一
  相邻单值 return、无后续写入/捕获/PhysicalRoot/`<close>`，因此仅按有限 `..` 段重新计费，
  不改变 `name`/`type` 查找、调用、concat 元方法或返回时点；默认预算下收回，用户降低
  `return_inline_max_complexity` 时仍保留原 local。
- `regress_80_same_header_nested_loops` / `regress_302_luau_numeric_for_multi_read_binding`：
  `logical-simplify` 仅在 Luau 方言下
  折叠有限、排除负零、`|n| <= 2^53` 的原始且整数值 numeric literal（`Integer` 或整数值
  `Number`）加法，并输出 `Number`。该范围内 VM
  数值快路径不查用户元方法，后序折叠不移动任何绑定、capture、root 或控制流事件；PUC、
  LuaJIT、非字面量、非有限数和舍入边界均保留原运算。
- `regress_234_nested_phi_short_value_merge`：HIR 已将分支值合流固定为单次求值的 `and/or`
  表达式，但默认完整节点预算会留下 `local value = E; return value`。Readability 仅对顶层
  最多 12 个有限、每个复杂度不超过 3 的短路叶按项计费；规则 40 的 recovered/唯一相邻单值
  return、write/capture/eval-prefix、call/lookup/global/metamethod、single/multi/vararg、
  debug/PhysicalRoot、GC/`<close>` 和控制流门槛均未放宽。故所有原始变量读取、短路跳过、
  比较/元方法与返回事件仍在同一顺序和同一返回点执行；仅删除机械 local。PUC 5.1–5.5、
  LuaJIT 与 round-trip 产物均覆盖该形状。
- `regress_315_nested_fallback_value_merge`：HIR/`logical-simplify` 已把严格的原始字面量
  比较收回 `Boolean(true)`，但首轮 `branch-pretty` 早于 `literal-fold`，留下 `if true then`
  与不可达 fallback。`branch-pretty` 现在订阅 `ExprShape` 并在下一轮消费该显式事实；条件
  没有运行时求值，未选 arm 的 lookup/call/assignment 不会发生。选中 arm 含 recovered local，
  因而保留一个 `do` 作用域；诊断、label/goto、break/continue、方言 `GlobalDecl` 或
  DebugHinted/PhysicalRoot/local-function/captured binding 任一存在时整壳保留，分别避免
  丢失诊断、改变 loop owner、移动 global 声明范围或削弱 binding identity。普通 recovered
  local 的选中 arm 仍以 `do` 保持词法域；`<close>`/GC root、单值/多值与原有 arm 内事件
  顺序均未改变。
- `regress_90_degenerate_numeric_for_nested_while` / `regress_116_luau_numeric_for_shared_nested_preheader`：
  HIR 路径事实会留下 `not true` / `not false` 的无事件 Boolean 壳。`literal-fold` 现在只把
  这两个显式字面量归一为 `false` / `true`，不触碰 HIR loop owner、body、break/continue
  edge 或嵌套作用域；因此 #90 仍保留 `while` 结构哨兵，#116 仅改善为 `while true`。
- LuaJIT `regress_55_leading_newline_string` / `regress_58_binary_string_bytes`：未证明安全，
  继续作为 residual。`#value` 位于多值 return 的 fixed prefix 时，跨 opaque call 移动会
  改变求值顺序；LuaJIT 的 `debug.setlocal` 可实际改写 caller slot，当前 HIR 没有 raw-length
  producer 与 debug/opaque-write 排除事实，故不在 AST 增加特判。只有新增通用 HIR 事实或真实
  错误复现后才重新立项。
- `tmp/test/01_alias_and_sugar.lua` / `regress_322_alias_and_sugar`：该样例的安全部分已经
  收敛为 `p.first .. " " .. p.last`、记录式 table constructor 和直接的局部函数声明；
  stripped 输出中的 `r0_*` 只是没有 debug 名时的默认 `debug-like` 命名，可用
  `--naming-mode heuristic` 改善观感，但不属于语义 pass。HIR 的 `method_name` 现在会
  跨 AST 普通 `Call` 保留，constructor 不再吞掉同一 fresh owner 上已有 method 事实的
  字段闭包，因此首轮输出可恢复 `function r2_0:add(...)` / `function r2_0:value_text()`。
  这只是字段写的 canonical spelling，不是对原始冒号源码的猜测；round-trip 后若调用已
  退化为普通点调用，字节码没有办法重新提供该事实，允许回到字段函数形状。
  顶层 low-IR 仍是 `r0_3:add(2)`、`r0_6:add(3)`、`r0_7.value_text`、`r0_6(...)`，但
  `SELF` 不是普通的 `GETTABLE + CALL`：VM 先执行
  `MOVE (A + 1) <- B` 覆盖隐式 `self` 槽，再用该快照做字段查找，`CALL` 随后消费同一
  槽。因此 `method=true/method_name` 足以证明 receiver 的一次求值、lookup 顺序和隐式
  首参协议；它不提供跨调用的 result identity，也不自动把旧 home 在下一次 `SELF` 中的
  覆盖与 lookup 时点配成一个可消费的 intra-call epoch。当前 promotion facts
  虽保留 trusted home/epoch 和相邻 MOVE 的写集合，`temp-inline` 融合 setup 后仍没有把
  “lookup 前的 SELF 覆盖”与“CALL 结果写回”区分给后层，因而只能把相关值保守标为
  `PhysicalRoot`。

  这使“只删最后两句”不能从 `SELF` 单独推出。可复现的 Lua 5.1 反例是：`first()` 返回带
  `__gc` 的 userdata，`second()` 返回另一个带 `__gc` 的 userdata，最终
  `__index.value_text` 先执行 `collectgarbage("collect")` 再记录日志。原始
  `object:first():second():value_text()` 在最终 lookup 内可观察到
  `first-result`；当前展开形状
  `first_result = object:first(); second_result = first_result:second();
  first_result = second_result.value_text; first_result(second_result)` 的 lookup 内日志
  为空，显式 collection 后才看到首个 finalizer。把它改成
  `second_result:value_text()` 又得到另一种存活时点。也就是说，删除/移动
  `r0_6` 的 home 覆盖会改变弱表、`__gc`、自动 GC 或 lookup metamethod 的观察。
  当前样例里的 `add` 虽然表面上每条路径都 `return self`，HIR 还没有把确切 closure
  occurrence、字段单写/逃逸和 return-self identity 作为可消费的通用事实；不能用这个
  case 的常量路径替代证明。这并不表示完整链恢复必须依赖 `return self`；若未来 HIR
  保留每次 `SELF` 的 receiver snapshot 与 lookup 前覆盖，嵌套链可以按原始结果逐次传递，
  但那仍须是覆盖/求值顺序的原子事务。因此末尾仍保留
  `r0_6 = r0_7.value_text; r0_6(r0_7)`，不新增 AST 文本特判。只有前层同时保留
  `SELF` snapshot/overwrite provenance，并能原子重建整条 method chain 时，才值得重新立项。

## 审计规则

1. **宽松生成必须保留**：结构恢复不完整时，用户仍应看到尽可能多的逻辑。宽松模式允许保留必要的 `goto` / `label` 和 `unluac error` 占位；严格模式要求目标方言可重新编译。
2. **诊断写入输出，不写 stderr**：诊断伪源码由首行 `unluac error` 注释和 `GeneratedChunkKind::DiagnosticPseudocode` 标识，不额外打印目标方言警告。
3. **错误注释不能删除**：它保留其余可读逻辑，也让用户能定位反编译器缺口。
4. **安全证明优先于形状断言**：任何内联、构造器折叠、binding 合并或 root 缩短，都必须同时证明求值顺序、词法身份、GC 存活和目标方言语义；无法证明时保留机械形状或返回诊断。

## 待处理问题

当前没有待处理项。已经证明属于 VM/源码表达边界或精确语义证据的数据结构不再作为可读性
优化缺口登记；只有出现新的等价性证明或真实错误复现时才重新立项。本轮还用匹配的 PUC
Lua 5.1 toolchain 复核了 `SELF` 的隐式槽覆盖与 `__gc` 观察：method provenance 是真实
证据，但不足以删除 `PhysicalRoot`/field alias，故该候选继续归档为 HIR snapshot/overwrite
事实缺口，而不是 AST 漏收。本轮抽样确认的
call-result logical self-update、`common_11` 的调用结果短路壳、`regress_282` 长 `or` 链、
call→field、闭包/字段快照与构造器 wiring 都保留原形：其中长链首值已由 HIR 标为 `PhysicalRoot`，不能按普通
`Recovered` alias 缩短。构造器字段 write 不再被错误计作独立 producer，但调用/查表/闭包
字段仍由 region evaluator 和 root/follow-up gate 保留；跨运行时执行差异（例如用 PUC Lua
执行 Luau 产物）不作为 Luau correctness 证据。本轮还抽样复核了 Luau O0/O1/O2 中
`local comparison; assert(alias)`、循环/分支状态 alias 与长短路值合流：直接调用可覆盖的
全局 `assert` 会改变 global lookup 与比较元方法的相对时点，循环项会改变重复求值或写回，
合流项则缺少稳定 HIR owner；这些形状继续保留机械 local，不再作为可读性待办。
`regress_90_degenerate_numeric_for_nested_while` 的 Luau inner while 虽由路径事实使正文
为空，但当前 HIR 没有可复用的 loop-owner/外部跳转证明，且回归明确保护嵌套循环壳；只
归一条件、不删除循环。`regress_258_short_circuit_subject_ownership` 的 `if true` 外壳同样
仍携带 TempRef owner/capture 边界，保留为 residual。
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
