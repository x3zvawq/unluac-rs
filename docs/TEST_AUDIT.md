# 测试集审计记录（2026-09-11）

本文记录本轮测试集审计的范围、证据与剩余边界；分层协议见 `design/11.test.md`。
通过记录只适用于下面明确列出的工作区版本和验证范围。

## 已核实基线

审计快照为 `755916e9`：磁盘有 730 个 Lua 源码，manifest 有 730 条不同源码路径（unit 27，
regression 703）；878 条静态 matrix entry 展开为 3,165 个测试实例。该快照中无未注册源码、无指向
不存在文件的 manifest path，也没有跨 manifest 分片重复的 path。

已进行三层重复检查：源码字节 SHA-256、统一换行/删注释行和空白/仅抹稳定输出标签后的保守文本、以及
包含 path/dialect/options/variant/expectation 的 canonical manifest entry。三者均未发现重复组。这只能
排除所检查的文本重复，不能证明两个不同 case 没有语义重叠；GC、Close、debug、方言协议与运行时探针
不同的两个案例不能因文件形状相似而合并。

manifest 仍按编号百位分片，所有路径都在所属分片的编号范围。历史上有 36 组重复数字前缀，但完整文件名
和 manifest path 唯一。重编号会同时改变路径、case filter、诊断和历史定位，且没有已证实的重复可消除；
因此只应为未来 case 分配大于当前最大编号的新号，不机械重排旧文件。

## 可读性合同补充

新增三种文本次数指令和三种 AST 次数指令，支持 dialect/debug/variant 筛选及 AST proto 作用域。
AST 指标直接读取最终 readability AST，避免把字符串、注释或变量名误当成语法结构。每次需要 AST
检查时仅遍历一次，再复用整个模块与各 proto 的统计；选择器覆盖在 runner 列表阶段按源码检查一次。

原有 70 个源码样例新增 100 条合同；另新增断言协议样例和有限循环语义回归。四份 literal 迁移所保留的
旧断言不计入新增。当前候选树有 732 个源码、1,962 条指令，566 个文件带可读性断言；相应基线为
730、1,846、519。仍有 166 个文件无可读性指令，不能将其已有运行时/协议断言视为无意义，也不能宣称
本轮已经为所有文件建立完整的可读性或语义合同。

首次全量探索执行 3,168 个实例，3,103 通过、65 项在新 readability 检查处失败。64 项来自本轮新要求
不准确：例如 debug 剥离后的合法 scope 消去、repeat 与 while 的规范化、误认 for 类型，以及 LuaJIT
与 PUC 不同的 proto 编号。这些新增要求根据实际结构纠正，未删除原有断言、失败源码或收敛预算。
另外撤回了无依据的 `empty-local <= 80` 和与目标无关的 call 次数要求。

剩余一项为 `regress_280` 的 Luau 内层 break 被写成 continue。原样例只观察 `type(run)`，未执行该
循环路径。新增 `regress_642` 用有限外循环和 `__index` 计数观察尾条件：最小复现原程序输出 `3, 0`，
错误反编译输出 `3, 2`。根因是 Structure 的 continue 分类没有追到单条 Jump pad 后已冻结的内层
break owner；在原分类 helper 补齐单跳查询后，原输入与输出均为 `3, 0`。

`regress_642` 保留七种方言，以及 Luau O0/O1/O2、stripped/retained 共 18 个配置。它进一步暴露了
Luau O2 + retained 的循环计数回写缺失；首次定向 28 项中该项超时，其余 27 项通过。首次 HIR 即出现
`continue; x = next_x`，并非命名造成：Structure 的残余跳转转换没有绑定 latch pad 上的 phi 动作。
修复复用最终 continue owner 与 `ContinueLatch` 路径，使 pad 入口保留为内部过渡，回边赋值按既有
action 计划执行；
修复后的 642 矩阵 18/18 通过。两处实现修复均在 Structure 的原 owner，未另建 HIR/AST 补救路径。

断言协议另做了 16 项反向注入：错误 exact/min/max、不存在的 proto、非法参数、重复/未知 selector、
零匹配的配置选择器均被拒绝。注入后样例按字节恢复，stripped/retained/ignored 三项重新通过。

## 已审阅的字面量迁移

下列四个基础字面量合同从独立 regression 入口迁为独立 unit 文件，保留原方言矩阵和源码级断言，不合并进
大型 `common_*` 文件：

| 原 regression | 新 unit case | 方言矩阵 |
| --- | --- | --- |
| `regress_55_leading_newline_string.lua` | `literal_leading_newline_string.lua` | `ALL_DIALECTS` |
| `regress_56_negative_zero_float.lua` | `literal_negative_zero_float.lua` | `PUC_LUA_GE_53` |
| `regress_57_utf8_control_string.lua` | `literal_utf8_control_string.lua` | `ALL_DIALECTS` |
| `regress_58_binary_string_bytes.lua` | `literal_binary_string_bytes.lua` | `ALL_NON_LUAU_DIALECTS` |

这四项是字面量输出的稳定基础合同，迁移后仍可单文件过滤。此映射不推导出其他 regression 可以按名称或
相似度迁入 unit；涉及已修复根因、GC、Close、debug、控制流所有权或 VM 协议的 case 保持回归身份。

## 仍需保持或补充的事实

readability 文本/AST 合同可保护机械形状、重复中转和词法结构，却不是语义证明。后续 case 审阅仍须保留或
补充以下可观察事实：

- 调用、索引、构造器和多返回的求值次数、顺序与 frame 边界；
- metamethod、错误路径、短路值、闭包 capture 和 cell identity；
- 物理 root 的退休时点、弱表 GC 观察、`<close>` 的关闭顺序及 scope；
- stripped/retained/ignored debug 和 Luau 优化档之间的实际差异；
- 残余、source-kind、重编译收敛和每个 target dialect 的官方执行等价。

不能以 `empty-local = 0`、任意 call 数量，或“生成源码更短”替代上述证明。需要按 case 的原 VM carrier 和
最早的事实 owner 选择运行时探针、manifest variant 或 structure contract。

## 最终验证

最终 manifest 有 885 条静态 entry，runner 实际展开 3,186 个配置（unit 146，regression 3,040），
与源码统计一致。相比 3,165 的基线，断言协议新增 3 项、642 新增 18 项；四份 literal 迁移不改变总数。

| 验证 | 实际结果 | 完整日志 |
| --- | --- | --- |
| `cargo unit-test --jobs 8` | 3,186/3,186；2,048/2,048 proto；0 失败、0 超时 | `tmp/test/audit.readability-suite.final.txt` |
| 642 定向矩阵 | 18/18，含 Luau 三档优化与两种 debug 状态 | `tmp/test/regress_642_fixed_matrix.txt` |
| 断言引擎反向注入 | 16/16 按预期拒绝；恢复后协议样例 3/3 通过 | `tmp/test/audit.assertion-negative.txt` |
| 全工作区 Clippy | `--workspace --all-targets --all-features --locked -- -D warnings` 通过 | `tmp/test/audit.readability.clippy.txt` |
| WASM | `cargo check -p unluac-wasm --target wasm32-unknown-unknown --locked` 通过 | `tmp/test/audit.readability.wasm.txt` |
| 差异空白检查 | `git diff --check` 通过 | — |

完整矩阵包含新增、补充断言及迁移的全部实例；各 case 按原 manifest 的 roundtrip/收敛预算执行，
没有修改既有 `recompile_rounds`。通过结果不外推为全部 Lua 程序的等价证明，也不把本轮未出现失败
解释为所有潜在可读性缺口已经闭合。

详细静态统计位于 `tmp/test/audit-suite-inventory/final-source-stats.json`。`tmp/` 是本地诊断产物，
不作为测试运行的依赖；可长期复现的输入与断言已保留在注册的 Lua 源码中。

## 2026-09-13：残余诊断断言的执行覆盖

继续审计发现选择器匹配不等于断言执行：`UnsupportedIsland` 路径未读取源码断言，
`GlobalDeclResidual` 则把首次 Permissive 结果作为非首次检查，跳过了 contains/order、
exact/min 次数以及所有 AST 指标。使用现有注册样例反向注入六项错误要求，修复前六项均返回成功。

现在专用残余入口对首次 Permissive 产物执行完整断言；未改变 Strict 错误种类和诊断源码类型要求。
295 与两份 410 mixed-global 样例新增六条诊断标记/AST Error 合同，三项定向配置通过；
同一组反向注入修复后六项全部报告 `readability-assertion-failed`，随后按字节恢复源码。
对应日志为 `tmp/test/audit.residual-before-probes.txt`、`tmp/test/audit.residual-after-probes.txt`
和 `tmp/test/audit.residual-focused.txt`。

`TableSetListResidual` 入口同步接入相同检查，但当前 manifest 无该 expectation 的注册条目，
因此本轮未对这条路径宣称运行覆盖。`ProtoFailureRecovery` 原本先执行普通 Source 测试，
其源码断言已经执行；注入失败后的恢复结构继续由既有专用合同负责。

本次全量 `cargo unit-test --jobs 8`：3,186/3,186 配置、2,048/2,048 proto 通过，无失败、无超时
（`tmp/test/audit.residual-full.txt`）。全工作区 Clippy 与本次文件的 `git diff --check` 通过。
没有修改核心库、WASM 接口或依赖，本轮未重复 WASM 构建。当前可读性指令较上一节增加六条至 1,968，
带断言文件增加一份至 567；源码样例和配置数量不变。

## 2026-09-13：无注册消费者的残余测试入口清理

核对 type-only 循环样例时，268 已执行唯一正常结束的参数路径；280 的有界运行差异由 642 覆盖。
本轮没有据此宣称发现新的反编译错误。

随后确认 `TableSetListResidual` 仅剩私有 expectation 枚举、分派分支及专用执行/报错函数，
没有任何 manifest 构造项或其他调用方。已删除这套不可达测试入口，共 104 行；核心 AST 的
`table-set-list` 残余拒绝及 Permissive 诊断能力、现有 SETLIST 源码样例均保留。
前一节所述“同步接入但没有运行覆盖”的入口因此不再存在。

删除前后从各自 Cargo artifact 获取的 runner `--list` 逐字一致，均为 3,186 项。
326、327、421、432 的普通 SETLIST 样例，以及 295 和两份 410 mixed-global 的有效残余合同，
共 18/18 配置通过；全工作区 Clippy 和差异检查通过。日志位于
`tmp/test/audit.dead-contract-focused.txt`、`tmp/test/audit.dead-contract-clippy.txt`，列表位于
`tmp/test/audit.dead-contract-{before,after}-list.txt`。
本轮只删除无实例可达的测试分支，未更改有效执行路径、核心库或依赖；未重复全量运行和 WASM 构建。

## 2026-09-13：循环退出的独立运行观察

新增两个基础 unit case，而不是把已闭合的 642 再复制成回归：

- `common_15_loop_exit_observations.lua` 用三个开关遍历八种内外层 break 组合，比较累计值和
  repeat 尾条件的完整调用序列。预期结果由有限 for 展开计算，避免重复待测 while/repeat 控制流。
  七种方言、Luau O0/O1/O2、stripped/retained 共 18 个配置；Lua 5.4 另检查目标 proto 的循环结构。
- `luau_03_loop_continue_actions.lua` 遍历四种 skip/stop 组合，比较累计值、尾条件事件序列和最终
  循环计数。它区分 while continue 回入口与 repeat continue 仍求值尾条件的行为，覆盖 Luau 三档
  优化及两种 debug 状态，共六个配置；保留 while/repeat 结构断言，O2 另约束 continue。

初拟的无条件 `continue >= 1` 在 O0/O1 四项失败。当前生成代码把跳过剩余循环体恢复为条件块，
repeat 尾条件仍在条件块外，属于合法且清晰的等价表示。因此这条新断言限定在 O2，运行 oracle
与循环结构检查仍对全部配置执行；没有更改旧回归断言、超时或收敛预算。

定向 24/24 配置及 24/24 proto 通过；完整 unit suite 170/170 配置、723/723 proto 通过，无失败、
无超时。全工作区 Clippy 通过。本轮只新增源码和 manifest 注册，未修改核心库或共享测试执行逻辑，
未重复 regression 全矩阵与 WASM 构建。日志为 `tmp/test/audit.loop-contracts.{focused,unit,clippy}.txt`。

Terra 独立审计在 `tmp/test/continue-latch-audit/` 保留九个临时 Luau O2+g2 探针。
其中七项生成可执行源码，官方 VM 的源/生成执行均正常退出且 stdout 逐字一致；覆盖双回边状态、
兄弟 break pad、内层 while、原生 continue 及索引事件。它们不是已注册矩阵，不能计入上述通过数。

另外两项返回明确标记的诊断伪代码，属于尚未修复的支持缺口，不能解释为通过或可执行错码：

- `deep_nested_breaks.lua`：Structure 报 `loop condition terminals contradict frozen syntax roles`。
  诊断文本在 VM 中退出码为零但输出不同；SourceKind 已标记失败，退出码不是成功依据。
- `inline_deep_repeat.lua`：HIR 报 `requires unavailable goto/label`；诊断文本执行失败。
  文件名不构成已经发生内联的证据，尚未定位首次事实丢失或证明拒绝。

两项使用下列独立源码形状可重新构造；官方 Luau `--binary -O2 -g2` 编译后交给 CLI `-i ... -D luau`。
前一个复现如下，不能因为其诊断输出能运行而注册为成功 residual 合同：

```lua
local function run(mode)
    local step, x, reads = 0, 0, 0
    local xs = setmetatable({}, {__index = function() reads += 1; return true end})
    while step < 3 do
        step += 1
        x += 1
        repeat
            repeat
                if mode == 1 and step == 2 then break end
                if mode == 2 then break end
            until xs[step]
            if mode ~= 3 then break end
        until xs[step]
    end
    return step, x, reads
end
for mode = 1, 3 do
    local step, x, reads = run(mode)
    print("deep", mode, step, x, reads)
end
```

后一个保持相同的 while/双 repeat 骨架，把内层分支换成
`if b then if c then break else print("unexpected-inner") end end; if d then break end`，
外层分支换成 `if a then break end`。`run(a,b,c,d,xs)` 返回 step/x，在 ipairs 循环中分别以
`{true,true,true,true}`、`{true,true,false,true}`、`{true,false,false,true}` 调用，xs 由外层相同的
计数型 `__index` 表传入。这两项尚未缩减、注册或修复，下一步应先定位原 Structure owner；
不能放宽冻结角色或 goto guard 来消除诊断。

## 2026-09-13：嵌套退出的早期 continue 身份

`deep_nested_breaks` 的首次矛盾已追到 `loops/continue_edges.rs`：两条内层循环出口
（原 proto#1 的 #13/#15）经 pad 接到外层 while latch，被提前标为 `Continue(outer)`。
循环细化已经依据完整六节点短路 DAG 确定 repeat；最终 condition selection 却因这份错误
continue 证据拒绝合并终端动作，改选同 header 的两节点正文条件。冻结时两条终端均在正文内，
于是报出上一节的语法角色矛盾。临时探针明确记录两份 `PreliminaryEdgeAction` 的
`has_continue_evidence=true`，而 phi inputs 为空；不是值动作不相等。

修复在原 continue 候选 owner 的直接分支和线性 arm 两个签发点，消费现有 natural-loop forest
的唯一内层身份和祖先区间查询，阻止内层退出被提前签发为祖先 continue。每次查询常数成本，
没有新建 membership 表或逐边搜索循环域；最终 region 仍决定具体退出语法。条件终端 guard、
repeat 协议拒绝以及后层语义分类均未放宽。

注册 `regress_643_nested_exit_condition_owner.lua`，保留双回边状态与索引读取计数，并对三条
实际执行路径断言最终 step/x 为 3、reads 分别为 2/0/6。18 个配置包含全部方言、Luau O0/O1/O2
及 stripped/retained；Luau 同时检查 repeat 和无 goto 结构。643、642、common_15 与 luau_03
共 60/60 配置及 60/60 proto 通过，无失败、无超时，日志为
`tmp/test/audit.condition-owner.focused.txt`。

集中全量 `cargo unit-test --jobs 8` 为 3,228/3,228 配置、2,090/2,090 proto 通过，无失败、
无超时；全工作区 Clippy、WASM `wasm32-unknown-unknown` 检查与差异检查通过。完整日志为
`tmp/test/audit.condition-owner.{full,clippy,wasm}.txt`。临时诊断打印已移除，最终核心修改只在
`loops/continue_edges.rs`，没有修改条件选择或降低其断言。

另一个 goto 支持缺口由 Terra 缩减为下列源码；官方 Luau `--binary -O2 -g2` 后仍为诊断伪代码。
移除外层 while、phi 和表尾条件并未消除它，因此不是本次祖先 continue 身份修复的同根问题：

```lua
local function run(a, b, c, d)
    repeat
        repeat
            if b then
                if c then break else print("m6-tail") end
            end
        until d
    until a
end
run(true, true, true, true)
run(true, true, false, true)
```

该 proto 的 natural loop 只有 header #0、两条回边 #8/#11；当前 plan 是 Unknown loop 加 island，
edge #0 与 #4 被冻结成 `irreducible-flow` goto。单层 repeat 对照能够正常恢复。
这仅证明共享入口的双 repeat 支持仍不完整，不证明 CFG 数学上不可规约，也不证明必须重新拆成
两个源码 loop。后续应从 Structure 候选与 region 分区证明选择合法表示，不能让 HIR 猜跳转归属。

## 2026-09-13：共享入口双 repeat 的分区证明

继续复核上述最小样例，首次漏覆盖在 `partition_repeat_like_natural_loop` 调用的嵌套判定：
已有分析能区分内层 backedge #8 和外层 backedge #11，但旧规则对分支 header 要求恰好一个
后继在 residual 内；最小样例的 #1/#4 都在内层，因此没有生成已有机制支持的 child/outer 候选。

现在只对“两条入口边都在内层”的形状补充证明：内层域严格且单入口，非空退出经单跳/清理 pad
归一到外层域内的唯一入口，该入口位于内层外并支配外层已知尾条件。短路条件的入口可以早于
continue target 末叶；`until a or xs[step]` 仍从 a 开始判断，不会直接进入 xs 的求值。实现复用
原自然循环分区、透明 pad 和支配查询，未增加逐候选可达图搜索，也未在 HIR 中替换 goto。

第一版额外证明未要求两条入口边都在内层，169 的五个 PUC 配置因此触发既有可读性断言。
保留这些断言并补齐入口域约束后，644 与 169 的 23 项全部通过；没有删除负例或调整预算。

- `regress_644_shared_repeat_body_branch.lua` 注册最小形状，经过表调用使 Luau O2 保留待测函数的
  实际执行；三条参数路径分别覆盖跳过 if、内层 break 和有副作用的 else。
- `regress_645_shared_repeat_short_exit.lua` 保留原始较大样例的外层 while、两份回边状态和短路
  尾条件，并运行 16 种布尔组合。以独立有限展开的索引序列检查求值次数与顺序，避免只比较结束值。

两份 case 各注册 18 个配置，包含所有方言、Luau 三档优化及 stripped/retained，并对 Luau 目标
proto 要求双 repeat、全模块无 goto。644/645、103/128 的相邻嵌套正例、135/169/170/176 的控制
边界样例及 643，共 94/94 配置、87/87 proto 通过，无失败、无超时；日志为
`tmp/test/audit.shared-repeat.focused-final.txt`。当前源码重建 CLI 后，原始 `inline_deep_repeat`
探针也生成正常双 repeat 源码，645 进一步提供已注册的运行与重编译验证。

集中全量 `cargo unit-test --jobs 8`：3,264/3,264 配置、2,126/2,126 proto 通过，无失败、无超时。
全工作区 Clippy、WASM `wasm32-unknown-unknown` 及差异检查通过；完整日志为
`tmp/test/audit.shared-repeat.{full,clippy,wasm}.txt`。两项此前记录的临时循环支持缺口现均有修复和
注册回归；这不代表所有样例的可读性合同或长期系统审计已完成。

## 2026-09-13：方言语法指标与不可观察的运行结果

本轮从当前无可读性指令的 165 个文件中审阅方言 unit 与四个早期 regression，没有把已有 GC、
生命周期或专用 residual 合同判为无效。新增三项 AST 指标，使指标总数为 21：`close-binding`、
`global-decl`、`named-vararg-function`。仍从最终 readability AST 一次遍历收集，不解析生成文本。
计数单位和父/子 proto 边界已写入 `design/11.test.md`。

四个方言 unit 补充关闭绑定、global 声明、命名变参以及可规约 goto 的结构合同；goto 约束只作用于
已检查的可规约 proto，未套到不可规约网格。协议样例新增三项零计数，并打印含相应语法的字符串，
证明文本中的关键字不会被算成 AST 节点。12 项定向配置、74 项 proto 通过。
另分别注入错误 close-binding exact、global-decl max 和 named-vararg-function min，三个探针
均被 `readability-assertion-failed` 拒绝，随后按字节恢复源码；日志为
`tmp/test/audit.dialect-metrics.{protocol,negative}.txt`。

GPT-5.6 Sol 只读审阅四个早期回归，主侧整合并验证：

- 09 只约束原生 generic-for，不把当前物理 home 准备链冻结为文本。其源码注释所述 escaped-root
  生命周期尚无本 case 的 GC/弱引用观察，不能把这个结构断言称为生命周期证明，也未据此报告错码。
- 147 新增三项调用展示顺序合同；现有 log 输出继续检查运行时求值顺序。
- 179 原 Luau 配置将长度与相等比较全部折成常量，两个目标字符串没有进入 Generate。最终 print
  现在同时携带原字符串，七种方言实际生成它们，并由两项分隔符断言与编译/执行检查保护边界。
- 207 原源码只返回 chunk 结果，进程 stdout/退出码比较不观察返回值。现保留 80 参数宽链，显式
  断言并打印未命中、尾部命中、中部命中和首部优先四条路径；目标 proto 的 if/goto 为零，父 proto
  保留唯一函数。增加运行观察后 PUC 合法采用 local 赋函数表达式，故本轮新合同使用 `function`
  计数，不强制 `local-function` 拼写；旧断言及预算没有降低。

四个回归合计 22/22 配置通过，细分日志为 `tmp/test/audit.dialect-metrics.early.txt`、
`tmp/test/audit.dialect-metrics.literal-carrier.txt` 和 `tmp/test/audit.dialect-metrics.wide-chain-final.txt`。
本轮新增 23 条指令，八份原无指令文件获得针对性合同；当前 737 个源码文件中仍有 157 份无指令。
源码/manifest 配置数未变化，没有按数字前缀重编号或删除语义未证明重复的样例。

集中全量 `cargo unit-test --jobs 8`：3,264/3,264 配置、2,133/2,133 proto 通过，无失败、无超时；
全工作区 Clippy 通过，日志为 `tmp/test/audit.dialect-metrics.{full,clippy}.txt`。本轮只修改测试支持、
样例与测试文档，未修改核心实现、依赖或 WASM 接口，未重跑 WASM 检查。

207 的发现还提示继续检查只返回 chunk 值、没有可观察输出的普通 case。静态候选清单位于
`tmp/test/audit.no-visible-oracle-candidates.txt`；该列表仅按文本筛选，包含专用 expectation、
间接输出或压力测试，不能直接当作失效测试名单，后续必须逐项核对 manifest 和真实执行。

## 2026-09-13：早期回归的实际调用与运行观察

核对 manifest 和 `support/pipeline.rs` 后，03/04/05/11_branch/63/64/65/69/70/72 均为普通
Source expectation、Lua 5.1 stripped 配置。03/04/11/63/64/65/69/70 原来没有执行被测函数，
05/72 仅返回结果且没有可观察输出。原展示合同仍有效，但不能据此声称对应行为已有运行验证。

保留十份样例的被测逻辑及全部旧可读性断言，在原文件补入观察：03 检查事件分支、回调次数和
含 nil 的三返回值；04 检查非函数短路和 Lua 真值；05 归一化无序 hits 并逐项检查材料分支；
11 检查优先分支、各闭包的独立 needed 与共享对象更新；63/64 检查四返回值、fallback 次数、
global 写入和无效边界；65 刻意区分捕获 owner 与调用 receiver。69 通过已有 yield 边界观察
队列消费，70 在下一轮入口的回调暂停并观察上轮状态，两者均有限次恢复且不修改原无限循环。
72 显式断言并打印退出结果。

65 的新增观察最初使用冒号调用，合法触发冒号声明恢复而与原点号声明合同冲突。新增调用改用
`owner.read(owner)` 后通过，未删除或降低旧断言。七个有限函数样例还分别在 tmp 中注入返回值、
分支动作或对象身份错误，七个单点变异均被 runtime assertion 拒绝；探针不改仓库原文件。

定向注册验证合计 10/10 配置、11/11 proto 通过，无失败、无超时；日志为
`tmp/test/audit.runtime-oracles.{focused-final,loops,negative}.txt`。本主题只改变 case 与文档，
未修改 manifest、runner 或核心实现，未重复运行全量、Clippy 和 WASM。

进一步审计 common_12 后，新增字节观察在其六个注册方言全部触发 generated-chunk-execution-failed，
证明存在被旧无输出样例掩盖的字符串语义问题；该问题转入 Generate 字面量 owner 单独修复。

## 2026-09-13：生成字符串的原始字节身份

common_12 原来只调用并丢弃 GBK 字符串，文本合同要求输出 `"中文"`。给返回值添加长度与逐字节
断言后，六个原注册方言均在生成产物执行时失败；独立 CLI/runtime 探针也确认原输出为
`4 214 208 206 196`，生成输出变成 `6 228 184 173 230 150 135`。这是实际不等价，
不是单纯的显示编码差别。原失败日志为 `tmp/test/audit.string-bytes.before.txt`。

RawString/LuaString 一直持有正确原始字节，首次错误消费位于 Generate 的 `emit/syntax.rs`：
长括号选择、引号正文和转义成本均优先使用 `preferred_text`，把 GBK 展示视图当成 UTF-8 源码值。
三个决策点现统一消费 `as_utf8()` 的原字节视图，非 UTF-8 继续使用原有逐字节十进制转义；
未引入新编码通道或深拷贝。解码视图保留用于元数据与调试展示。

原要求将 GBK 字节输出成 UTF-8 中文的合同与运行语义冲突，已改为精确 GBK 字节转义合同；
另加入真正 UTF-8 字节并要求它仍显示为中文且只出现一次，避免用全转义掩盖可读性退化。
同一 unit 覆盖非 UTF-8 换行、引号、数字续接和 NUL/高位二进制字节，均逐字节断言并输出。
Luau 无实际编译/运行限制，故将已有 unit 扩为 ALL_DIALECTS，保留单份源码。

原六方言及相邻字面量 69/69 配置、26/26 proto 通过；扩入 Luau 后 common_12 的 7/7 配置、
14/14 proto 通过。另对 auto、显式 GBK、显式 UTF-8 各自可解析输入，组合三种引号策略，
九项 Lua 5.4 CLI/runtime 字节输出均与源程序一致。显式 GBK 仍按 Parser 合同拒绝不可解码的
任意二进制字节，未改变该选项行为。日志为 `tmp/test/audit.string-bytes.{focused,all-dialects,options}.txt`。

集中全量 `cargo unit-test --jobs 8`：3,265/3,265 配置、2,158/2,158 proto 通过，无失败、无超时。
全工作区 Clippy、WASM `wasm32-unknown-unknown` 和差异检查通过；日志为
`tmp/test/audit.string-bytes.{full,clippy,wasm}.txt`。这是当前实现的验证结果，长期覆盖审计仍未完成。

后续运行观察候选仍有 120/123/124/128/131 的返回函数、320 的深闭包链、324 的未调用方法、
402_function_sugar_nested_local_ids 的未调用构造器，以及 extraarg/133 的宽常量边界。
这些目前是覆盖缺口，不是已确认错码。410 的两个 GlobalDeclResidual 样例通过专用协议验证，
509 通过 report 间接输出，不能因文本检索未发现 print/assert 而判作无效或删除。
其余候选的 manifest/执行路径证据及建议观察入口见临时审阅记录 `tmp/runtime_coverage_audit_sol.md`。

## 2026-09-13：宽常量、返回函数与延迟回调的运行观察

沿上一轮候选补强八份现有源码，未修改原被测函数体或旧可读性断言，也未新增副本或 manifest
配置。普通 Source 的执行入口仍按现有协议比较输出和退出状态，观察逻辑放在各 case 内：

- `lua52_03_extraarg_boundary` 在巨表及 marker 之后逐项断言 262145 个值，并打印 SETLIST 边界
  两侧与最后一个值。使用官方 Lua 5.2 反汇编比较，新增观察前后指令 1..272124 完全一致，包含
  原数组 SETLIST 和 LOADKX/EXTRAARG 常量 262145；新 global/string 常量位于原边界之后。
  保留压力样例原 `recompile_rounds=0`，没有增加预算。
- 123 经表调用遍历三个布尔输入的八种组合，检查两臂结果；新增 if 数量上限保护不再拆散，
  不要求永远保留可等价简化的三个 if。124 观察空、一项、四项迭代域的 break 与正常退出路径；
  两种非终止参数组合仅用于空域，未声称执行其无限循环体。
- 128 执行跳过 while 与 inner break 两种有限路径，检查零返回宽度，并用 AST 数量保护原主题的
  一层 repeat 与一层 while。131 检查匿名变参零参数、单 nil、对象及中间/末尾 nil 的四返回宽度，
  要求 named-vararg-function 为零。
- 320 逐层调用 300 次，到达最终值 0，并要求 300 个函数节点，确保深 proto 压力未被观察代码消去。
- 324 用独立列出的期望表检查九条渠道、状态、等级路径，同时检查 open/official/require/lv 顺序，
  验证短路不会提前加载 player。402_function_sugar 区分 begin 与 finish 的 receiver，保存回调并在
  build 返回后执行，检查 token 身份与 begin/finish/side/use 顺序；原链式展示断言仍通过。

定向注册验证共 14/14 配置、14/14 proto 通过，无失败、无超时；123 最终采用 if 上限后再次通过。
八份 tmp 副本分别注入边界元素、返回值、变参宽度或调用参数错误，八个单点变异均被运行断言拒绝。
日志为 `tmp/test/audit.returned-functions.{focused,callbacks,shape-final,negative}.txt`；原边界指令
比较见 `tmp/test/audit.extraarg-observation-layout.txt`。本主题仅 case/文档修改，未重复运行全量、
Clippy 或 WASM，也没有借上一轮全量结果宣称本轮全量通过。

本轮未发现新的反编译语义反例。120 仍需为非终止路径设计有意义的观察方式；132/133 已有精确
文本合同，但 chunk 返回值尚未观察，其中 133 不能用无参时恒为 false 的比较充当宽操作数证明。

## 2026-09-13：剩余返回值与有限循环观察

132 改为显式检查正负无限复数的实部为零、虚部分别为正负 math.huge，再输出各分量；原 numeric
token 三条合同保留。133 将原 vararg chunk 的完整主体放进独立 compare proto，父 proto 提供
命中、低字节错误常量、末项 padding 与 nil 输入，并观察 sink。官方 LuaJIT 反汇编确认前后全部
269 条目标指令一致，ISEQS 的 D 仍为 260，错误截断到低字节 4 仍会引用 padding-005。

133 的“比较不得拆成机械 local”合同随被测 proto 从 0 迁移到 1 更新名字，并增加目标 proto 的
if 为零合同；没有降低比较展示要求。未命中输入用 string.format 在父 proto 构造，避免测试载体
自身引入 padding-005 字面量与原禁止错误常量的断言冲突。正负号错误与 D 截断错误的 tmp 变异
分别被运行断言拒绝。

120 根据 Sol 只读审阅补入 pcall 和带 __index 的表，分别执行 a=true 时的 break/continue 路径，
检查结果 3 与索引序列 1,2,3。pcall 使 Luau O2 保留被测函数；正式载体与原样例的 O2 stripped
Function 0 反汇编完全一致。索引偏移一位的 tmp 变异被新增断言拒绝。
该观察保护 x 的跨轮携带、查表次数和顺序及有限终止；a=false 的非终止分支仍未执行。
在这组 a=true 输入下，某些错误 continue 归属可以行为等价，不能用通过结果声称证明全部 owner；
原 repeat/continue/break 和禁止 goto 的结构合同继续保留，没有用超时或人为异常扩大证据。

另确认基础 `literal_binary_string_bytes` 在当前 Luau 可保留目标字面量并正确执行，将该独立 unit
扩为 ALL_DIALECTS，未复制源码。10/10 注册配置、3/3 输出 proto 检查通过，无失败、无超时；
Clippy 通过。仅 case/manifest/文档变化，未重复全量或 WASM。日志为
`tmp/test/audit.remaining-observers.{focused,loop,luajit-negative,loop-negative,clippy}.txt`；
字节码布局证据为 `tmp/test/audit.wide-compare-layout.txt` 与 `tmp/test/audit.loop120-layout.txt`。

本轮未发现新的语义反例。静态“没有显式 print/assert”候选已逐项补观察或确认专用/间接观察协议，
但这不意味着所有函数与路径已覆盖。另筛选 type 输出时确认 268 已有限调用 run，280 的无限循环
仍主要由自身结构断言及已有有限反例 642 保护；不能把 type(run) 输出单独称作循环运行验证。
