# 审计问题与交接清单

> 更新时间：2026-08-22
> 审计起点：`main@ce3ad8e`（本轮 observable condition carrier 复核前）
> 当前复核：`main@2698c81`（physical call-root lifetime 主题已收口）
> 本文只记录尚未解决且已经取证的问题、明确风险和已确认的设计决定；完成项立即删除。

## 不应回退的决定

1. **宽松生成必须保留**：结构恢复不完整时，用户仍应看到尽可能多的逻辑。宽松模式允许保留必要的 `goto` / `label` 和 `unluac error` 占位；严格模式才要求目标方言可重新编译。
2. **诊断写入输出，不写 stderr**：诊断伪源码由首行 `unluac error` 注释和 `GeneratedChunkKind::DiagnosticPseudocode` 标识，不再额外打印“目标方言不支持 goto/label”的 stderr 警告。
3. **错误注释不能删除**：它既保留其余可读逻辑，也让用户能定位并反馈反编译器缺口。
4. **允许高价值大改**：涉及层次职责、核心数据模型和跨 pass owner 时，直接替换错误架构，不保留兼容层、双轨事实或后层 fallback。

## 未解决问题

1. **LuaJIT `ISTYPE/ISNUM` 尚无严格源码表达**：官方 `LJLIB_LUA` 内建函数用这两条指令实现 `CHECK_str/func/tab/int/num`；失败路径调用 `lj_meta_istype`。Transformer/HIR 已保留 guard 的读取、顺序、具体 expected type，以及 string/integer/number 原槽转换后的 SSA def；function/table 仍是纯检查。官方 opcode/type-id 矩阵之外的组合会 typed fail-fast。宽松模式能继续恢复余下函数，严格模式会拒绝 unresolved guard；但直接生成 `assert(type(...))` / `tonumber(...)` 会依赖可覆盖全局且不满足 LuaJIT 的错误与 `int32` 转换合同，不能冒充等价源码。后续若要关闭此项，需要先确定一个目标方言 helper 合同或正式的内建伪源码输出模式。
2. **Luau 递归词法 factory owner self-capture 尚只安全拒绝**：官方 Luau 0.713 `-O2` 会稳定生成 owner `DUPCLOSURE` 对自身目标寄存器的 `CAPTURE VAL`，再把该 owner 传给重复 captured shared site。当前 HIR shared-closure matcher 不会把 owner 创建前的 `Entry(reg)` 与创建后的 `Def(reg)` 猜成同一 identity，稳定返回 `UnrepresentableRepeatedCapturedSharedClosure`，不会 panic 或误编译；synthetic DAG 内的直接 self-capture 同样 fail-fast，避免退化成 `NEWCLOSURE CAPTURE REF` 后改变对象相等性。关闭此项需要在 HIR plan 显式建模 `OwnerSelf`，并证明 occurrence 精确捕获该 owner def；不能全局合并前后 SSA identity，也不能在 AST 用 function sugar 兜底。
3. **natural-loop 成员合同仍会在深层嵌套上展开为二次 incidence**：最终 StructurePlan 的 branch domain、edge/phi/cleanup validator 已改为稠密索引和区间，但 `cfg/graph.rs::compute_natural_loops` 仍为每个 header 反向物化完整 `NaturalLoop.blocks`，随后 `loops.rs`、`goto.rs`、`branches.rs` 和 `plan/arena.rs::LoopPartitions` 又把每个 block 展开到全部祖先 loop。普通编译器受语法嵌套上限约束，现有 corpus 与 16k 顺序分支压力样例不会触发灾难性退化；人工构造的深层可规约 CFG 仍可达到 Θ(blocks × loop-depth) 时间与内存。要关闭此项，需要一次独立 `perf(structure)` 主重构：用 LLVM LoopInfo 风格的子 loop 收缩构建 `NaturalLoopForest`，保存唯一 `innermost_by_block + loop parent + direct blocks`；Structure 再建立 canonical semantic loop forest 和 dense `LoopPart`，删除 `LoopCandidate.blocks/body_scope_blocks/control_blocks`、逐候选 subset/clone 以及每 loop 的 body BFS。DSU 实现的严谨复杂度是 `O((blocks + edges) α(blocks))`，不能继续在文档或交付说明中把这条尚未完成的 evidence 路径声称为纯线性。
   同一主题还包括 `hir/analyze/bindings.rs::region_blocks`：它目前为每个嵌套 loop
   重新枚举 body subtree，并把外围 for binding 展开到每个后代 block。后续应让
   binding owner 直接挂在 region/loop forest 上，由 lowering 按 ancestor stack 查询，
   不再复制 `loop × descendant block` 映射。
4. **合法 Luau 深原型与当前递归 tree pipeline 不兼容**：pinned Luau 能生成主 proto 深度 999 的合法平面表；当前输入在约 300 层进入 Structure 时会系统栈溢出。Parser 已把所有 dialect 的 raw proto 深度统一限制为 200，使畸形或过深输入稳定返回 `ParseError`；这只是安全闭环，不是完整 Luau 兼容。关闭此项需要把 `RawProto -> LoweredProto -> Cfg/Graph/Dataflow/StructureFacts -> HIR` 的跨 proto 调度改为索引 arena 上的迭代后序遍历，再按实测安全边界放宽 Luau。相同重构还应消除 `build_proto_tree` 把共享 flat-proto DAG 递归克隆成潜在指数级 tree 的风险。
5. **HIR capture 跨 key 图遍历仍可受不同 epoch 数放大**：当 `K` 个不同 `(slot, epoch)` 都覆盖整张 CFG 时，逐 key 反向写后数据流仍为 `O(K×(blocks+edges))`；不同 capture root 也可能重复遍历同一大型 normal-phi ancestry。普通编译器输出受寄存器数和词法 epoch domain 限制，但人工构造输入仍可放大此路径。关闭此项需要利用 epoch 的 dominator domain 限制反向传播范围，并对 normal phi graph 做 SCC 后的 earliest-def memo，不能建立 `key×block` 持久矩阵。
6. **Luau captured-shared component matcher 对人工共享 DAG 仍可能二次展开**：owner 对 root occurrence 的支配检查已折成每组一次 NCA 包络，词法 scope 也先按稠密 region memo 与 containment DFS 左右端点冻结，Move identity 统一使用 `CanonicalMoveIndex`；但 `shared_closures.rs::match_component` 仍需为每个 root occurrence 递归验证完整 template DAG。官方 O2 通常为每个内联 function-expression 现场物化对应的 `DUPCLOSURE + captures`，此时遍历与实际 instruction/capture incidence 同阶；人工 chunk 可以让 `R` 个 root 共用一条深度 `N` 的 dependency DAG，使物理输入为 `O(R+N)`、验证退化为 `Θ(R×N)`。同一 root `Origin` 若有多种 owner template，component shape 也会按候选重验。关闭此项需要把 owner-independent shape proof 与 owner capture proof 分开，按 `TemplateClass` 缓存 node/group 关系，并构建压缩或持久的 alias 约束，使成本只随新出现的 `(template node, physical instr/capture edge)` incidence 增长；不能只记“某 node/instr 已见”，否则 diamond dependency 会漏检同一实例中的别名冲突。
7. **`temp-inline` 的单个超长 argument run 已有硬预算，但极端链会保守放弃融合**：同一 block 的多个独立 callee/materialization run 已按原 statement 索引批量处理并一次压缩；单个 run 对 growing sink 做 site/rewrite 的单读 argument/materialization 候选最多处理 1024 个，超限时整包保留原 temp，零读且 discard-safe 的候选因不扫描 sink 而不计，callee 只增加固定一次扫描。人工 chunk 因而不能再无界放大这条路径，但算法仍是有界的 `Θ(min(arguments, 1024) × sink expr nodes)`，不能声称整个 pass 已线性化。关闭剩余 TODO 需要为 sink 建立一次性 substitution DAG/use-site rewrite 计划，在 output incidence 内完成验证和改写，以去掉极端链的保守上限并恢复可读性融合。
8. **table-constructor 的 SETLIST carrier 仍有明确 residual 边界**：已有 local/temp 的 `Assign` producer、跨 producer 的 open `SETLIST`、尾部 handoff、exact-width pack，以及无法证明多值求值顺序的区域都保留原 HIR 节点；不能在 AST 阶段静默拆成普通 table assignment，因为 raw SETLIST 的 `__newindex`、nil hole、open pack 和分配时点均可能不同。当前放行三类窄路径：canonical `NewTable` 后紧邻、同 binding 的 fixed data-only batch；保留 `LocalDecl` seed 原位、在完整 prefix proof 下把 fixed batch 改成 indexed writes；以及 seed 原位保持、prefix/producer/eval-order 全部通过的极窄 LocalDecl open-tail 路径。所有路径都保留 seed 分配点，拒绝 nil/不确定数组形状、控制流、跨 block、producer `Assign`、debug/capture 资源身份和外部 mention；raw temp 不进入 generic open 路径。联合数组形状检查还拒绝“seed 尾部可能为 nil、后续 SETLIST 追加确定值”的跨语句折叠（`lua54_01_close#15`），避免把 `t[1] = nil; t[2] = 1` 改成 `{ nil, 1 }`。源码 `LocalDecl` 的 indexed proof 可覆盖已经证明连续的数组前缀（`start <= seed_array_len + 1`），但不能跳过未知或可能为 nil 的洞。当前仍会 fail-fast 的 HIR carrier 只有 `common_07`（全方言）、`common_10`（仅 Luau）、`regress_30`（Lua 5.1）和 `regress_33`（Lua 5.1）；它们涉及多返回/复杂表、open tail 或复杂调用，后续必须在 HIR 建立完整 producer/eval-order/GC proof 后再处理，不应为通过形状断言恢复旧 defer/handoff。

本轮完整矩阵（`cargo unit-test --suite all --recompile-rounds 1 --jobs 8`）为 `1220/1248` entries、`1629/1629` protos，`timed_out=0`。10 个 decompile failure 正是上述 carrier residual 的 strict fail-fast；没有回编译或运行语义失败：

- `common_07_return_and_multiret`：Lua 5.1/5.2/5.3/5.4/5.5、LuaJIT、Luau（7 个）仍有 residual `table-set-list`。
- `common_10_tables`：Luau 仍有 residual `table-set-list`。
- `regress_30_table_setlist_nested_producer`、`regress_33_table_setlist_binary_producer`：Lua 5.1 仍有 residual `table-set-list`。

另有 18 个首轮 readability assertion failure，均是源码形状差异而非运行失败：

- `regress_11_assert_short_circuit_value_merge`：Lua 5.2/5.3/5.4/5.5、Luau O0/O1/O2（7 个）仍保留 `local r = assert(...)`。
- `regress_08_global_table_install_readability`、`regress_09_mechanical_call_and_for_inline`、`regress_12_loop_break_shared_continuation`：各有 1 个 Lua 5.1 形状断言未满足。
- `regress_235_table_constructor_eval_ownership`：LuaJIT 仍保留分步 `cross_seed` 初始化。
- `regress_305_temp_inline_independent_runs`：Luau O0 仍保留 `local r = assert(...)`。
- `regress_313_branch_value_terminal_sink`：Lua 5.1/5.2/5.3/5.4/5.5、LuaJIT（6 个）仍保留 `local r = assert(...)`。

这些失败均已归档到下方 residual/可读性队列；不应通过放宽 producer、handoff、global lookup 或 root-lifetime 身份门来“修复”。

本轮关闭一个窄的 AST 展示子题：对“已恢复的单值调用结果紧接着被同一 binding 的直接写入覆盖”的形状，cleanup pass 将调用保留在原求值位置，并把 surviving value 作为后置 local 声明。该规则拒绝 debug/带属性 binding、多目标或间接 lvalue，以及调用或 replacement 再引用该 binding 的情况；它只关闭 `regress_252` 的机械外壳，不代表该案例涉及的 branch/value proof 已完成。`regress_252` 的 7 个方言、round-1 重编译和 Rust 负例测试均通过。

本轮另关闭一个 Generate 层的窄展示子题：当 AST 已明确函数目标是 plain local/synthetic-local
字段路径，且函数体不捕获该路径根 binding 时，输出使用 `a.b = function(...)` 的字段赋值拼写；
global、method、param/upvalue 根以及会捕获根 binding 的函数保留声明语法，避免 implicit-self、
词法 owner 或 debug 身份变化。`regress_37`、`regress_65`、`regress_165` 定向用例和全量
原型回归均通过；这只是 Generate 的等价表面选择，不替代 HIR 的 owner/eval-order 证明。

本轮关闭 266 的无效 `Entry(nil)` arm：promotion 传递 canonical region-result phi provenance，
`locals` 只对无身份敏感、同槽且结构化可证明的 nil 写做路径状态裁剪；allocation-root 轨道
同时保留 direct table escape 后的物理 GC root，直到同一 alias 链的 nil 覆盖。回归包含
“先写非 nil 再清空”的负例，以及弱表 + 两次 `collectgarbage` 的运行时 oracle，并通过首轮与
round-1 重编译。

本轮补齐 call-result 的物理槽边界：显式 GC 栅栏会保留仍占据 trusted home 的未读结果，
canonical MOVE 只有在同一 basic block 内紧随 producer 时才可作为跨槽覆盖证据；中间隔着
语句的 MOVE 不再被提前到 CALL 位置。`lua54_01_close#18` 覆盖未读结果到栅栏的存活，
`#19` 覆盖不同槽独立调用，`#20` 覆盖延后 MOVE 的时点负例；Lua 5.4/5.5 首轮与
round-1 重编译均通过。

本轮关闭 267 的 for 可见 binding 写回缺口：HIR 降低阶段把 numeric/generic-for body 中
可见的 loop binding 直接映射为同一 local lvalue，保留臂内对 `i`、`key`、`value` 的显式
覆盖，不再让 dead-temp 清理误删真实写入。Lua 5.1–5.4、LuaJIT、Luau 的生成产物均保留
这些写回，首轮与 round-1 回编译及运行 oracle 通过；该样例不是 generic-for 准备间隔主题。

本轮关闭 175 的 close 声明前死 local：AST build 现在把 `Assign(temp..., close_temp) +
ToBeClosed(close_temp)` 识别为一条完整的多 binding `<close>` 声明，整组 temp 都不再被
根块预先 hoist。生成结果恢复为单条 `local plain, resource <close> = ...`，不改变值包求值、
词法作用域或关闭时点；Lua 5.4/5.5 的首轮与 round-1 回归通过。

本轮关闭 198、199、206、209 的临时链队列：198 的短独立 IIFE 按正向合同保留，避免把
大量调用重新物化成长生命周期 local；199 的 `local-scope-limit` 携带外层活跃 local 预算，
用有限 `do` 块分段释放嵌套 block；206 的 stripped Luau 只在无 debug 身份时按 trusted
home slot 复用稳定 local；209 的 HIR method bridge 保留固定参数前缀并把 open tail 留给
末位调用。对应方言产物均无诊断源码，首轮与 round-1 回编译及运行 oracle 通过；这些不再
属于“Luau 大量临时链”未解决项。

本轮关闭 222 的稳定 binding 吸收律：branch-control 在合成 repeat 尾条件后，针对条件上下文
再次应用一条严格的 truthiness 规则，把 `x or ((x or y) and z)` 收成 `x or (y and z)`；
重复 guard 必须是 `expr_is_repeatable` 的同一 binding，普通值表达式不会走这条规则，`y/z`
的原求值顺序也不改变。222 的 Lua 5.1–5.5、LuaJIT 六个入口及 round-1 回编译、运行 oracle
均通过，生成结果保留 `repeat` 且无 goto、unresolved 或诊断；逻辑简化模块另有值上下文负例
单测，防止把仅在条件中成立的吸收律外溢。

本轮关闭 312 的跨块 direct snapshot：carried-locals verifier 以 `Unproduced/Pending/Synced`
状态逐路径验证 result 是否已被当前 state 精确承接，禁止沿后续覆写或 ancestry 继续合并；
因此 `result = carried` 仍在递增前保留为独立快照，`stop=true` 与正常退出分别返回 `nil` 和
`1`。Lua 5.1–5.5、LuaJIT 六个入口及 round-1 回编译、运行 oracle 全部通过，生成代码无
诊断或错误控制边；该规则不再属于未收敛的 handoff 队列。

本轮关闭 `regress_35` 的多入口 while 状态审计：StructurePlan 明确记录了 branch-entry 的
共同初值、loop header 的 self/backedge phi，以及 break 后的 result phi。带 debug 元数据时，
`count2/index3` 是进入 loop 的 edge snapshot，不是可按词法名字直接删除的临时变量；把它们
强行并回 `count/index` 会丢失多入口快照与 source-debug binding 身份。strip 输入则满足无捕获、
无 debug、共同 `(reg, epoch)` 的 coalescing 合同，现有 lowering 已生成直接更新 `count/index`
的形状。Lua 5.1 入口的首轮与 round-1 回编译、两条运行 oracle 均通过，故该项保留为按
debug/strip 分层的必要残差，不再把“少一个 loop local”作为待实现优化。

剩余 18 个 readability 断言已按生成形状复核，当前属于必要的保守残留而不是失败语义：
`regress_11`、`regress_305`、`regress_313` 的 `local r = assert` 快照不能在没有全局环境
不可变性证明时改成直接调用，必须保留 `_ENV` 查找时点；`regress_12` 的 `ipairs` 与循环
准备表、`regress_08` 的 global/table lvalue，以及 `regress_09` 的嵌套构造器别名都涉及
接收者求值、元方法或对象生命周期，不能仅按“下一条使用”内联；`regress_235` 的
`parent/child` 构造器合并同样缺少 allocation/identity 证明。后续若要关闭这些断言，
必须先在 AST/HIR 建立对应的全局查找、lvalue 顺序和 root-lifetime 合同，不能为满足
`expect-not-contains` 直接扩大 alias/constructor 白名单。

## 人工可读性审计队列

`cargo unit-test` 证明现有语义 oracle 与机器可读断言通过，不证明生成源码已经逐项达到人工
可读。当前已分段复查 regression 001–318，但尚未为每个 manifest entry 的每个 dialect 产物
形成“已优化”或“现状必要”的关闭证据；因此全量测试绿色不能作为本轮人工审计完成条件。

已定位 owner、可以围绕统一安全合同继续实现的高置信主题：

Generate formatter 的 229 长逻辑链与 161、163、164 大型 constructor 已在 Doc 层分别用
统一悬挂换行和逐项 `Fill` 关闭；对应 case 直接约束最大物理行长与同一行字段装箱，不再列入
HIR 可读性队列。

AST `installer-iife` 现把独立调用语句中包含多条语句或复合控制流的匿名函数物化为最小
`do` 作用域内的 `local function + call`，保持 closure 创建、参数求值和调用顺序，并让新增
binding 在原调用点后立即失活。该规则关闭 02、05、07、17、29、126、275；短独立 IIFE
（166）与表达式内短 IIFE（198）由正向断言保留。81、82、83 复核后确认当前产物本来已经是
普通 `local function`，也补了负向断言并移出历史队列。

具有返回值的 closure callee 现由 HIR `temp-inline` 按 child-first body 事实决定是否保留
producer binding：去掉机械空 return 后包含多条语句或复合控制流的 child 不再内联进
assign/local-decl/return call。AST `function-sugar` 的 terminal-constructor 规则复用同一阈值，
不会在稍后又把复杂 callee 连同 constructor 参数吞回表达式。该合同关闭 10、11、38、42、
52、59、250、251、255、293、301、310，并由 `end)(` 负向断言锁定；134、258 的单条简单
body 由正向断言保留短 IIFE。314 在 PUC Lua 5.2–5.5 只包一条为 deferred lvalue base/key
顺序服务的写入，也不扩大为命名函数；33 的剩余 strict failure 属于上面的 SETLIST carrier，
不再重复列入函数展示队列。

AST `branch-pretty` 现会在控制流和相邻语句都收敛后，把恒真 single-pass fence 收回普通
`if/else`：只允许一个 arm 接管线性后缀，后缀不复制；两个 arm 都可能 fallthrough、直接
local 作用域会被延长、`do` 内仍有 fence break，或出现 continue/goto/label 时均保留 repeat。
嵌套真实循环的 break 也不参与候选。该规则关闭 03、20、34、70，并由四个 AST 单测与
Lua 5.1 round-1 回编译锁定；HIR 仍保留 synthetic repeat 来保证无标签 break 的 owner。

78 与 178 的空条件壳复核后确认是必要的 effect carrier，不是可继续删除的机械控制：
78 的两个 break 动作虽然相同，中间的 `xs[x]` 仍可能触发 `__index` 或错误；178 则明确用
global/table lookup 和比较元方法计数验证每次条件求值。Lua 只有调用能独立成为表达式语句，
其它动态 predicate 若删除空 if 就会丢求值，改成临时 local 又会引入新的 root 生命周期。
现有 HIR `branch-control` 因而只删除 discard-safe 条件，并把 effect-only call 收成调用语句；
78 新增表读取正向断言，178 继续由 global shell 断言和运行 oracle 锁定。

157 与 294 的 Luau repeat 条件 scratch 已按 frozen condition owner 收敛：Structure 在存在
直接 continue 时把 latch header 的纯常量 prefix 放到 HIR body 首部，`temp-inline` 只消费
这个 plan 标记、canonical、trusted-home 且唯一由当前 repeat condition 使用的标量 temp。
普通 body producer、lookup/call、capture/debug、coalesced state 与任意层 goto/label 都不能
进入这条规则；定向首轮与 round-1 回编译覆盖 7 个 157 方言和 3 个 294 Luau 优化级别。

仍需先补齐语义证明、不得直接按输出形状改写的候选包括 40、86、94、100、101、109、
112、116、117、123、152、156、208、226、252、265、270、291、296、311。它们涉及
循环入口 phi、并行 snapshot、closure identity、continue latch、构造器求值或资源作用域，应与
上面的高置信主题分开处理。

关闭本节必须逐项核对源码与当前生成产物；可安全优化的主题完成实现、负例和运行 oracle，
不能证明安全的主题保留原因与最小反例。仅有“未再发现失败”或全量测试通过不构成关闭证据。
