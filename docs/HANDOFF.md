# unluac-rs 阶段接续（2026-09-11）

本文记录当前接续状态；分层合同在 docs/design。先检查工作区和最新产物，不把本文或历史计数当作当前事实。
长期 goal 保持 active，只记录持续目标和约束，不写阶段状态；本阶段通过不代表长期审计完成。

## 入口与边界

工作区 E:/workspace/unluac-rs，分支 dev。先读根 AGENTS.md、unluac-debug、rust-skills，
按实际修改范围读 docs/design.md、目标层和 docs/design/11.test.md。先看 git status、diff 和本文的最新日志。
保留全部未提交修改，不 reset、不机械清理。最多一名子代理，明确文件边界并协调 Cargo 窗口。
src 不放 Rust 内嵌测试；新测试用已注册 Lua case。避免新增 O(n²) 及以上实现。
每个问题先找首次事实丢失或证明拒绝，在原 owner 修复；不能凭假设放宽 guard。
不删除失败回归、不降低断言、不用不断增加轮数掩盖增长。完整主题集中验证并提交。

不要重做已闭合的 shared_cell、兄弟分支 cell、04 外层表构造器或 601 CALL/COPY 释放归属。
实际 HEAD 以 git log 为准。已提交 d004ce6e 是独立的 CALL/COPY owner 修复，仅四文件，
不是整批优化完成。e0207891 独立提交显式收敛 case 的生成元信息设置；其余跨层实现、
设计合同和回归在 c2c76744 完成依赖闭合提交。572d4cb2 补齐 Boolean 预写与模板 record 事务；
4a3b1303 补 CLOSE 输出绑定和完整 FASTCALL 准备；bfe50230 修复 numeric-for 正常后态与
完整 header，并补原高槽全局比较。90e1288f 修复 skip 出口原 index 的单槽覆盖；
c5c8e11f 将它替换为完整原 LOADNIL 组，并恢复后继低槽调用前的词法末端。
35e98b12 补齐 debug Phi 窗口，0d3e0ce8 按已证固定点设置592 O0预算，
91f2a7ee 补齐比较条件的原调用入口。本阶段恢复for前原声明帧，并修复参数快照root交界。
所有回归仍保留，验证范围以以下实际日志为准。

## 最新完整验证

`cargo unit-test --jobs 8`：**3013 项全部通过，0 失败，0 超时；2030 个 proto 全部通过**。
日志：`tmp/test/audit.binding-state-final.full.txt`。包含615–617的20项新配置。
592六配置全部通过：O0 stripped预算为已证足够的4，其余五配置仍为3；本阶段未再调预算。
610的比较条件入口修复也已进入本次全量，不再依赖旧定向结果作为当前结论。
已注册全量没有运行不等价、源码收敛或其它断言失败，但不外推为整个长期审计完成。
合并 nil/分支/limit 与后继调用帧的已证错误现已加入 609–611 并通过，不外推未覆盖形状。
594 六配置、598 六配置、599 七方言、600 四配置、601 十二配置、602/603/605 各六配置、
604 七方言 stripped/debug 共十四配置全部通过。604 原三轮预算未提高。
596 全部七配置通过，原三轮预算未提高。606 十八配置、607 十六配置通过；
606 包含非法 step 不进入 body 的显式检查。608/609/610 各四配置、611 六配置、612 三配置、
613两配置、614十二配置全部通过。
不要将旧日志中 594、596、598 的失败当作当前问题。

同一最终源码的全工作区 Clippy（all-targets/all-features、-D warnings）、WASM check 和 debug CLI 构建均通过。
日志分别为 `tmp/test/audit.binding-state-final.clippy.txt`、`.wasm.txt`、`.cli-build.txt`。
CLI 已更新；diff-check 通过，src 未检出内嵌 Rust 测试或临时诊断打印。
`audit.numeric-frame.full.txt`（2981全过）尚未包含后加的参数holder竞争与纯nil终点反例；
`audit.numeric-frame-owners.txt`是修复交界后的32项定向。不能用首次全绿替代这些后来发现的问题。
`audit.phi-window-final.full.txt`（2979/2978/1）记录旧592 O0预算失败，现已按固定点闭合。
`tmp/test/audit.numeric-global-final.full.txt`（2958/2956/2）是 skip 修复前的最近基线。
`audit.numeric-skip-final.full.txt`（2962/2960/2）是单槽修复基线；
`audit.nil-groups-scopes.full.txt`（2970/2966/4）含现已闭合的66/317可读性失败；
`audit.nil-groups-final.full.txt`（2976/2974/2）尚不含610新增If/While场景，最终日志以上文为准。
`audit.record-prewrite-final.full.txt` 是修复 237 Batch 所有权回退前的中间结果（6 项 residual SETLIST）；
该回退已修复，237 七方言定向通过。`audit.native-frames-final.full.txt` 是更早取消的测试。
`audit.numeric-header-final.full.txt` 是全局比较修复前的中间结果；还包含新增样例错误给
Lua55 const index 赋值的两项 baseline failure。可写场景已完整移至607的现有受支持方言矩阵。
此前 `audit.closed-output-final.full.txt`（2924/2921/3）、`audit.record-prewrite-checked.full.txt`（2904/2901/3）、
`audit.native-frames-checked.full.txt`（2898/2892/6）、`audit.materialized-copy-final.full.txt`（2892/2881/11）和
`audit.handoff-final.full.txt`（2863/2851/12）仅是历史比较基线。

## 已闭合事实与本阶段实现

### 闭包与 cell 身份

- HIR→AST 保留 Fresh/MayReuse；独立 HirCaptureInitializer 区分 FirstVararg 与
  NegatedNumericString，普通数值事实不授权删除捕获初始化。
- 非 vararg Fresh 已证明范围：零参数、有限 f64 数值 r0、首 Fresh closure r1、单个 VAL r0，
  随后直接 RETURN r1。生成 `local value=(-"-7")`，再生仍从原 LOADK/MINUS 的 SSA 验证。
  保留 ±0、负小数、最小次正规和最大有限数；598 用 buffer f64 逐字节与闭包身份验证六配置。
- 不能推广到任意后缀：新增数字字符串常量曾把后缀 ADDK K255 推为 LOADK r5 K256 / ADD，
  改变 scratch。证据 `tmp/audit-fresh-agent/pool-251-*.lua.asm`。字符串比较、乘法、显式 if
  也不能替代当前已证布局。原零参数 vararg 屏障继续用 `((...) and (n) or (n))`。
- capture 窗口按真实 CLOSE/RETURN 区分兄弟分支 cell；RETURN 窗口必须有真实初始化 Def，
  Entry cell 不伪造初始化。已知初始化支配所有 capture/映射写/phi 时在原 owner 声明，
  不为 shared_cell 再造空 local。合成 edge COPY 读取原 MOVE 已绑定的 Local。
- CALL 写回 COPY 实际复用源码 local 时始终登记 materialized owner；是否被选为 GC 观察代表
  不控制真实 home 的释放归属。601 的无 alias 最小例已注册，500 六项运行回归已闭合。
  不恢复中途 Move|GetTable 限制：assignment_copies 应验证原 Def 协议，而不是限定初值 opcode。

### 原求值帧与完整初始化事务

- Promotion 保存 CALL 的 canonical Def/phi 值版本、FASTCALL COPY 两端 home、callee 原身份，
  NumericFor 的三个原 header 值与槽，以及 GenericFor raw dispatch results。值身份不等于根退休。
- SourceFrames 在 lexical block 退出恢复 unproven_prefix，不把一个已结束子块的未知前缀传播到外层。
  同槽 CALL 结果可成为下一 callee，但必须逐次核对结果宽度、home 与完整事件。
- 比较树保留任意 AND/OR 分组；每个短路右臂都不能吸收原无条件 producer。一次树遍历，
  不逐级重扫子树。条件 subject、Boolean 写回、常量 scratch 与 fallback lookup 分别核对。
- Luau FASTCALL2K 的内嵌常量与普通 direct 参数分开：先按参数序准备非内嵌 direct，
  再按参数序执行 fallback COPY/内嵌常量加载，最后取 callee。允许原位数字/静态键读取和
  已由 builder 证明的单结果 CALL；不删除元方法或独立 root endpoint。
  开放参数仍保留 tail CALL 全部返回值。597/600 覆盖环境变化、fallback 和 captured-value 快照。
- 低槽 canonical NEWTABLE 若被直接 callee lookup 使用，Promotion 保留其前缀身份，避免
  temp-inline 先移入高槽 callee。599 保留真正已闭合 cell 的调用前缀；不把 epoch 归零。
- 固定 SETLIST 的索引降低移至 Final：Normal/Deferred 联合稳定后才运行，变化仍回到原固定点，
  使用同一个总预算。原 table owner 的全部 guard 保留，不从已展开索引写反猜 batch。
- 完整 Luau 内层数组消费原 allocation/唯一 Batch 的输出和 buffer；debug initializer 查询
  复用实际 scope/direct seed/原 home，不签发 root 删除。O0 单层数字 Neg 仅覆盖末字段，
  同时核对字段结果槽与整批 buffer 末端的原 unary 输入槽。非末字段的编译器 scratch 公式不同，
  当前没有借此放宽；输入 home 由 Promotion 已有操作扫描保留。
- GenericFor 预派发的普通 nil Assign 携带 dispatch/raw result Def/released Temp 身份，
  不是可自动删除的 LocalRootRelease。完整 header 同时消费唯一 CALL initializer、
  准备区和相邻精确释放；preview 若删 producer 却残留对应 nil，整批拒绝。
  这使 outer cases 与 ipairs header 联合恢复，而不延长内层表 root。
- 602 首次空声明来自 debug 分支 SSA 合流：原 scope 在 comparison 完成后开始，
  locals 先造 empty declaration，boolean-shells 原来因 debug 名字一概拒绝吸收。
  analyze 现在发布具体 phi/predicate/continuation 证书，boolean-shells 再核对 scope、
  promoted local 与 home，恢复同一 initializer；342 中条件前可见的 local 仍拒绝后移。
  六配置与 expect-not-contains " = nil" 在全量全部通过，未降低断言。

### 其它已保留实现

- Luau 模板显式值与隐式预置零角色分开；construction owner 消费角色，不能删除模板分配约束。
- 互斥来源用持久 DAG，Promotion query 在同一快照内缓存；分支合并仍核对全部来源。
  branch-control 克隆候选前使用有界双边节点计数，避免深臂逐层复制。
- NumericFor 三个 header 的原值/home 经 HIR 完整帧消费；PUC 和 LuaJIT 使用各自原 CALL layout，
  FR2 不套用 PUC 公式。Luau header 顺序尚不能套该证明。
- 显式收敛 case 从首次生成起关闭 Generate 元信息注释，避免路径/行号导致假差异；
  普通注释/debug case 保留默认输出，不在比较器删除任意源码文本。

### Boolean 预写与模板 record 完整事务

- 596 proto15 的尾部 assert 原有 false header 预写被 Deferred dead-unresolved-temps
  按 entry-nil/GC-inert 合法清除，但 native 仍需要这个实际事件作为帧证明输入。
  当前 Deferred 从当前 CALL 的原预写列表借用迭代、同一次树遍历收集临时保护集合；
  Final 才按原 guard 清理未消费者。不用永久 retention，不跳过缺失 Temp 的 native guard。
  原 shared_cell 的 assert 已直接恢复；其余失败不代表该子问题未闭合。
- 594 O0 首个持续增长点是重复 record 初始化之后的 assert。普通调用帧候选已成立，
  但原键 scratch 的多个 local 声明令 prefix 拒绝。新事务联合消费 LuauTemplate 的
  隐式字段、原 key/value 槽、每个单结果 CALL 与最后 record，整个 preview 保留 seed 声明。
  字段重建仍复用 ConstructorBuilder 的角色恢复，不单独去重真实重复字段。
- LuauTemplate 不适用通用 indexed/batched capacity query；由模板 owner 核对原键许可、
  完整隐式角色和 32 字段上界。O0 的动态 key 与优化配置内嵌 key 按原 layout 分开证明。
  原同 owner 后续 Batch 优先拥有完整混合构造区，不能提前结束 record 区间（237）。
  每个直线区仅选择最后 record 候选，不逐字段重建增长前缀。
- record value 当前只消费经 builder.call 验证的 CALL。字面量或已有低槽值不能冒充
  原结果 scratch；且 Luau constant-pack 会把 `{a=f(), a=5}` 中 f() 删除。
  603 用原分离写验证副作用不可丢失，并验证三次动态重复字段的顺序。
  反例原/候选实测输出为 event+5 / 5，证据 `tmp/audit-596-next/record-{original,candidate}.lua`。
- 594 O0/O1/O2 stripped 均在原三轮预算通过；本阶段没有调整收敛预算。

### CLOSE 输出绑定、非零 epoch 与全 direct FASTCALL

- 604 暴露原 nil holder 与块内闭包写回未连接：AST build 的统一 Temp hoist 是首次移动
  声明的位置，HIR Bindings 是缺失身份的 owner；没有在 AST 按同寄存器猜变量。
- Bindings 的 debug nil 排除由整个 Reg 改为完整 capture home/source scope；采集仍包含
  全部 ByValue/ByReference，不从 cell local 是否分配反推未捕获。旧 r2 cell 已关闭后，
  新 epoch 的未捕获 next_first 可使用自己的原 nil。
- stripped 输出只消费最终保留的单块 CLOSE 窗口、canonical nil/output、无旧读取/Phi/alias、
  未捕获的精确 home。输出限定原位 Closure 或唯一紧邻 Closure→MOVE，不绑定高槽 producer。
  原 holder 是该槽最后 fixed Def，后续开放写/提前 Close/排除该槽的根观察均拒绝；
  用 Dataflow 根区间查询，候选窗口不重叠，无逐候选全后缀扫描。
- Lua51 首个窗口没有 LOADNIL；原 Def 的 EntryNil 覆盖证明授权入口声明，旧 Entry 读取
  仍为 nil。Lua54/55 的 CloseKind::Return 指向下一条 Return，不是 Close 自身；只有
  最终相邻普通词法退出协议能结束根窗口。604 原 case 保留三轮预算及全部十四配置。
- 原 home/epoch 与源码位置分开：SourceFrame 按唯一 trusted home 的 slot 核对活动声明，
  CALL 附加写仍使用原 producer 的完整 home。604 同时覆盖同槽复用与旧闭包状态未被新 cell 覆盖。
- 全 direct FASTCALL 与 mixed/COPY 参数共用 fixed 参数准备事务；原表字段/事件与 allocation
  参数槽均须已证。592 的 setmetatable 参数已恢复，605 六 Luau 配置验证全 direct/mixed
  表身份及字段/嵌套 CALL 次序。605 沿用普通一次再编译语义验证，不宣称它证明多轮收敛。

### NumericFor 正常后态与 Boolean 全局读取

- 596 proto24 原 step COPY 的 t12 并非 Phi。入口 nil 首产于 lower 的 copy_root_temps
  前插，循环后 nil 来自 copy_root_before_releases；locals 只是消费已存在的写。
- 更早缺失在 NumericForInit effects：Luau 准备后 limit/step 已数值化，却未成为新 Def，
  旧 COPY 根被误追到循环后的两个 LOADBOOL。Transformer 现在发布 normalizes_controls，
  Dataflow 在真实准备点定义两槽；Promotion 的 GC 分类消费同一事实。错误 nil 自然消失，
  未加 numeric COPY 排除集合，也未按后层 nil 文本删除。最新证据
  `tmp/audit-596-header-next/normal-state.passes.txt`。
- VM 核对：51/52/53/JIT/Luau 在所有正常后继（含零次迭代）完成 limit/step 数值化；
  54/55 可提前 skip，未发布该保证。协议检查新隐式 Def 仅由同 latch 对应控制读取，
  真死 Phi 可忽略；普通读取/capture 或活的未归属合流明确失败，不留未初始化 Temp。
- Luau 完整 header 以原 controls 和用户 binding 确定 top：普通 index 的 start CALL
  在 top-1 原位返回；其它值（可写 index 时三个值）在 top CALL 并唯一紧邻 MOVE 回对应
  control_values。三组按源码顺序共同消费，使用原 Def/home 和完整写集合，不借 retained-copy
  证书。`tmp/audit-596-header-next/header-plan.passes.txt` 保存 proto24 整体恢复结果。
- 596 根部真正的后续首拒绝是 sentinel assert：Global value 原读取 r15、Boolean r14、
  callee r13。缺 GlobalRef subject 支持让声明占源码 slot13/14，污染随后全部 prefix。
  现只允许仍有 Local 定义、原比较 lhs=Boolean slot+1/rhs内嵌常量、标识符全局键的
  Eq 读取，仍过 home 和事件验证。旧拒绝证据 `tmp/audit-596-root-next/`。

### 原 LOADNIL 完整写组与源码帧末端

- `tmp/audit-for-skip/index-gc.lua` 不依赖 debug.getlocal：动态 1 MiB 数值字符串作为 start，
  零次循环后由 `_ENV.__index` 触发 GC，比较相对基线 >512 KiB。54/55 原源码、strip 原
  chunk、debug 再生均为 `true,false`，旧 strip 再生为 `true,true`；仅在原位置补回 nil
  后恢复 `true,false`。首次删除在 AST statement-merge 将入口 Temp 合并为原位声明后，
  cleanup 按无 read 的普通 nil 删除；HIR 原本仍保留 t9=nil。
- 该入口旧值由 init/latch 合流而未知，不能把全部根因归给 DefinedScalar。现已删除
  NumericFor 专用 init→单槽 endpoint 映射和 HIR init_instr，改由 Promotion 保存原
  LOADNIL 的完整 canonical 定义组。source_frames/nil_writes 在最终 HIR 原语句位置
  消费全组、单写无 read/capture、连续可信 home 和完整写域；语法与事实整批预览提交。
  不猜旧根、不加入口 holder、不拆组补槽。609 合并 nil、分支、limit 等原失败现已闭合。
- 只恢复声明起点会引入另一种真实不等价：`scope-observed-value.lua` 原第二次低槽
  make 调用已不保活 do 内全局查询返回的弱对象，旧再生父块 Local 却延长了根。
  同一预览现将线性 nil/未读 GlobalRef 段在后继原帧复用首槽时包回 do；部分退休或
  活出变量仍拒绝。初始 lowering 通过 temp_decl_locals 发布真实 Temp→Local 身份，
  让 debug 原声明也能消费完整写组和末端；只保存 home 不足以辨认该生产者。
- 610 用弱表断言覆盖后继 for、赋值 CALL、If 与 While。Lua54 的 while/break 会先
  合成 `Call and predicate`，入口查询只沿短路左项与 not 消费原 CALL；不能用右项补证。
  SourceFrames 完整扫描后缀，While 只按词法进出 body，Break/Continue 不改变声明槽序。
- 中间全量暴露 66、317 原可读性断言失败。66 的原 nil 与紧邻 empty declaration 同
  完整 home，现复用 carried_locals 相邻事务，保留既有 carrier，避免重复 Local 导致槽名
  漂移；不逐候选重扫后缀。317 保留原清槽分支，branch-pretty 将匿名受保护 nil 臂完整
  放到 else，并使 not 规范化服从同一方向；611 用原弱对象释放验证该交换，不删除清槽。
- `normalizes_controls` 明确包含 index/limit/step；54/55 的 index 逻辑 Def 不再被 GC
  分类或 scratch 消费者无条件当作原位数值覆盖。binding 的独立全路径分类尚未闭合，
  不能把 index 反例外推为所有控制槽已完成审计。
- 608 覆盖无清槽/清槽、有效低槽前缀、嵌套 scope、非零循环和连续 endpoint；54/55 各
  strip/debug 四配置通过。部分其它高槽残值的原输出存在方言差异，由同方言 baseline
  比较，不把它们改成统一 GC 断言。45 项定向日志 `tmp/test/audit.numeric-skip-targeted.txt`。

### 本阶段已闭合的 debug Phi 窗口

592 O2 debug 第1→2轮的 end=@139 cohort 原仅收 Def r9..r16，遗漏已接受的
scope16/17/18（r17/r18/r19 的 phi10/11/12），导致 caller_end20 与 ceiling+1=17 不符。
现由 lexical_windows 原 owner 同时消费 Def/Phi 和同槽输入闭包，仍验证完整窗口、
发射域、capture/escape及 caller_end 精确相等。Phi 合流本身不当作写；原 @114 callee
r18 的退休由后续 Phi 所有直接同槽 Def 实际覆盖、合流块必经共同证明。嵌套Phi/Entry
不签发该覆盖下界。同 scope 的 holder 后续写须逐原PC证明身份，不能接入新binding。
`tmp/audit-fresh/current-592-o2debug/phi-window-2.lua` 已恢复三个 do 和末尾直接 print。
612 的最小 factory/布尔Phi/后继调用在三个Luau debug优化配置通过，预算3。
`tmp/audit-phi-window/` 保存前后对比及外层holder、分支初值真假挑战；这些挑战都运行一致，
不是持续增长证据。O2 debug 原持续增长已经闭合，不要重做 Fresh 或 setmetatable。

### 本阶段已闭合的原帧复用与参数快照

`tmp/audit-for-binding/table_integer_skip.lua`
   和`table_float_once.lua`在54 strip/debug中原源码/原chunk weak=false、再生weak=true。
   主侧已重跑integer-skip对照确认。原do内`local a,b,c,object=false,false,false,{}`将表放r3，
   54整数FORPREP即使skip也写binding r3，或float成功迭代写r3；再生删padding和do，
   表成父块r0、for从r1开始，旧对象不再被相应写覆盖。原/再生/ASM保存在同目录。
   原首拒绝：debug四个accepted Def scope(r0..r3)共同end=@6，最后
   观察@5为SETTABLE；lexical_windows::debug_binding_window开头只接纳Call，因而不恢复do，
   debug再生for从r4开始。stripped初始HIR也无do，locals将原t3(r3)table提升父块l1，
   dead-unresolved-temps再删除三个false padding，for从r1开始。pass证据
   `table_integer_skip-5.4-strip.passes.txt`。这是FORPREP覆盖的词法/根末端未被承接，
   不能归因于binding非GC分类本身后直接放宽guard；本整数路径原binding确实为数值。

现由bindings/reused_frames消费原for协议和共享lexical_scope_evaluation_start，恢复入口
直线声明组与header首求值之前的do。false/nil占位、旧表、额外alias及同槽清零一起绑定，
低槽prefix留在外面；匿名GETUPVAL/SETTABLE base不冒充后续alias声明。613覆盖integer skip、
float once、prefix、alias保留/清除、全局header、CALL header及全局实参，原观察分别为
false / false / false / true / false / true,false / false,false / true,false,false。
不在header前加nil。跨块旧窗口、未知低槽前缀、open/CALL/capture等仍按明确边界拒绝。

追加审查发现parameter_holder_competition：先发新帧绑定、后发copy-root holder会把读取
重定向到未初始化Local（原true,false,false变false,false,false）。现copy-root owner先发布
完整身份，新帧候选按现有bound_temp_targets冲突整体拒绝。该反例保留在613，含再编译检查。
下一轮又暴露普通scalar root owner没有消费参数COPY的纯nil终点：第一次temp-inline删
独立holder，lookup通过debug.setlocal清参数时丢根。现只消费已有copy_root_overwrites
精确证书，不扩大回边/观察型覆盖owner或无条件保留参数别名。614是不含循环的最小例，
六原生方言strip/debug十二配置通过；613/601/604/610的32项定向亦通过。
证据 `tmp/audit-for-binding/parameter-holder-round1.passes.txt` 和 `parameter_snapshot_pure_end.lua`。

### 数值循环正常后继事实

Transformer独立发布`normalizes_binding`，与`normalizes_controls`通过`normalizes_slot`
供Promotion和scratch共同消费。PUC51–55均不能保证Init所有正常后继都写数值binding；
LuaJIT FORI整数/浮点都先写FOR_EXT，Luau由数值化index覆盖，保留两者已证事实。
effects中服务body值归属的逻辑binding Def不变，不把它当物理skip覆盖。
Loop的非GC分类仅接受internal index：PUC51–54 body可把binding写成表；LuaJIT双数值
IFORL溢出在写FOR_EXT之前跳出。当前Windows JIT构建为单数值，后者是pinned VM源码证明，
没有用当前运行探针声称覆盖双数值配置。VM导航位于lua/sources/各版本lvm/vm_x64文件。
615覆盖长数字string step的skip/once状态（10配置），616覆盖JIT Init旧binding退休
（2配置），617覆盖PUC51–54 body写入binding后退出仍保留对象（8配置）。这些原/再生
均通过；本批修正错误证明前提，尚无normalizes_binding独立导致再生差异的反例。

## 仍需推进的问题

1. **完整条件求值入口**已证明两个新反例：`1 < tonumber(make())`与
   `for_condition_left == make()`，54/55各strip/debug共8配置原源码/原chunk通过、再生失败。
   证据`tmp/audit-for-skip/right-condition/summary.json`与同目录源码、ASM、HIR，探针CLI
   时间戳06:20:37（尚未含本批normalization事实修正）。首次拒绝在
   `nil_writes::expression_call_frame`：Binary只查左项，常量或GlobalRef返回None。
   第一例完整入口是外层tonumber的r0，不是先执行的内层CALL r1；第二例左GETTABUP r0
   观察旧r1仍存活，随后右callee写r1才应退休它，不能跳过左观察直接猜右CALL帧。
   字符串常量相等已归一化为CALL==const，四配置通过，不要重复修复它。
   下一步核对现有原操作/operand provenance，在原owner证明完整入口与准备顺序。
2. 系统性语义、可读性与性能审计继续；已注册测试之外的真实探针失败同样需要处理。
   592六配置已通过，594/596也已闭合，不能从旧日志重复修复这些入口。

## 有限预算与性能证据

**592 O0 stripped 的有限收敛预算**：当前CLI有界探针为
   2658→3070→3280→3230→3230 字节，五次运行均与原结果相同，第4/5次完整源码相等。
   最新证据 `tmp/audit-phi-window/592-o0-current/summary.json`、`3-4.diff`。
   第4次 native-call-frames 发布的 PhysicalFramePrefix 从l0..l8扩至l0..l21，AST
   function-sugar 与相邻声明合并按 may_move_scope_start 撤回糖、保留独立行；callee COPY
   由temp-inline及完整帧消费。`4.owner.passes.txt`、`3.final.hir.txt`、`4.final.hir.txt`
   保存实际owner快照。按首次相同所需4轮设置该配置，完整六配置定向通过；其它五配置仍为3。

当前 case ID 只作导航，每次 manifest 改动后核对：
592 2715–2720；594 2722–2727；595 2728–2733；596 2734–2740；
597 2741–2742；598 2743–2748；599 2749–2755；600 2756–2759；
601 2760–2771；602 2772–2777；603 2778–2783；604 2784–2797；605 2798–2803；
606 2804–2821；607 2822–2837；608 2838–2841；609 2842–2845；610 2846–2849；611 2850–2855；
612 2856–2858；613 2859–2860；614 2861–2872。
六 Luau 配置顺序通常为 O0/O1/O2 stripped、O0/O1/O2 debug。

598 O0 debug 的预算 4 来自早先单次声明规范化后连续三次固定的实测，未继续增加；
其它五配置仍为 3，并在本阶段全量全部通过。
296 当前 case-1051 的 round 1–4 输入→regen 字节数依次为 1696→1951、1951→2078、
2078→2002、2002→2002；第 4 轮首次逐字符相同，运行验证在本次全量通过。
证据在 target/unluac-tests/regression/recompile-round-4{,-regen}/luau/case-1051/generated-source/。
最后变化为 callee 中转消除、函数声明形状与末尾 print 内联；旧 case-1050 或
296-eight-rounds 是旧失败产物，不用来证明当前固定点。
`tmp/audit-fresh/stages-o2`、`stages-o0` 保存修复前七轮增长，
`direct-call-o2` 保存 direct CALL 修复后首次/下一次相同；当前版本以全量源码比较为准。

历史有界性能探针 `tmp/audit-loops/capture-window-scaling/`：
64/128/256/512 个连续 closed-cell，调试 CLI 约 184/278/526/1049ms，运行输出相同。
CLOSE 扫描改为按槽退休的前向 sweep；这只是有界证据，不是整个长期性能目标完成。

## 实际命令与产物规则

```powershell
cargo unit-test --suite regression --case-filter regress_592 --case-filter regress_594 --case-filter regress_596 --jobs 8
cargo build -p unluac-cli --features unluac/decompile-debug --locked
target/debug/unluac-cli.exe -i <chunk> --dump-pass native-call-frames,locals --proto 0 --detail verbose
cargo unit-test --jobs 8
cargo clippy --workspace --all-targets --all-features --locked -- -D warnings
cargo check -p unluac-wasm --target wasm32-unknown-unknown --locked
```

PowerShell，必要时将 C:/Users/X3ZvaWQ/.cargo/bin 放 PATH 前端；python 可能是 WindowsApps stub。
-s 是源码，-i 是已编译 chunk，-i 不与 --strip 联用。--dump-pass 不与 -o 联用；
多阶段 dump 用重复 --dump，不用逗号；--dump-pass 接受逗号分隔真实 pass 名。
普通 HIR dump 已是简化后结果，首次偏差看 pass 前后。pass 快照只在 CHANGED 时输出。

Luau 编译用 lua/build/luau/luau-compile.exe --binary -O0/-O1/-O2 -g0/-g2；
二进制 stdout 用 .NET Process BaseStream 写文件，避免文本重定向损坏。
最新测试产物在 target/unluac-tests/regression/<round>/luau/case-<ID>/。
recompile-round-N/generated-source 是上一轮输出，-regen 才是本轮新输出；
readability/runtime 提前失败时 regen 可能未写出，须核对时间或从该轮 chunk 重新反编译。
临时 dump 放 tmp，不能依赖持久存在。源码保存 LF，避免 PowerShell WriteAllLines 制造整文件 CRLF 差异。
