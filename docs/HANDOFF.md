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
设计合同和回归在 c2c76744 完成依赖闭合提交。本阶段继续补齐 Boolean 预写与模板 record 事务，
失败回归仍保留，不能把提交当作全绿。

## 最新完整验证

`cargo unit-test --jobs 8`：**2904 项，2901 通过，3 失败，0 超时；2030 个 proto 全部通过**。
日志：`tmp/test/audit.record-prewrite-checked.full.txt`。三项均为 recompile-convergence-mismatch：

- 592：Luau O0 stripped、O2 retain-debug。
- 596：Luau retain-debug。

各失败均完成对应轮次运行比较后才到源码收敛断言；没有本次已检出的运行不等价或其它断言失败。
594 六配置、598 六配置、599 七方言、600 四配置、601 十二配置、602/603 各六配置全部通过。
596 的 PUC 五方言与 LuaJIT 通过。不要将旧日志中 594、598 的失败当作当前问题。

同一最终源码的全工作区 Clippy（all-targets/all-features、-D warnings）、WASM check 和 debug CLI 构建均通过。
日志分别为 `tmp/test/audit.record-prewrite-checked.clippy.txt`、`.wasm.txt`、`.cli-build.txt`。
CLI 已更新；diff-check 通过，src 未检出内嵌 Rust 测试或临时诊断打印。
`audit.record-prewrite-final.full.txt` 是修复 237 Batch 所有权回退前的中间结果（6 项 residual SETLIST）；
该回退已修复，237 七方言定向通过。`audit.native-frames-final.full.txt` 是更早取消的测试。
此前 `audit.native-frames-checked.full.txt`（2898/2892/6）、`audit.materialized-copy-final.full.txt`（2892/2881/11）和
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

## 仍需推进的问题

1. **592 O0 stripped / O2 debug**：从当前相邻轮首次差异重新审理。
   旧定位为 fresh-vararg-root 的 print 前缀，随后 callee/COPY/nil 增长。
   新完整帧入口已变化，旧推测不能直接当根因；尚未证明所有剩余变化有限。
2. **596 Luau debug**：proto15 的 Boolean 预写已消费；下一处首轮差异在 proto18 sequential_cell。
   原 callee r2 在 CLOSE r2 后复用，可能因新 epoch 被 source prefix 的 epoch0 假定拒绝，
   该具体拒绝仍待一次动态 Plan.base/prefix 诊断确认，不能按猜测归零 epoch。
   `tmp/audit-596-next/prewrite18.passes.txt` 已证其 false 保留到 Final，故不是前层预写漏发布。
   proto24 numeric_frame_scopes 另有已证 Luau header 直接排除：物理顺序 limit r3 / step r4 /
   index r5，求值仍 start→limit→step；start CALL 留 r5，后两 CALL 在 r6 再 COPY 到 r3/r4。
   不能仅排列三个 home 后放行，需要在原 header owner 联合证明 scratch CALL 与结果 COPY。
   证据 `tmp/audit-596-next/prewrite24.layers.txt` 和 pinned Compiler.cpp::compileStatFor。
   不重做已闭合的 cell 身份、原 PUC/JIT header 和 04 外层构造器。
3. 系统性语义、可读性与性能审计继续；上述三项之外没有当前证据不等于全仓不存在缺口。

当前 case ID 只作导航，每次 manifest 改动后核对：
592 2715–2720；594 2722–2727；595 2728–2733；596 2734–2740；
597 2741–2742；598 2743–2748；599 2749–2755；600 2756–2759；
601 2760–2771；602 2772–2777；603 2778–2783。
六 Luau 配置顺序通常为 O0/O1/O2 stripped、O0/O1/O2 debug。

## 有限预算与性能证据

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
