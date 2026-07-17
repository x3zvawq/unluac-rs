# 审计问题与交接清单

> 更新时间：2026-07-17
> 基线：当前 `dev`
> 本文只记录尚未解决且已经取证的问题、明确风险和已确认的设计决定；完成项立即删除。

## 不应回退的决定

1. **宽松生成必须保留**：结构恢复不完整时，用户仍应看到尽可能多的逻辑。宽松模式允许保留必要的 `goto` / `label` 和 `unluac error` 占位；严格模式才要求目标方言可重新编译。
2. **诊断写入输出，不写 stderr**：诊断伪源码由首行 `unluac error` 注释和 `GeneratedChunkKind::DiagnosticPseudocode` 标识，不再额外打印“目标方言不支持 goto/label”的 stderr 警告。
3. **错误注释不能删除**：它既保留其余可读逻辑，也让用户能定位并反馈反编译器缺口。
4. **允许高价值大改**：涉及层次职责、核心数据模型和跨 pass owner 时，直接替换错误架构，不保留兼容层、双轨事实或后层 fallback。

## 未解决问题

1. **LuaJIT `ISTYPE/ISNUM` 尚无严格源码表达**：官方 `LJLIB_LUA` 内建函数用这两条指令实现 `CHECK_str/func/tab/int/num`；失败路径调用 `lj_meta_istype`，其中 string/integer/number 还会原地隐式转换。Transformer/HIR 现已保留 `TypeGuard` 的读取、顺序和具体 expected type，宽松模式能继续恢复余下函数，严格模式会拒绝 unresolved guard；但直接生成 `assert(type(...))` / `tonumber(...)` 会依赖可覆盖全局且不满足 LuaJIT 的错误与 `int32` 转换合同，不能冒充等价源码。后续若要关闭此项，需要先确定一个目标方言 helper 合同或正式的内建伪源码输出模式。
2. **branch-stop 通用 continuation 搜索仍有嵌套高次访问上界**：HIR 的 membership-only 消费者已直接查询 `BranchRegionFact`，single-pass repeat/shared loop tail 也已收窄到 CFG predecessor 与已知 nested-loop preheader；但 `loop_body_shared_continuation_stop` 仍为每层 branch 扫描完整支配区间，且每个候选可能重新执行 all-path / avoiding DFS。proto 共 `N` 个 block、单个 region 含 `R` 个候选时，单次最坏约 `O(R·N log N)`，`R≈N` 时即 `O(N² log N)`，深层嵌套累计可到 `O(N³ log N)`；由仓库官方 Lua 5.1 toolchain 编译的临时可扩源码从深度 8 到 96 时，HIR lower 由约 1.04 ms 增至 38.7 ms，不过同期 Structure 已达约 234–256 ms。后续应先加聚合计数器分离扫描与 path-check 状态，再由 Structure 提供按 loop/branch identity 的 loop-bounded weak-postdom/selected continuation fact；不能用全局 region 缓存重新引入平方内存，也不能用不完整 predecessor 猜测丢掉合法 tail。
3. **table-constructor 非 use 类 rebuild 失败仍没有单调性分类**：binding facts、pending membership 与 `BindingIndex` 已改为分域 dense storage，producer 最后 use 之前的必败累计前缀也由 horizon 跳过；但到达 horizon 后，`try_extend_constructor_from_steps` 仍以 `Option` 合并所有失败原因，扫描器只能在后续每个 record/SETLIST 边界重试完整累计 steps。这里不能直接在首次失败后终止：后续 SETLIST 会切换整数 record 的 prefix policy，可能让旧前缀合法。若后续官方源码证明这部分仍形成显著长尾，应先把结果拆成 `BlockedByRemainingUse` 与已证明 prefix-monotonic 的失败类别，或改成可增量恢复的 speculative state，不能用清空 steps 掩盖候选。
4. **LuaJIT `LJLIB_LUA` 专用 opcode 尚无永久源码矩阵覆盖**：`TGETR/TSETR` 与 `ISTYPE/ISNUM` 由 LuaJIT `host/genlibbc.lua` 为 C 内建的 `LJLIB_LUA` 函数修补，普通 `.lua` 源码通过官方编译器不会生成这些指令；现有只接受可编译源码的 `cargo unit-test` 因此无法直接固化该协议。本轮已用仓库内官方 LuaJIT 运行时的 `string.dump(table.remove, true)` 临时产物核对：LIR 保留 3 次 raw read 和 3 次 raw write，hole + metatable 输入也证明普通索引改写会多触发 `__index/__newindex` 并改值。要关闭此项，需要先为“测试时由仓库官方 toolchain 产生内建 dump”建立清晰的测试分层与可重现合同；不提交 bytecode-only fixture，也不在 root `src/` 加 Rust 特例测试。
5. **same-header sibling latch 仍会被误拆成伪嵌套 loop**：`tests/regress-case/regress_169_same_header_conditional_sibling_latch.lua` 在 Lua 5.1/5.5 恢复为单个 `while true`，但 Lua 5.2/5.3/5.4 当前生成 `repeat; while not a do ... end; until b`。`src/structure/loops.rs::same_header_nested_outer_blocks` 只凭 header 两个 successor、inner/outer 集合关系和外层 backedge 形状就判定嵌套，没有证明 inner 拥有来自 outer-only 区域的独立 preheader，因此把同一 loop 的 sibling latch 当成两层源码 owner。现有 case 只禁止 goto/diagnostic，且固定布尔输入下伪结构恰好等价，未锁住结构形状。后续应先补可观察条件求值次数或明确结构断言，再要求 nested inner 具备唯一独立入口证据；`regress_128/167/170` 的合法 same-header 嵌套形状需同时回归，不能用方言特判。
6. **single-eval producer barrier 重复扫描同一区间**：`src/hir/analyze/exprs/regs.rs::expr_for_reg_use_single_eval_with_call_policy` 先调用 `def_has_intervening_use`，再调用 `def_has_intervening_observable_effect`，两者连续遍历同一 `(def, consumer)` 指令区间；递归展开长 producer chain 时会重复支付区间扫描成本。当前没有已证实的输出错误，但这是本轮 correctness owner 修复留下的明确性能清理项。后续可把寄存器 use 与 effect tag 合并成一次 barrier scan，保持现有“任一命中即拒绝移动”的合同，不应放宽 single-eval 边界。
7. **Lua 5.5 global declaration 协议仍可做防御性来源校验**：HIR 目前把“当前 `SetTable` 紧邻同名 `ErrNil`”视为前端给出的原子 global 声明，即使 Env base 与访问之间包含声明 probe 的可观察读取也允许恢复 global。官方 Lua 5.5 编译器及源码矩阵符合该合同；但 `access_is_global_decl` 尚未继续证明 `ErrNil.subject` 确实来自同 base/key 的 `GetTable` probe，手工构造的非标准 chunk 理论上可能撞形。后续若强化，应沿 canonical SSA use 回溯该 subject 并核对 probe 身份，不能重新用“区间完全无 effect”破坏合法宽常量声明。
