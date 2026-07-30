# 审计问题与交接清单

> 更新时间：2026-07-30
> 基线：当前 `dev`
> 本文只记录尚未解决且已经取证的问题、明确风险和已确认的设计决定；完成项立即删除。

## 不应回退的决定

1. **宽松生成必须保留**：结构恢复不完整时，用户仍应看到尽可能多的逻辑。宽松模式允许保留必要的 `goto` / `label` 和 `unluac error` 占位；严格模式才要求目标方言可重新编译。
2. **诊断写入输出，不写 stderr**：诊断伪源码由首行 `unluac error` 注释和 `GeneratedChunkKind::DiagnosticPseudocode` 标识，不再额外打印“目标方言不支持 goto/label”的 stderr 警告。
3. **错误注释不能删除**：它既保留其余可读逻辑，也让用户能定位并反馈反编译器缺口。
4. **允许高价值大改**：涉及层次职责、核心数据模型和跨 pass owner 时，直接替换错误架构，不保留兼容层、双轨事实或后层 fallback。

## 未解决问题

1. **LuaJIT `ISTYPE/ISNUM` 尚无严格源码表达**：官方 `LJLIB_LUA` 内建函数用这两条指令实现 `CHECK_str/func/tab/int/num`；失败路径调用 `lj_meta_istype`，其中 string/integer/number 还会原地隐式转换。Transformer/HIR 现已保留 `TypeGuard` 的读取、顺序和具体 expected type，宽松模式能继续恢复余下函数，严格模式会拒绝 unresolved guard；但直接生成 `assert(type(...))` / `tonumber(...)` 会依赖可覆盖全局且不满足 LuaJIT 的错误与 `int32` 转换合同，不能冒充等价源码。后续若要关闭此项，需要先确定一个目标方言 helper 合同或正式的内建伪源码输出模式。
2. **LuaJIT `LJLIB_LUA` 专用 opcode 尚无永久源码矩阵覆盖**：`TGETR/TSETR` 与 `ISTYPE/ISNUM` 由 LuaJIT `host/genlibbc.lua` 为 C 内建的 `LJLIB_LUA` 函数修补，普通 `.lua` 源码通过官方编译器不会生成这些指令；现有只接受可编译源码的 `cargo unit-test` 因此无法直接固化该协议。本轮已用仓库内官方 LuaJIT 运行时的 `string.dump(table.remove, true)` 临时产物核对：LIR 保留 3 次 raw read 和 3 次 raw write，hole + metatable 输入也证明普通索引改写会多触发 `__index/__newindex` 并改值。要关闭此项，需要先为“测试时由仓库官方 toolchain 产生内建 dump”建立清晰的测试分层与可重现合同；不提交 bytecode-only fixture，也不在 root `src/` 加 Rust 特例测试。
3. **Luau 带 capture 的重复 `DUPCLOSURE` 尚未源码化**：同一 closure constant 在多个静态位置出现时，VM 会按首次 capture 与后续 capture 的 raw equality 决定复用对象；即使两个位置读取同一 SSA 值，`NaN` capture 也会让对象身份不同，因此不能静态 alias。Transformer 已区分 `Reusable` 与 `Fresh`，capture-free 重复引用已正确恢复；带 capture 的重复引用当前 fail-fast。要关闭此项，需要为每个父 proto 局部 shared 引用合成单一词法 factory owner，让目标 Luau 编译器重新产生同一 `DUPCLOSURE` site，而不是在 HIR/AST 猜测运行期相等性。
4. **natural-loop 成员合同仍会在深层嵌套上展开为二次 incidence**：最终 StructurePlan 的 branch domain、edge/phi/cleanup validator 已改为稠密索引和区间，但 `cfg/graph.rs::compute_natural_loops` 仍为每个 header 反向物化完整 `NaturalLoop.blocks`，随后 `loops.rs`、`goto.rs`、`branches.rs` 和 `plan/arena.rs::LoopPartitions` 又把每个 block 展开到全部祖先 loop。普通编译器受语法嵌套上限约束，现有 corpus 与 16k 顺序分支压力样例不会触发灾难性退化；人工构造的深层可规约 CFG 仍可达到 Θ(blocks × loop-depth) 时间与内存。要关闭此项，需要一次独立 `perf(structure)` 主重构：用 LLVM LoopInfo 风格的子 loop 收缩构建 `NaturalLoopForest`，保存唯一 `innermost_by_block + loop parent + direct blocks`；Structure 再建立 canonical semantic loop forest 和 dense `LoopPart`，删除 `LoopCandidate.blocks/body_scope_blocks/control_blocks`、逐候选 subset/clone 以及每 loop 的 body BFS。DSU 实现的严谨复杂度是 `O((blocks + edges) α(blocks))`，不能继续在文档或交付说明中把这条尚未完成的 evidence 路径声称为纯线性。
   同一主题还包括 `hir/analyze/bindings.rs::region_blocks`：它目前为每个嵌套 loop
   重新枚举 body subtree，并把外围 for binding 展开到每个后代 block。后续应让
   binding owner 直接挂在 region/loop forest 上，由 lowering 按 ancestor stack 查询，
   不再复制 `loop × descendant block` 映射。
