# 审计问题与交接清单

> 更新时间：2026-08-10
> 基线：当前 `dev`
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
