# 审计问题与交接清单

> 更新时间：2026-08-20
> 基线：`main@fbc45e0`
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

## 人工可读性审计队列

`cargo unit-test` 证明现有语义 oracle 与机器可读断言通过，不证明生成源码已经逐项达到人工
可读。当前已分段复查 regression 001–318，但尚未为每个 manifest entry 的每个 dialect 产物
形成“已优化”或“现状必要”的关闭证据；因此全量测试绿色不能作为本轮人工审计完成条件。

已定位 owner、可以围绕统一安全合同继续实现的高置信主题：

1. **跨分支/循环 handoff**：312。owner 是 deferred HIR carried-locals；它只能收回 immediate snapshot，不能沿 ancestry 合并到随后覆写的 carried state。
2. **机械控制与 materialization**：03、20、34、70 的 single-pass 壳；78 的 condition-only absorption；154 的 terminal nil pack；157、294 的 repeat 条件 scratch；175 的 close 声明前死 local；178 的可观察空 boolean shell；198、199、206、209 的 Luau 大量临时链；222 的稳定 binding 吸收律；266 的无效 nil arm；267 的 generic-for 准备间隔。
3. **函数展示策略**：02、05、07、10、11、17、29、33、38、42、52、59、81、82、83、126、134，以及 250、251、255、258、275、293、301、310、314，仍会把源码命名 local function 压成多行 IIFE。需要区分短小 capture-free 立即调用与应保留声明的多行 closure，不能全局禁止或全局强制内联。
4. **formatter 展示**：161、163、164 的大型 constructor 固定为一项一行，229 的逻辑表达式形成超长物理行。需要独立的稳定换行策略，不在 HIR 中为排版改写语义树。

仍需先补齐语义证明、不得直接按输出形状改写的候选包括 35、40、86、94、100、101、109、
112、116、117、123、152、156、157、208、226、252、265、270、291、296、311。它们涉及
循环入口 phi、并行 snapshot、closure identity、continue latch、构造器求值或资源作用域，应与
上面的高置信主题分开处理。

关闭本节必须逐项核对源码与当前生成产物；可安全优化的主题完成实现、负例和运行 oracle，
不能证明安全的主题保留原因与最小反例。仅有“未再发现失败”或全量测试通过不构成关闭证据。
