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
2. **branch-stop 通用 continuation 搜索仍有嵌套平方访问上界**：HIR 的 membership-only 消费者已直接查询 `BranchRegionFact`，single-pass repeat/shared loop tail 也已收窄到 CFG predecessor 与已知 nested-loop preheader，不再 materialize region 集合；但 `loop_body_shared_continuation_stop` 仍会为每层 branch 扫描完整支配区间，深层嵌套累计访问量可能是 `Σregion_size`。后续应由 Structure 提供 loop-bounded postdom/selected continuation 事实或等价的有界候选索引；不能用全局 region 缓存重新引入平方内存，也不能用不完整 predecessor 猜测丢掉合法 tail。
3. **超大表构造器仍有显著 HIR 长尾**：`lua52_03_extraarg_boundary.lua` 含 267,394 条 HIR stmt、262,145 个字段；三轮独立计时中，`table-constructors` 首轮约 1.64–3.90 秒，第二个空轮仍需 36–74 毫秒。首轮热点已定位为 binding summary/intern（763–2,374 毫秒）和 region rebuild（291–721 毫秒），不是 fixed-point 空轮；临时 dense `BindingIndex` 实验可把 summary 降到 56–86 毫秒、整 pass 降到 0.91–1.41 秒，dense materialized lookup 也有稳定收益。后续应以按 `TempId/LocalId` 索引的 dense storage 替换这些 `BTreeMap`；累计 `steps` 的重复前缀 rebuild 与 pending producer 的线性成员扫描也要一并消除，不能只换 `HashMap` 或放宽测试超时。
4. **Luau closure 常量归一化是显式平方查找**：`parser/dialect/luau/parser.rs::normalize_constants` 为每个 closure 常量都对完整 `child_indices` 调用 `.position(...)`，当一个 proto 同时含有大量 child 和 closure 常量时上界为 `O(constants × children)`。应在单次 normalization 前建立 `proto_index -> child_proto_index` 索引，并保留现有“缺少映射立即报 `InvalidLuauClosureProto`”的 fail-fast 边界；不应用缓存整个常量池或放宽无效索引来换性能。
5. **LuaJIT `LJLIB_LUA` 专用 opcode 尚无永久源码矩阵覆盖**：`TGETR/TSETR` 与 `ISTYPE/ISNUM` 由 LuaJIT `host/genlibbc.lua` 为 C 内建的 `LJLIB_LUA` 函数修补，普通 `.lua` 源码通过官方编译器不会生成这些指令；现有只接受可编译源码的 `cargo unit-test` 因此无法直接固化该协议。本轮已用仓库内官方 LuaJIT 运行时的 `string.dump(table.remove, true)` 临时产物核对：LIR 保留 3 次 raw read 和 3 次 raw write，hole + metatable 输入也证明普通索引改写会多触发 `__index/__newindex` 并改值。要关闭此项，需要先为“测试时由仓库官方 toolchain 产生内建 dump”建立清晰的测试分层与可重现合同；不提交 bytecode-only fixture，也不在 root `src/` 加 Rust 特例测试。
6. **nested hoisted-local 搜索存在三次上界**：`statement_merge::try_sink_hoisted_decl_into_nested_stmt_anywhere` 对长度 `p` 的候选 run 枚举 start 与 end，每次又重建 binding 集合并扫描 slice，失败路径最坏 `O(p³)`。后续应按真实 mention 定位少量连续区间或缓存前缀集合，不能让大函数的展示层下沉成为主耗时。
