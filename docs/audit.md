# 审计问题与交接清单

> 更新时间：2026-07-16
> 基线：当前 `dev`
> 本文只记录尚未解决且已经取证的问题、明确风险和已确认的设计决定；完成项立即删除。

## 不应回退的决定

1. **宽松生成必须保留**：结构恢复不完整时，用户仍应看到尽可能多的逻辑。宽松模式允许保留必要的 `goto` / `label` 和 `unluac error` 占位；严格模式才要求目标方言可重新编译。
2. **诊断写入输出，不写 stderr**：诊断伪源码由首行 `unluac error` 注释和 `GeneratedChunkKind::DiagnosticPseudocode` 标识，不再额外打印“目标方言不支持 goto/label”的 stderr 警告。
3. **错误注释不能删除**：它既保留其余可读逻辑，也让用户能定位并反馈反编译器缺口。
4. **允许高价值大改**：涉及层次职责、核心数据模型和跨 pass owner 时，直接替换错误架构，不保留兼容层、双轨事实或后层 fallback。

## 未解决问题

1. **LuaJIT `ISTYPE/ISNUM` 尚无严格源码表达**：官方 `LJLIB_LUA` 内建函数用这两条指令实现 `CHECK_str/func/tab/int/num`；失败路径调用 `lj_meta_istype`，其中 string/integer/number 还会原地隐式转换。Transformer/HIR 现已保留 `TypeGuard` 的读取、顺序和具体 expected type，宽松模式能继续恢复余下函数，严格模式会拒绝 unresolved guard；但直接生成 `assert(type(...))` / `tonumber(...)` 会依赖可覆盖全局且不满足 LuaJIT 的错误与 `int32` 转换合同，不能冒充等价源码。后续若要关闭此项，需要先确定一个目标方言 helper 合同或正式的内建伪源码输出模式。
2. **按需 branch region 集合仍有嵌套平方上界**：`BranchRegionFact` 已用支配区间消除 StructureFacts 中每个 suffix 的常驻集合，但 HIR 的 `branch_stops/path_checks/break_pads/loop state` 在需要集合接口时仍会 materialize 当前 header 的支配子树。普通短路根只消费一次，不再触发该成本；深层嵌套分支若逐层要求完整 region，累计访问量仍可能是 `Σregion_size`。后续应让这些消费者直接接受支配区间 membership/iterator，只有确实需要可变并集的局部路径才分配集合，不能用全局缓存重新引入平方内存。
