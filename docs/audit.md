# 审计问题与交接清单

> 更新时间：2026-07-18
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
4. **while/repeat 的 `if/elseif continue` 仍会抢占后续 break tail**：Luau O0/O1/O2 下，只要一臂含副作用、另一臂条件 continue，且两臂之后还有共享 break guard，HIR 就会因重复访问近端 tail 而 panic；numeric/generic-for 同矩阵正常。Structure 已完整给出 branch、continue 与 break owner，缺口在 `loop_body_shared_continuation_stop` 没有接受“tail 自身是 merge 到 post-loop 的 break branch”。修复必须分别验证 while 的显式 continue edge 与 repeat 的 condition-block owner，不能放宽通用 visited fallback。
5. **嵌套 repeat 的条件写回仍会留下 live-out generic phi**：PUC Lua 5.1-5.5 下，numeric-for 内 repeat 若条件臂更新外层值、另一条路径提前 break，随后共享 tail 再读取该值，Structure 会在连续 merge 上留下 unresolved generic phi；严格模式拒绝，宽松模式可生成通过语法检查但运行时对 nil 做算术的错误源码。当前还会把 inner break 后进入 outer numeric latch 的边误记为 unstructured continue。应先在 Structure 补齐 branch/loop value owner 与跨层 control edge，再由 HIR 消费，不能在 AST 或宽松输出里猜默认值。
