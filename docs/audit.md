# 审计问题与交接清单

> 更新时间：2026-08-23
> 审计起点：`main@ce3ad8e`
> 当前复核：本次 residual 收口
> 本文件只保留尚未完成、需要后续决策或仍需安全证明的事项；完成项应立即删除。

## 审计规则

1. **宽松生成必须保留**：结构恢复不完整时，用户仍应看到尽可能多的逻辑。宽松模式允许保留必要的 `goto` / `label` 和 `unluac error` 占位；严格模式要求目标方言可重新编译。
2. **诊断写入输出，不写 stderr**：诊断伪源码由首行 `unluac error` 注释和 `GeneratedChunkKind::DiagnosticPseudocode` 标识，不额外打印目标方言警告。
3. **错误注释不能删除**：它保留其余可读逻辑，也让用户能定位反编译器缺口。
4. **安全证明优先于形状断言**：任何内联、构造器折叠、binding 合并或 root 缩短，都必须同时证明求值顺序、词法身份、GC 存活和目标方言语义；无法证明时保留机械形状或返回诊断。

## 待处理问题

当前没有待处理项。已经证明属于 VM/源码表达边界或精确语义证据的数据结构不再作为可读性
优化缺口登记；只有出现新的等价性证明或真实错误复现时才重新立项。

## 当前验证基线

- `cargo fmt --all -- --check`：通过。
- `cargo clippy --workspace --all-targets --all-features --locked -- -D warnings`：通过。
- `cargo test --workspace --all-targets --locked`：通过。
- `cargo unit-test --suite all --recompile-rounds 1 --jobs 8 --progress off`：1250/1250 entries
  通过，`timed_out=0`；1714/1714 proto 通过。
