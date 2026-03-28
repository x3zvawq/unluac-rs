# 重构计划

这份文档是当前代码库的重构 backlog。

后续每做完一项，就直接勾掉或删掉对应条目，不保留已经解决的历史负担。

## 范围与约定

- 审查顺序按 `Parser -> Transformer -> CFG -> GraphFacts -> Dataflow -> StructureFacts -> HIR -> AST -> Naming -> Generate`。
- 当前代码库实际上还存在独立的 `Readability` 阶段，并且很多问题集中在那里。
  本文会把它单独列出来，而不是硬塞进 AST，避免遗漏真实问题。
- 重构时优先修“前层事实没有表达好，导致后层重复推断/反复兜底”的根因，不接受靠补特判压 case。
- 从 `StructureFacts` 开始，所有 pass 风格文件都应该补齐统一的中文说明：
  - 这个 pass 解决什么问题
  - 它依赖哪一层已经提供好的事实
  - 它不会越权做什么
  - 至少给一个“输入形状 -> 输出形状”的例子

## 当前总体判断

- `Parser` 和 `Transformer` 的方言实现已经出现“同构骨架在多个版本文件里平行复制”的趋势，继续加 dialect 会越来越重。
- `GraphFacts`、`Dataflow`、`StructureFacts`、`HIR` 之间已经有一部分“前层给了候选，但后层还要自己再把底层事实拼回去”的现象。
- `HIR simplify`、`AST readability`、`Generate` 里已经有多个超过 1000 行的大文件，且不少文件内部同时承担了多种关注点。
- 当前代码库在 `cargo clippy --all-targets --all-features --locked -- -D warnings` 下并不干净，说明还有一批低风险但必须清掉的 Rust 写法问题。

## 需要先定方向的设计决策

### 1. Parser / Transformer 的共享骨架抽到什么粒度

方案 A：继续按 dialect/version 保持大文件，只抽局部 helper。

- 优点：版本差异最直观，重构风险较低。
- 缺点：重复骨架还会继续扩散，大文件问题不会真正消失。

方案 B：抽 family 级共享骨架，只把版本差异留在 spec / helper / opcode lowering 表。

- 优点：能明显消掉重复实现，也更符合“前层统一表达事实”的目标。
- 缺点：第一轮重构更大，需要先把 family 边界设计清楚。

建议：先对 `PUC-Lua 5.2/5.3/5.4/5.5` 走方案 B；`LuaJIT` 和 `Luau` 先保留独立骨架。

原因：PUC-Lua family 的 parser / lowerer 现在已经出现明显的“同一套骨架，混入少量版本差异”的形状，继续复制不划算；而 LuaJIT、Luau 的二进制协议差异更大，先不要硬并。

### 2. Readability 是继续独立 stage，还是并回 AST

方案 A：继续保持独立 stage。

- 优点：边界清楚，`AST lowering` 只负责“合法语法”，`Readability` 只负责“更像源码”。
- 缺点：如果边界维护不好，会出现 AST build 和 Readability 都在做模式恢复。

方案 B：并回 AST，统一放在 AST 层内部。

- 优点：调用链更短，少一个 stage 名字。
- 缺点：更容易把“合法性 lowering”和“可读性美化”重新搅在一起。

建议：继续独立 stage，但要把 AST build 中现有的 readability 风格模式识别往外挪。

### 3. Naming 的核心入口是否继续直接吃 `RawChunk + HirModule + AstModule`

方案 A：维持当前接口 `assign_names(ast, hir, raw, options)`。

- 优点：调用方便，暂时不用改上游接口。
- 缺点：Naming 核心继续直接穿透到 Parser/HIR，边界不够干净。

方案 B：把 `NamingEvidence` 的构建独立出来，Naming 核心只吃 `AST + NamingEvidence + Options`。

- 优点：符合设计文档，也更容易测试和替换证据来源。
- 缺点：入口层要补一层 evidence builder。

建议：走方案 B。

## 跨层优先事项

- [ ] [P0] 先把代码库恢复到 `cargo clippy --all-targets --all-features --locked -- -D warnings` 通过。
  当前已确认的问题包括：
  - `src/ast/readability/global_decl_pretty.rs` 的递归参数与重复分支问题
  - `src/hir/analyze/structure/body/branches.rs`、`src/hir/analyze/structure/loops.rs`、`src/hir/simplify/table_constructors.rs` 等处可以直接改成 `?`
  - `src/naming/allocate.rs`、`src/parser/dialect/luajit/parser.rs` 的参数过多
  - `src/parser/dialect/luau/parser.rs` 的返回类型过于复杂
- [ ] [P0] 建立统一的 pass 注释模板，并补齐从 `StructureFacts` 开始的 pass 风格文件。
- [ ] [P0] 对所有超过 1000 行的实现文件建立拆分清单，重构时优先按“职责/关注点”切开，而不是继续在大文件上堆逻辑。

## 分层清单

### Parser

- [ ] [P0] 抽取 PUC-Lua family 的共享 parser 骨架，避免 `parse_header / parse_proto / parse_constants / parse_debug_info` 在 `lua52/lua53/lua54/lua55` 中继续平行复制。
- [ ] [P1] 收敛 `src/parser/dialect/luajit/parser.rs` 的 `parse_debug_info` 参数列表，改成上下文 struct，顺手消掉 `too_many_arguments`。
- [ ] [P1] 收敛 `src/parser/dialect/luau/parser.rs` 的复杂返回元组，改成具名结果 struct，避免“记不住第几个元素是什么”。
- [ ] [P1] 评估 Luau proto tree 构建中的 clone 路径，避免 `build_proto_tree` 一边缓存一边复制整棵 proto。
- [ ] [P1] 把“共享 reader 基础设施”和“版本专属协议解释”再明确拆开，避免下一次新增版本时再复制一整份 parser 文件。
- [ ] [P2] 检查 parser 层是否还有“本该在 parser 保存的协议事实，后面才靠猜补回来”的点；找到后优先上移到 raw 层。

### Transformer

- [ ] [P0] 抽取 family 级 lowering 骨架，统一 `ProtoLowerer`、`PendingLowInstr`、跳转目标回填、`LoweringMap` 组装、`raw_pc -> raw_index` 等通用流程。
- [ ] [P0] 抽取 operand shape 校验 helper，避免 `expect_a / expect_ab / expect_abc / expect_asbx ...` 在各个 lowerer 里重复维护。
- [ ] [P1] 拆分以下超长文件：
  - `src/transformer/dialect/lua55/lower.rs`
  - `src/transformer/dialect/lua54/lower.rs`
  - `src/transformer/dialect/luau/lower.rs`
  - `src/transformer/dialect/luajit/lower.rs`
  - `src/transformer/dialect/lua53/lower.rs`
  - `src/transformer/dialect/lua52/lower.rs`
  - `src/transformer/dialect/lua51/lower.rs`
- [ ] [P1] 统一 `env upvalue`、call/result pack、for-loop lowering 这类家族共性逻辑的抽象层，减少版本文件里“业务逻辑 + 样板 emit”混写。
- [ ] [P1] 补一轮现代 Rust 写法整理，尤其是 `?`、`let-else`、具名上下文 struct，减少长函数里的机械 match。

### CFG

- [ ] [P1] 复查 CFG 层对后续层暴露的查询能力是否足够；如果 `StructureFacts/HIR` 仍然要自己重复写 block/edge 查询 helper，优先把稳定查询能力补在 CFG/GraphFacts 边界，而不是散落到后层。
- [ ] [P2] 评估 `cfg` 相关共享类型是否需要进一步按“构图事实 / 图分析事实 / 数据流事实”拆开，避免 `common.rs` 继续膨胀。

### GraphFacts

- [ ] [P0] 消除 `src/cfg/graph.rs` 内部的重复计算。
  当前 `analyze_graph_facts()` 会多次重新算 dominator tree / backedges / loop headers / natural loops，而不是一次算出后复用。
- [ ] [P1] 把图分析内部常用的 visited / frontier / reachable 集从 `BTreeSet` 优先替换成更贴合主路径的稠密结构或 bitset。
- [ ] [P1] 如果后层频繁需要“最近公共后支配点”“结构 region 入口/出口”之类稳定图查询，优先在这一层或下一层显式产出，而不是让后层自己再写 BFS。

### Dataflow

- [ ] [P0] 拆分 `src/cfg/dataflow.rs`。
  当前一个文件同时承担：
  - effect 计算
  - defs / open-def 建模
  - reaching defs 求解
  - liveness 求解
  - phi candidate 生成
  - SSA-like value materialization
- [ ] [P0] 压缩热路径里的 `BTreeMap/BTreeSet + clone` 使用，优先向稠密向量、bitset、轻量小集合收拢。
  当前 `fixed_in/fixed_out/open_in/open_out` 与 instr snapshot 存在明显整块 clone。
- [ ] [P1] 评估是否要把“后层经常直接索引的底层数组”封装成更明确的 query API，减少后续层直接揉 `phi_candidates/use_values/reaching_defs` 的裸下标逻辑。
- [ ] [P1] 复查 open pack 的数据流事实是否已经足够直接给 HIR/AST 使用；不够的话继续在 Dataflow 补事实，不要让后层再去“猜开放尾值的前缀”。

### StructureFacts

- [ ] [P0] 抽取结构层共享 query/cache，避免 `branches/loops/goto/regions/scope/short_circuit` 各自重复做可达性、出口、entry-edge、branch-region 扫描。
- [ ] [P0] 让 StructureFacts 对 HIR 更“可直接消费”。
  当前一个明显症状是：HIR 在消费 `branch_value_merge_candidates` 时，仍要回头再查 `dataflow.phi_candidates` 取 incoming defs。
- [ ] [P1] 评估是否应把 loop source-visible binding 证据前移到 StructureFacts。
  当前 `hir/analyze/bindings.rs` 还在重新扫 low-IR/CFG 找 numeric-for / generic-for 的源码绑定寄存器。
- [ ] [P1] 统一结构层文件头注释模板，并补“输入形状 -> 候选产物”的例子。
  当前不少文件虽然有中文说明，但还没有形成统一的例子化注释。
- [ ] [P2] 提前拆分 `short_circuit` 内部的“条件出口型识别”和“值合流 DAG 提取”，避免后续继续膨胀成单个巨型模块。

### HIR

- [ ] [P0] 拆分以下超长文件：
  - `src/hir/analyze/short_circuit.rs`
  - `src/hir/analyze/exprs.rs`
  - `src/hir/analyze/structure/loops.rs`
  - `src/hir/simplify/temp_inline.rs`
  - `src/hir/simplify/table_constructors.rs`
  - `src/hir/simplify/decision/synthesize.rs`
- [ ] [P0] 合并 `src/hir/simplify/decision.rs` 与 `src/hir/simplify/logical_simplify.rs` 中重复的递归遍历骨架，抽出共享 visitor / folder。
- [ ] [P0] 继续减少 HIR 对底层事实的回看式拼装。
  重点检查：
  - branch value merge 仍回查 `phi_candidates`
  - loop binding/local 恢复仍回扫 low-IR/CFG
  - 某些 `entry_overrides/phi_overrides` 逻辑是否本该由更前层直接给证据
- [ ] [P1] 复查 fixed-point 调度里“同一 pass 重跑多次”的原因，明确哪些是必要依赖，哪些是当前边界不清导致的兜底。
  当前至少有：
  - `table-constructors` 在 `locals` 前后各跑一次
  - `locals` 在 `close-scopes` 前后各跑一次
- [ ] [P1] 落一轮现代 Rust 写法整理，尤其是结构恢复分支里的 `?`、`let-else`、简化控制流。
- [ ] [P1] 补齐 simplify pass 的注释例子。
  当前优先补：
  - `logical_simplify.rs`
  - `dead_labels.rs`
  - 以及其它只写了抽象描述、没有具体输入输出例子的 pass 文件

### AST

- [ ] [P0] 重新划清 AST build 与 Readability 的职责边界。
  当前 `src/ast/build/patterns.rs` 已经在做：
  - method call alias / chain
  - global decl 形状
  - forwarded multiret call
  - installer IIFE call
  这些里既有“合法语法 lowering”，也有“更像源码的模式恢复”，边界已经开始混。
- [ ] [P0] 拆分以下超长文件：
  - `src/ast/readability/inline_exprs.rs`
  - `src/ast/readability/global_decl_pretty.rs`
  - `src/ast/readability/function_sugar.rs`
- [ ] [P1] 把 AST build 中仅仅为了“更好看”的模式恢复尽量迁回 Readability，让 AST build 主要承担“合法语法化”职责。
- [ ] [P1] 把 `src/ast/readability/global_decl_pretty.rs` 按关注点拆开。
  这个文件当前同时承担：
  - seed run merge
  - explicit global 收集
  - nested write 收集
  - missing global 推断
  - decl 插入
- [ ] [P1] 检查 AST build 与 Readability 是否存在“不同 pass 在解决同一个问题”的重叠。
  优先看：
  - method/function sugar
  - global decl 相关恢复
  - call alias / call arg 美化
- [ ] [P1] 补齐 AST readability pass 的中文注释例子。
  当前优先补：
  - `branch_pretty.rs`
  - `cleanup.rs`
  - `function_sugar.rs`
  - `global_decl_pretty.rs`
  - `materialize_temps.rs`
  - `statement_merge.rs`

### Readability

- [ ] [P0] 明确写进代码与文档：Readability 继续作为独立 stage 存在，不负责给前层过度内联/过度结构化兜底。
- [ ] [P1] 收敛 AST readability 各 pass 重复出现的递归 walker / statement clone 样板，减少“每个 pass 自己抄一套 rewrite_block/rewrite_stmt/rewrite_expr”。
- [ ] [P1] 复查 stage 顺序，并把“为什么是这个顺序”写到代码注释里，而不是只保存在设计文档里。
- [ ] [P1] 检查 `cleanup` 作为后置 pass 的重复调用是否可以抽象成 stage helper，避免 stage 表手写重复。

### Naming

- [ ] [P0] 把 Naming 核心入口收缩到 `AST + NamingEvidence + NamingOptions`，不要让 Naming 主入口继续直接吃 `RawChunk + HirModule`。
- [ ] [P0] 把 `src/naming/allocate.rs` 的 `assign_names_for_function()` 改成 context struct，避免参数过多，也让职责边界更清楚。
- [ ] [P1] 把 NamingEvidence 的构建链路从 Naming 主流程中拆开，形成“证据构建”和“名字分配”两个独立可测的步骤。
- [ ] [P1] 检查 `naming/evidence.rs` 是否继续膨胀成另一套 HIR walker；如果继续增长，就要按“capture provenance / debug names / temp hints”拆分。
- [ ] [P2] 在接口收敛之后，再做一轮 clone 与字符串分配审查，优先消掉明显的机械复制。

### Generate

- [ ] [P0] 拆分 `src/generate/emit.rs`。
  当前一个文件同时承担：
  - NameMap 解析
  - feature 校验
  - stmt emit
  - expr emit
  - precedence / 括号决策
  - literal / table layout 辅助
- [ ] [P1] 明确拆开“名字解析”和“AST -> Doc lowering”的关注点，避免 emitter 继续变成一个全知对象。
- [ ] [P1] 检查 `Generate` 是否还在替前层兜底任何语法/命名问题；如果存在，一律上移修正，不在 Generate 补猜。
- [ ] [P2] 视拆分结果决定是否把表达式 precedence、表构造器布局、字符串/数字字面量格式化再拆成更细的 helper 模块。

## 第一批建议先做的事项

- [ ] 先修 Clippy 报出来的 14 个确定问题，保证后续重构时不会混进旧噪音。
- [ ] 先定 `Parser/Transformer` 的 family 共享骨架方案。
- [ ] 先把 `GraphFacts` 的重复计算去掉，因为这属于“前层内部自己没复用好自己产出的事实”。
- [ ] 先拆 `Dataflow`、`HIR temp_inline`、`AST global_decl_pretty`、`Generate emit` 这几个最重的大文件。
- [ ] 然后再做 `StructureFacts -> HIR` 的证据前移，减少后层重新拼底层事实。

## 当前已确认的超长文件

- `src/transformer/dialect/lua55/lower.rs`
- `src/transformer/dialect/lua54/lower.rs`
- `src/transformer/dialect/luau/lower.rs`
- `src/transformer/dialect/luajit/lower.rs`
- `src/hir/simplify/temp_inline.rs`
- `src/ast/readability/inline_exprs.rs`
- `src/hir/analyze/short_circuit.rs`
- `src/transformer/dialect/lua53/lower.rs`
- `src/transformer/dialect/lua52/lower.rs`
- `src/ast/readability/global_decl_pretty.rs`
- `src/hir/simplify/decision/synthesize.rs`
- `src/cfg/dataflow.rs`
- `src/hir/simplify/table_constructors.rs`
- `src/hir/analyze/structure/loops.rs`
- `src/parser/dialect/lua55/parser.rs`
- `src/generate/emit.rs`
- `src/hir/analyze/exprs.rs`
- `src/ast/readability/function_sugar.rs`

后续如果这些文件在重构过程中继续增长，优先先拆再加逻辑，不要继续堆。
