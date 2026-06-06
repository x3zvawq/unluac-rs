# Copilot Instructions

当前仓库的核心文档入口如下：

- 设计文档见 [design.md](./design.md)，当你刚开始接手这个项目的时候务必阅读。如果需要修改某一层次的业务实现的时候 **必须** 先阅读对应层次的文档。并且如果在修改了仓库中的业务代码（比如增加了某些 helper 方法，或者某些 facts 可以给后层消费的）需要同步更新文档。
- 调试手册见 [debug.md](./debug.md)，排查错误、需要调试 cli 以及库的时候**务必阅读**。
- 仓库内有完整的lua执行环境，见 [lua/README.md](../lua/README.md)。

## 工作时一定、必须遵循的规则

- 务必使用以下skills: rust-best-practices
- 该项目目前处在测试阶段，因此修改的时候可以大刀阔斧激进修改结构，写注释的时候也需要注意不要遗留早期口径, 比如“这里这么改是因为之前xxx”的口径应该直接写成“这里的考量是”
- 当在某个case下发现问题的时候，应该尽可能追踪是不是更早的某个层次漏掉了什么东西或者写错了什么。**不要** 在后面的层次为前面缺失或者错误的东西兜底；**永远不要** 用堆特判的方式去让某个问题不再出现，而是应该在遇到问题的时候定位问题的根源尝试从结构上去修复问题。判定规则是永远都写不完的，再多的判定规则也总是会被特定的case hack。
- 如果要解决的问题，本质上只是现有某个 pass 已经在处理的同类形状因为约束过窄而漏掉了，那么应优先扩充这个 pass 或它的共享 helper，而不是平行再新建一个 pass 去接同一类职责。
- 每一个文件头都需要通过中文文档注释的方式解释当前文件的的设计理念，也就是说为啥要要有这个文件？这个文件提供什么方法或者struct？然后当你修改某个文件的时候也需要判断是否需要同步更新注释。从 `StructureFacts` 开始，所有 pass 风格文件都应带中文说明，至少说明：这个 pass 解决什么问题、它依赖哪一层已提供的事实、它不会越权做什么、至少一个“输入形状 -> 输出形状”的例子。同样当修改pass的时候也需要酌情修改注释。在代码可能产生误解或者代码本身不足以解释“为什么”的时候也需要补充中文注释，告知维护者某一段代码为什么存在，拒绝翻译代码的注释，也就是说你需要做的是讲清楚“为什么”而非“做什么”。
- 当某个文件超过1000行的时候，**需要特别注意** 是否可以根据职责 或者 根据关注点进行拆分，当然如果确实职责一致且关注点一致的话可以保留长度过长的文件。
- 测试代码不要放在根 crate 的 `src/` 中；`src/` 只保留实现。测试体系只保留两类公开测试：`tests/unit-case/` 下的源码 case 作为单元测试，`tests/regress-case/` 下的最小源码复现作为回归测试。两类测试统一通过 `cargo unit-test` 驱动完整流程，不再使用 `tests/regression/` 或 `cargo test --test regression`。
- 测试 case 必须是可由仓库官方 Lua toolchain 编译的源码文件，不支持只提交 `.luac` / `.luau` 的 bytecode-only case。反编译可读性问题通过 Lua 注释中的机器可读 `unluac:` 断言表达，例如 `expect-contains`、`expect-not-contains`、`expect-order`。
- 该库需要考虑到编译成wasm模块的方式分发，因此需要避免使用某些导致库无法编译为wasm模块的操作或者依赖。
- 调试时临时文件可以在tmp里读写，但是不能假设这个目录里的文件会持久存在。如果需要持久存在的测试样例应该考虑丢到`tests/lua_cases`里。
- 每一轮工作完成如果修改了业务代码则需要通过一下两条命令进行验证。
  - `cargo clippy --workspace --all-targets --all-features --locked -- -D warnings`
  - `cargo unit-test --jobs 8`
- 当更新了decompile参数输入的时候，需要同步更新以下项目：
  - `README.md/README_en.md` 中的参数列表
  - `packages/unluac-js/src/index.ts` js包装库中的类型声明
  - `packages/unluac-cli/src/cli.rs` cli工具中的参数解析部分
  - `packages/unluac-wasm/src/lib.rs` wasm库中的参数解析部分
  - `packages/unluac-web` 前端入口的setting panel、参数说明、传入等
- 提交信息应该只使用一行："type(scope): description"，其中 type 是 feat/fix/refactor/test/doc/chore 之一，scope 是修改的模块或者层次，description 是简短的描述。比如 "fix(transformer): handle missing loop body"。不需要描述修改细节，使用中文。
