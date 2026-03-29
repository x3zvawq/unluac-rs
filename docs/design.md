# 维护地图

这组文档描述仓库的代码地图、层间事实边界、共享设施与维护约束。

阅读这些文档时应当默认采用下面的维护视角：

- 先确认某个事实应当由哪一层产出，再决定改动落点。
- 先复用该层已经声明好的 helper、query、macro、walker、visitor，再考虑新增实现。
- 后层只消费前层事实；如果后层开始回看底层细节，通常意味着 owner 放错了。
- 生成层、命名层、可读性层都不负责给更前层补事实。

分层文档入口：

- [0.introduce.md](./design/0.introduce.md)
- [1.parser.md](./design/1.parser.md)
- [2.transformer.md](./design/2.transformer.md)
- [3.cfg-dataflow.md](./design/3.cfg-dataflow.md)
- [4.structure.md](./design/4.structure.md)
- [5.hir.md](./design/5.hir.md)
- [6.ast.md](./design/6.ast.md)
- [7.readability.md](./design/7.readability.md)
- [8.naming.md](./design/8.naming.md)
- [9.generate.md](./design/9.generate.md)
- [10.debugging.md](./design/10.debugging.md)
- [11.test.md](./design/11.test.md)

推荐阅读顺序：

1. 先读 [0.introduce.md](./design/0.introduce.md) 了解全局边界。
2. 改某一层时，再读对应层文档与它的前一层文档。
3. 改跨层问题时，从最早可能持有该事实的层开始看，不要从报错位置开始补丁式修复。
