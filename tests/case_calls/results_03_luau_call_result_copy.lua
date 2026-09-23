-- 活动低槽赋值必须重发 callee scratch 与 CALL 结果回写；独立提升 scratch 会逐轮增长。
-- 同槽 CALL→GETTABLEKS 是一个 initializer，读取结果之后的 COPY 才建立第二个源码身份。
-- unluac: expect-contains [[getfenv().print]]
-- unluac: expect-ast-count [[local-binding]] [[2]]
-- unluac: expect-ast-count [[assign]] [[1]]
local fn = getfenv().print
local saved = fn
saved = saved("first")
print(saved)
