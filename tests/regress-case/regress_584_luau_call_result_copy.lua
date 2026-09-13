-- 活动低槽赋值必须重发 callee scratch 与 CALL 结果回写；独立提升 scratch 会逐轮增长。
local fn = getfenv().print
local saved = fn
saved = saved("first")
print(saved)
