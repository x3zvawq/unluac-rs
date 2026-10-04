-- regress_283_nested_table_candidate: block早停不能跳过后序遍历发现的嵌套构造器
-- 原构造器预留字段容量；本例验证嵌套候选遍历，不要求改变空表的原始分配。
-- unluac: expect-contains [[return { answer =]]
-- unluac: expect-not-contains [[unluac error]]
-- 返回构造器直接位于条件路径中，不遗留 result 或调用准备中转。
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[table-constructor]] [[1]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=1]]
-- unluac: expect-ast-max [[local-binding]] [[2]] [[@proto=0]]
local function build(enabled, value)
    if enabled then
        local result = { answer = value }
        return result
    end
end

local result = build(true, 42)
assert(result.answer == 42 and build(false, 42) == nil)
-- 未进入分支返回零个值；false 字段不能误作缺失字段，0 仍为真值。
assert(select("#", build(false, 42)) == 0)
assert(select("#", build(nil, 42)) == 0)
assert(build(0, false).answer == false)
assert(next(build(true, nil)) == nil)
assert(select("#", build(true, nil)) == 1)
print("regress_283_nested_table_candidate", result.answer)
