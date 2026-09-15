-- regress_283_nested_table_candidate: block早停不能跳过后序遍历发现的嵌套构造器
-- 原构造器预留字段容量；本例验证嵌套候选遍历，不要求改变空表的原始分配。
-- unluac: expect-contains [[return { answer =]]
-- unluac: expect-not-contains [[unluac error]]
local function build(enabled, value)
    if enabled then
        local result = { answer = value }
        return result
    end
end

local result = build(true, 42)
assert(result.answer == 42 and build(false, 42) == nil)
print("regress_283_nested_table_candidate", result.answer)
