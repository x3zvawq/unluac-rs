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

print("regress_283_nested_table_candidate", build(true, 42).answer)
