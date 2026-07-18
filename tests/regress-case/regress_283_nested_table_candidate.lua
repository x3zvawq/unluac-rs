-- regress_283_nested_table_candidate: block早停不能跳过后序遍历发现的嵌套构造器
-- unluac: expect-contains [[return { answer = 42 }]]
-- unluac: expect-not-contains [[unluac error]]
local function build(enabled)
    if enabled then
        local result = {}
        result.answer = 42
        return result
    end
end

print("regress_283_nested_table_candidate", build(true).answer)
