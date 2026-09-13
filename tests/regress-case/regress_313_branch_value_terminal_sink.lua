-- regress_313_branch_value_terminal_sink#1: branch value 新暴露的终结 temp 应在 locals 前收回
-- 约束目标子函数，外层 do 的正常声明也有缩进，不能据缩进禁止整个模块的 local。
-- unluac: expect-contains [[return p1_0 ==]]
-- unluac: expect-not-contains [[local r1_]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
local anchor = {}
local function is_anchor(value)
    return value == anchor
end

assert(is_anchor(anchor))
assert(not is_anchor({}))
print("regress_313_branch_value_terminal_sink#1", "OK")
