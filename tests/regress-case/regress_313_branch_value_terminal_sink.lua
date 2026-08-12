-- regress_313_branch_value_terminal_sink#1: branch value 新暴露的终结 temp 应在 locals 前收回
-- unluac: expect-contains [[    return ]]
-- unluac: expect-not-contains [[    local ]]
-- unluac: expect-not-contains [[ = assert]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
local anchor = {}
local function is_anchor(value)
    return value == anchor
end

assert(is_anchor(anchor))
assert(not is_anchor({}))
print("regress_313_branch_value_terminal_sink#1", "OK")
