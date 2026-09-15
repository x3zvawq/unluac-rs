-- regress_75_guard_bvm_priority#1: guard leaves own an equal-sized branch value candidate
-- unluac: expect-contains [[if p1_0 and p1_1 then]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]

local function select_value(a, b, touch)
    local value = "default"
    if a and b then
        touch()
        value = "selected"
    end
    return value
end

local touched = false
local result = select_value(true, false, function()
    touched = true
end)
assert(result == "default" and not touched)
print("regress_75_guard_bvm_priority#1", result)
