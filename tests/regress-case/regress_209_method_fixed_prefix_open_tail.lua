-- regress_209_method_fixed_prefix_open_tail#1: fixed args stay before the method open tail
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
local function multi(value)
    return value, value + 1
end

local object = {}

function object:method(...)
    return ...
end

print("regress_209_method_fixed_prefix_open_tail#1", object:method(1, multi(2)))
