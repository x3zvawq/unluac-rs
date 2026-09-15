-- regress_209_method_fixed_prefix_open_tail#1: fixed args stay before the method open tail
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-contains [[:method(]]
-- unluac: expect-not-contains [[.method(]]
local function multi(value)
    return value, value + 1
end

local object = {}

function object:method(...)
    return ...
end

local first, second, third = object:method(1, multi(2))
assert(first == 1 and second == 2 and third == 3)
print("regress_209_method_fixed_prefix_open_tail#1", first, second, third)
