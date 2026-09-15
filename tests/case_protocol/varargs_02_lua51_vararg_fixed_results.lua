-- regress_141_lua51_vararg_fixed_results#1: OP_VARARG B encodes fixed result count as B - 1
-- unluac: expect-not-contains [[unluac error]]
local function fixed_vararg(...)
    local first, untouched = 0, 41
    first = ...
    return first, untouched
end

local first, untouched = fixed_vararg(7, 8)
assert(first == 7 and untouched == 41)
print("regress_141_lua51_vararg_fixed_results#1", first, untouched)
