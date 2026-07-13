-- regress_141_lua51_vararg_fixed_results#1: OP_VARARG B encodes fixed result count as B - 1
-- unluac: expect-not-contains [[unluac error]]
local function fixed_vararg(...)
    local first, untouched = 0, 41
    first = ...
    return first, untouched
end

print("regress_141_lua51_vararg_fixed_results#1", fixed_vararg(7, 8))
