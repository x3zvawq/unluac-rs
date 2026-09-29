-- unluac: expect-ast-count [[function]] [[1]]
-- unluac: expect-ast-max [[local-binding]] [[5]] [[@proto=0]]
-- unluac: expect-ast-max [[local-binding]] [[2]] [[@proto=1]]
-- unluac: expect-count [[ = 0]] [[1]]
-- unluac: expect-ast-count [[error]] [[0]]
-- regress_141_lua51_vararg_fixed_results#1: OP_VARARG B encodes fixed result count as B - 1
-- unluac: expect-not-contains [[unluac error]]
local function fixed_vararg(...)
    local first, untouched = 0, 41
    first = ...
    return first, untouched
end

local first, untouched = fixed_vararg(7, 8)
assert(first == 7 and untouched == 41)
local missing, still_untouched = fixed_vararg()
assert(missing == nil and still_untouched == 41)
assert(select("#", fixed_vararg(nil, 9)) == 2)
print("regress_141_lua51_vararg_fixed_results#1", first, untouched)
