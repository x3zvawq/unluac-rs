-- unluac: expect-ast-count [[function]] [[1]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[assign]] [[0]]
-- unluac: expect-ast-max [[local-binding]] [[3]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=0]]
-- unluac: expect-contains [[(-0]]
local function preserve_positive_zero(x)
    local subject = x and 0.0
    if subject then
        return (x == 0.0) and 0.0
    end
    return x
end

local result = preserve_positive_zero(-0.0)
assert(result == 0.0)
assert(1 / result == math.huge)
assert(1 / preserve_positive_zero(0.0) == math.huge)
assert(preserve_positive_zero(false) == false and preserve_positive_zero(nil) == nil)
assert(preserve_positive_zero(1) == false and preserve_positive_zero(true) == false)
assert(preserve_positive_zero("") == false)
assert(select("#", preserve_positive_zero(nil)) == 1)
print("regress_427_decision_signed_zero_identity", 1 / result)
