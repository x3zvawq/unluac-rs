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
print("regress_427_decision_signed_zero_identity", 1 / result)
