-- unluac: expect-contains [[return p1_0 and (]]
-- unluac: expect-not-contains [[if p1_0 then]]

local function choose(a, b, c, d, e, f)
    return ((a and b) or (a and c)) and d and e and f
end

local result = choose(true, false, true, 4, 5, 6)
assert(result == 6)
print("regress_426_decision_environment_partition", result)
