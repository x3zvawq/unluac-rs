-- regress_429_constructor_nil_local_prefix: an independent nil local may stay between a
-- constructor seed and a folded field, but a field that reads the local must remain after it.
-- unluac: expect-contains [[local r1_0 = { value = 7 }]]
-- unluac: expect-not-contains [[r1_0.value = 7]]
-- unluac: expect-order [[local r2_1 = nil]] [[r2_0.value = r2_1]]

local function fold_independent(flag)
    local result = {}
    local later
    result.value = 7
    while flag do
        later = "used"
        break
    end
    return result, later
end

local folded, folded_later = fold_independent(true)
assert(folded.value == 7)
assert(folded_later == "used")

local function preserve_dependency(flag)
    local result = {}
    local later
    result.value = later
    while flag do
        later = "used"
        break
    end
    return result, later
end

local preserved, preserved_later = preserve_dependency(true)
assert(preserved.value == nil)
assert(preserved_later == "used")
print("regress_429_constructor_nil_local_prefix", folded_later, preserved_later)
