-- regress_429_constructor_nil_local_prefix: an independent nil local does not justify changing
-- empty-table preallocation; a field that reads the local must also remain after its declaration.
-- unluac: expect-order [[local r1_0 = {}]] [[r1_0.value = 7]]
-- unluac: expect-order [[local r2_1 = nil]] [[r2_0.value = r2_1]]

-- 两条路径都只需要原表和 later 声明。
-- unluac: expect-ast-max [[local-binding]] [[2]] [[@proto=1]]
-- unluac: expect-ast-max [[local-binding]] [[2]] [[@proto=2]]
-- unluac: expect-ast-count [[table-constructor]] [[2]]
-- unluac: expect-ast-count [[function]] [[2]]
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
local skipped, skipped_later = fold_independent(false)
assert(skipped.value == 7 and skipped_later == nil)
assert(select("#", fold_independent(nil)) == 2)
local dependent_skipped, dependent_later = preserve_dependency(nil)
assert(dependent_skipped.value == nil and dependent_later == nil)
assert(select("#", preserve_dependency(false)) == 2)
print("regress_429_constructor_nil_local_prefix", folded_later, preserved_later)
