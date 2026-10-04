-- regress_430_constructor_eventless_assignment_prefix: an eventless captured-local write does
-- not justify changing empty-table preallocation; a dependent field cannot cross the write.
-- unluac: expect-order [[local r1_2 = {}]] [[r1_2.answer = 7]]
-- unluac: expect-order [[local r3_2 = {}]] [[r3_0 = "new"]]
-- unluac: expect-order [[r3_0 = "new"]] [[r3_2.answer = r3_0]]

-- 捕获读取保留独立 closure，不为建表或读取制造中转 local。
-- unluac: expect-ast-max [[local-binding]] [[3]] [[@proto=1]]
-- unluac: expect-ast-max [[local-binding]] [[3]] [[@proto=3]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=4]]
-- unluac: expect-ast-count [[function]] [[4]]
-- unluac: expect-ast-count [[table-constructor]] [[2]]
local function fold_independent()
    local value
    local function read()
        return value
    end
    local result = {}
    value = "new"
    result.answer = 7
    return result, read()
end

local folded, folded_value = fold_independent()
assert(folded.answer == 7)
assert(folded_value == "new")

local function preserve_dependency()
    local value
    local function read()
        return value
    end
    local result = {}
    value = "new"
    result.answer = value
    return result, read()
end

local preserved, preserved_value = preserve_dependency()
assert(preserved.answer == "new")
assert(preserved_value == "new")
assert(select("#", fold_independent()) == 2)
assert(select("#", preserve_dependency()) == 2)
print("regress_430_constructor_eventless_assignment_prefix", folded_value, preserved_value)
