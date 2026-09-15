-- regress_430_constructor_eventless_assignment_prefix: an eventless captured-local write does
-- not justify changing empty-table preallocation; a dependent field cannot cross the write.
-- unluac: expect-order [[local r1_2 = {}]] [[r1_2.answer = 7]]
-- unluac: expect-order [[local r3_2 = {}]] [[r3_0 = "new"]]
-- unluac: expect-order [[r3_0 = "new"]] [[r3_2.answer = r3_0]]

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
print("regress_430_constructor_eventless_assignment_prefix", folded_value, preserved_value)
