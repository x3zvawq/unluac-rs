-- regress_430_constructor_eventless_assignment_prefix: an eventless captured-local write does
-- not justify changing empty-table preallocation; a dependent field cannot cross the write.

-- 捕获读取保留独立 closure，不为建表或读取制造中转 local。
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
