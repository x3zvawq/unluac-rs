-- Non-nil result facts may recover array fields; possible nil must preserve allocation holes.
local function build(flag, left, right)
    local result = {}
    result[1] = not flag
    result[2] = left < right
    result[3] = flag or false
    return result
end

for _, flag in ipairs({ true, false }) do
    local result = build(flag, 2, 3)
    assert(result[1] == not flag and result[2] == true and result[3] == flag)
    print("non-nil-array", #result, result[1], result[2], result[3])
end

local comparisons = 0
local operand = setmetatable({}, {
    __lt = function()
        comparisons = comparisons + 1
        return false
    end,
})
local result = build(nil, operand, operand)
assert(result[1] == true and result[2] == false and result[3] == false)
assert(comparisons == 1)

local function hole(flag)
    local result = {}
    result[1] = flag and false
    result[2] = true
    return result
end
local absent = hole(nil)
local present = hole(false)
assert(absent[1] == nil and absent[2] == true)
assert(present[1] == false and present[2] == true)
print("possible-nil-array", #absent, #present)

local function dense()
    local result = {}
    result[1] = false
    result[2] = true
    return result
end
local cleared = dense()
cleared[1] = nil
assert(cleared[2] == true)
print("cleared-non-nil-array", #cleared)

-- The caller can observe allocation history even when every initial value is non-nil.
local function three_slots()
    local result = {}
    result[1] = false
    result[2] = true
    result[3] = false
    return result
end
local middle = three_slots()
middle[1] = nil
middle[3] = nil
assert(middle[2] == true)
print("cleared-three-slot-array", #middle)

local function array_with_method()
    local result = { false, true, false }
    result.read = function() return 7 end
    return result
end
local method_owner = array_with_method()
method_owner[1] = nil
method_owner[3] = nil
assert(method_owner[2] == true and method_owner.read() == 7)
print("cleared-array-with-method", #method_owner)

local function numeric_records(first, center, last)
    return { [1] = first, [2] = center, [3] = last }
end
local records = numeric_records(false, true, false)
records[1] = nil
records[3] = nil
assert(records[2] == true)
print("cleared-numeric-records", #records)

local function mixed_batch(tail)
    return { 1, label = 4, 2, tail() }
end
local mixed = mixed_batch(function() return 3, 4 end)
assert(mixed[1] == 1 and mixed[2] == 2 and mixed[3] == 3 and mixed[4] == 4)
assert(mixed.label == 4)
print("mixed-original-batch", #mixed)
print("regress_512_table_result_nil_shape", comparisons)

-- Multiple local targets reserve a common array buffer before either RHS is evaluated.
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@dialect=luau]] [[@proto=11]]
-- unluac: expect-ast-count [[table-constructor]] [[2]] [[@dialect=luau]] [[@proto=11]]
-- unluac: expect-ast-count [[call]] [[2]] [[@dialect=luau]] [[@proto=11]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@dialect=luau]] [[@proto=12]]
-- unluac: expect-ast-count [[table-constructor]] [[5]] [[@dialect=luau]] [[@proto=12]]
-- unluac: expect-ast-count [[call]] [[2]] [[@dialect=luau]] [[@proto=12]]
local function grouped_open(first, second)
    local left, right = { first() }, { second() }
    return left, right
end

local function grouped_mixed(first, second)
    local left, middle, right = { first() }, { tag = "grouped", nested = { "inside", false }, empty = {} }, { 0, second() }
    return left, middle, right
end

do
    local order = ""
    local function first()
        order = order .. "first;"
        return "head", nil, "tail"
    end
    local function second()
        order = order .. "second;"
        return nil, "last"
    end
    local left, right = grouped_open(first, second)
    assert(order == "first;second;")
    assert(left[1] == "head" and left[2] == nil and left[3] == "tail" and left[4] == nil)
    assert(right[1] == nil and right[2] == "last" and right[3] == nil)
    order = ""
    local mixed_left, middle, mixed_right = grouped_mixed(first, second)
    assert(order == "first;second;")
    assert(mixed_left[1] == "head" and mixed_left[2] == nil and mixed_left[3] == "tail")
    assert(middle.tag == "grouped" and type(middle.nested) == "table")
    assert(middle.nested[1] == "inside" and middle.nested[2] == false and middle.nested[3] == nil)
    assert(type(middle.empty) == "table" and next(middle.empty) == nil)
    assert(mixed_right[1] == 0 and mixed_right[2] == nil and mixed_right[3] == "last")
    local function empty()
        order = order .. "empty;"
    end
    order = ""
    local empty_left, empty_right = grouped_open(empty, empty)
    assert(order == "empty;empty;" and next(empty_left) == nil and next(empty_right) == nil)
    print("grouped-open-tables", left[1], left[3], right[2], mixed_right[3], order)
end
