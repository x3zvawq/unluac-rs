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
