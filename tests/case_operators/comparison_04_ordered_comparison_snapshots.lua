-- >/>= 保持左读取、右调用和 VM 反向关系的元方法参数，不用补集替换有序关系。
-- unluac: expect-ast-count [[function]] [[9]]
-- unluac: expect-ast-count [[if]] [[3]]
-- unluac: expect-ast-max [[local-binding]] [[15]]
local events = {}
local old = getmetatable(_G)
local nan_mode = false
local reversed_arguments = true
local numeric_left, numeric_right = 0 / 0, 1
local lt_result, le_result = true, false
local mt = {
    __lt = function(a, b)
        assert(a.side == (reversed_arguments and "right" or "left"))
        assert(b.side == (reversed_arguments and "left" or "right"))
        events[#events + 1] = "lt"
        return lt_result
    end,
    __le = function(a, b)
        assert(a.side == (reversed_arguments and "right" or "left"))
        assert(b.side == (reversed_arguments and "left" or "right"))
        events[#events + 1] = "le"
        return le_result
    end,
}
setmetatable(_G, {__index = function(_, key)
    if key == "ordered_comparison_left" then
        events[#events + 1] = "left"
        if nan_mode then return numeric_left end
        return setmetatable({side = "left"}, mt)
    end
end})
local function right()
    events[#events + 1] = "right"
    if nan_mode then return numeric_right end
    return setmetatable({side = "right"}, mt)
end
local function greater()
    return ordered_comparison_left > right()
end
local function greater_equal()
    return ordered_comparison_left >= right()
end
local function not_greater()
    return not (ordered_comparison_left > right())
end
local function less()
    return ordered_comparison_left < right()
end
local function less_equal()
    return ordered_comparison_left <= right()
end
assert(greater())
assert(not greater_equal())
assert(not not_greater())
assert(table.concat(events, ",") == "left,right,lt,left,right,le,left,right,lt")
events = {}
reversed_arguments = false
assert(less())
assert(not less_equal())
assert(table.concat(events, ",") == "left,right,lt,left,right,le")
events = {}
nan_mode = true
assert(not greater())
assert(not greater_equal())
assert(not_greater())
assert(table.concat(events, ",") == "left,right,left,right,left,right")

-- NaN 换到右侧，以及相等/递增的普通值，仍须先取左快照再调用 right。
events = {}
numeric_left, numeric_right = 1, 0 / 0
assert(greater() == false and greater_equal() == false and not_greater() == true)
assert(less() == false and less_equal() == false)
assert(table.concat(events, ",") == "left,right,left,right,left,right,left,right,left,right")
events = {}
numeric_right = 1
assert(greater() == false and greater_equal() == true and not_greater() == true)
assert(less() == false and less_equal() == true)
assert(table.concat(events, ",") == "left,right,left,right,left,right,left,right,left,right")
events = {}
numeric_right = 2
assert(greater() == false and greater_equal() == false and not_greater() == true)
assert(less() == true and less_equal() == true)
assert(table.concat(events, ",") == "left,right,left,right,left,right,left,right,left,right")

nan_mode = false
reversed_arguments = true
lt_result, le_result = false, 0
events = {}
assert(greater() == false and greater_equal() == true and not_greater() == true)
assert(table.concat(events, ",") == "left,right,lt,left,right,le,left,right,lt")
reversed_arguments = false
lt_result, le_result = "", nil
events = {}
assert(less() == true and less_equal() == false)
assert(table.concat(events, ",") == "left,right,lt,left,right,le")
events = {}
reversed_arguments = true
assert(select("#", greater()) == 1)
assert(select("#", greater_equal()) == 1)
assert(select("#", not_greater()) == 1)
reversed_arguments = false
assert(select("#", less()) == 1)
assert(select("#", less_equal()) == 1)
assert(table.concat(events, ",") == "left,right,lt,left,right,le,left,right,lt,left,right,lt,left,right,le")
setmetatable(_G, old)
assert(getmetatable(_G) == old)
print("ordered-comparison-snapshots-ok")
