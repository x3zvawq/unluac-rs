-- >/>= 保持左读取、右调用和 VM 反向关系的元方法参数，不用补集替换有序关系。
local events = {}
local old = getmetatable(_G)
local nan_mode = false
local reversed_arguments = true
local mt = {
    __lt = function(a, b)
        assert(a.side == (reversed_arguments and "right" or "left"))
        assert(b.side == (reversed_arguments and "left" or "right"))
        events[#events + 1] = "lt"
        return true
    end,
    __le = function(a, b)
        assert(a.side == (reversed_arguments and "right" or "left"))
        assert(b.side == (reversed_arguments and "left" or "right"))
        events[#events + 1] = "le"
        return false
    end,
}
setmetatable(_G, {__index = function(_, key)
    if key == "ordered_comparison_left" then
        events[#events + 1] = "left"
        if nan_mode then return 0 / 0 end
        return setmetatable({side = "left"}, mt)
    end
end})
local function right()
    events[#events + 1] = "right"
    if nan_mode then return 1 end
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
setmetatable(_G, old)
print("ordered-comparison-snapshots-ok")
