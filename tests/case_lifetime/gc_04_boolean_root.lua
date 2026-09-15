-- CALL 和最终 Boolean 同槽，不代表中间 LEN 也覆写同一个根。
-- cdata __eq 对 false/nil 仍可返回 true；观察自身必须避开该重载。
local ffi = require("ffi")
ffi.cdef[[typedef struct { int tag; } cdata_boolean_root_578;]]
local weak = setmetatable({}, {__mode = "v"})
local first_seen, length_seen, final_seen
local function observe()
    collectgarbage("collect")
    collectgarbage("collect")
    return type(weak[1]) == "cdata"
end
local value
value = ffi.metatype("cdata_boolean_root_578", {
    __eq = function(left, right)
        if left.tag == 1 then
            first_seen = observe()
            return true
        end
        final_seen = observe()
        return true
    end,
    __len = function()
        length_seen = observe()
        return value(2)
    end,
})
local function make()
    local item = value(1)
    weak[1] = item
    return item
end
local function named(owner)
    local item = make()
    item = item == false and #owner == 0
    return item
end
local function inline(owner)
    return make() == false and #owner == 0
end
local function staged(owner)
    local item = make()
    if item == false then
        item = #owner
        item = item == 0
    else
        item = false
    end
    return item
end
collectgarbage("stop")
assert(named(value(0)))
assert(first_seen and length_seen and final_seen)
print("named", first_seen, length_seen, final_seen)
assert(inline(value(0)))
assert(first_seen and length_seen and not final_seen)
print("inline", first_seen, length_seen, final_seen)
assert(staged(value(0)))
assert(first_seen and length_seen and not final_seen)
print("staged", first_seen, length_seen, final_seen)
collectgarbage("restart")
