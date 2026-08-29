-- unluac: expect-contains [[ == nil]]

local ffi = require("ffi")

ffi.cdef[[
typedef struct {
    int value;
} regress_391_value;
]]

local equality_hits = 0
local value_type = ffi.metatype("regress_391_value", {
    __eq = function()
        equality_hits = equality_hits + 1
        return true
    end,
})

local function observe_equality(value)
    if value == nil then
        return equality_hits
    else
        return equality_hits
    end
end

assert(observe_equality(value_type(1)) == 1)

local function observe_twice(value)
    local result = (value == nil) and (value == nil)
    return result, equality_hits
end

equality_hits = 0
local result, hits = observe_twice(value_type(1))
assert(result and hits == 2)
