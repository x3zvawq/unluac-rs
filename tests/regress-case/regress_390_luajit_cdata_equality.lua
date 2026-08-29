local ffi = require("ffi")

ffi.cdef[[
typedef struct {
    int value;
} regress_390_value;
]]

local equality_hits = 0
local value_type = ffi.metatype("regress_390_value", {
    __eq = function()
        equality_hits = equality_hits + 1
        return true
    end,
})

local function compare_with_nil(value)
    local unused = value == nil
    if 1 == 1 then
        return equality_hits
    else
        return unused
    end
end

assert(compare_with_nil(value_type(1)) == 1)
