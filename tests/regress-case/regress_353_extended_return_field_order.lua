-- regress_353_extended_return_field_order: a field lookup may not move behind a return-prefix event
-- unluac: expect-contains [[local r5_0 =]]
-- unluac: expect-contains [[local r5_1 =]]
local trace = ""

local source = setmetatable({}, {
    __index = function()
        trace = trace .. "l"
        return 49
    end,
})

local function make_outer()
    trace = trace .. "o"
    return function(value)
        return value
    end
end

local function observe()
    trace = trace .. "p"
    return trace
end

local function unsafe(value)
    trace = ""
    local first = source.value
    local outer = make_outer()
    return observe(), first, outer(value)
end

local prefix, first, value = unsafe(50)
assert(prefix == "lop" and first == 49 and value == 50 and trace == "lop")
