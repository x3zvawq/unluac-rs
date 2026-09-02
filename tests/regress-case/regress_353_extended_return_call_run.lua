-- regress_353_extended_return_call_run: a non-tail dynamic callee keeps the complete preparation run
-- unluac: expect-contains [[local r4_0 =]]
-- unluac: expect-contains [[local r4_1 =]]
local function make_value(value)
    return value
end

local function make_outer()
    return function(value)
        return value
    end
end

local function safe(value)
    local first = make_value(value)
    local outer = make_outer()
    return first, outer(value)
end

local first, value = safe(41)
assert(first == 41 and value == 41)
