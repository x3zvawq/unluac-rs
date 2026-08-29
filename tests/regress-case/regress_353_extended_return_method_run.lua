-- regress_353_extended_return_method_run: a method producer stays scalar in a non-final return slot
-- unluac: expect-not-contains [[local r4_0 =]]
-- unluac: expect-not-contains [[local r4_1 =]]
local provider = {}

function provider:get(value)
    return value
end

local function make_outer()
    return function(value)
        return value
    end
end

local function safe(value)
    local first = provider:get(value)
    local outer = make_outer()
    return first, outer(value)
end

local first, value = safe(46)
assert(first == 46 and value == 46)
