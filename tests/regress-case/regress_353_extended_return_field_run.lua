-- regress_353_extended_return_field_run: a non-tail dynamic callee keeps the complete preparation run
-- unluac: expect-contains [[local r3_0 =]]
-- unluac: expect-contains [[local r3_1 =]]
local holder = { nested = { value = 47 } }

local function make_outer()
    return function(value)
        return value
    end
end

local function safe(value)
    local first = holder.nested.value
    local outer = make_outer()
    return first, outer(value)
end

local first, value = safe(48)
assert(first == 47 and value == 48)
