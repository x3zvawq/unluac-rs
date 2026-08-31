-- regress_353_extended_return_call_run_order: a return prefix may not overtake call-run producers
-- unluac: expect-contains [[local r5_0 =]]
-- unluac: expect-contains [[local r5_1 =]]
local trace = ""

local function make_value(value)
    trace = trace .. "v"
    return value
end

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
    local first = make_value(value)
    local outer = make_outer()
    return observe(), first, outer(value)
end

local prefix, first, value = unsafe(42)
assert(prefix == "vop" and first == 42 and value == 42 and trace == "vop")
