-- regress_352_multi_return_call_run_accept: stable multi-return prefixes allow the complete callee run to collapse
-- unluac: expect-contains [[return "stable",]]
-- unluac: expect-not-contains [[local r5_0 =]]
-- unluac: expect-not-contains [[local r5_1 =]]
local function make_outer()
    return function(value)
        return value
    end
end

local function make_inner()
    return function(value)
        return value
    end
end

local function safe(value)
    local outer = make_outer()
    local inner = make_inner()
    return "stable", outer(inner(value), value)
end

local prefix, value = safe(42)
assert(prefix == "stable" and value == 42)
