-- regress_354_adjacent_final_arg_value_arity: a call moved from a local initializer into the final argument remains single-valued
-- unluac: expect-contains [[((p]]

local function pair()
    return 7, 99
end

local function wrap(...)
    local argc = select("#", ...)
    local value = ...
    return function()
        return value, argc
    end
end

local function adjacent(pair_fn, wrap_fn, mark_fn)
    mark_fn()
    local seed = pair_fn()
    return wrap_fn(seed)
end

local callee = adjacent(pair, wrap, function() end)
local value, argc = callee()
assert(value == 7 and argc == 1)
print("regress_354_adjacent_final_arg_value_arity")
