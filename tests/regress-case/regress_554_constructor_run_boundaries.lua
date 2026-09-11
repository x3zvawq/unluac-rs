-- Constructor run facts must preserve non-call returns and later callee starts.
local function objects()
    local a = { read = function() return 1 end }
    local b = { read = function() return 2 end }
    local c = { read = function() return 3 end }
    local d = { read = function() return 4 end }
    local e = { read = function() return 5 end }
    local f = { read = function() return 6 end }
    local g = { read = function() return 7 end }
    local h = { read = function() return 8 end }
    return a, b, c, d, e, f, g, h
end

function __reg554_collect(...)
    local total = 0
    for i = 1, select("#", ...) do
        total = total + select(i, ...).read()
    end
    return total
end

local function later_callee()
    local prefix = { read = function() return 17 end }
    local callee = __reg554_collect
    local a = { read = function() return 3 end }
    local b = { read = function() return 5 end }
    return callee(a, b), prefix.read()
end

assert(__reg554_collect(objects()) == 36)
local result, prefix = later_callee()
assert(result == 8 and prefix == 17)
print("regress_554_constructor_run_boundaries", result, prefix)
