-- regress_401_constructor_value_arity: a scalar call initializer stays scalar as the final argument

local function pair()
    return 7, 99
end

local function consume(t, ...)
    return select("#", ...), (...), t.get()
end

local function build()
    local callee = consume
    local tbl = {}
    local value = pair()
    tbl.get = function()
        return 1
    end
    return callee(tbl, value)
end

local count, value, marker = build()
assert(count == 1, count)
assert(value == 7, value)
assert(marker == 1, marker)
print("regress_401_constructor_value_arity", count, value, marker)
