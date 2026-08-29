-- regress_362_constructor_call_capture: constructor-call folding must retain locals captured by an inlined field closure
-- unluac: expect-contains [[return (function(]]
local function build()
    local callee = function(table_value, value)
        return table_value.get()
    end
    local table_value = {}
    local value = 7
    table_value.get = function()
        return value
    end
    return callee(table_value, value)
end

assert(build() == 7)

local function build_safe(anchor)
    local callee = function(table_value)
        return table_value.get()
    end
    local table_value = {}
    table_value.get = function()
        return anchor
    end
    return callee(table_value)
end

assert(build_safe(11) == 11)
