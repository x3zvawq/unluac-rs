-- DUPTABLE initializes one table; dynamic entries use VM zero placeholders, not nil.
-- unluac: expect-ast-min [[table-record-field]] [[20]]
local function constants(unused)
    return { first = 1, second = 2, third = 3, fourth = 4, missing = nil, enabled = false }
end
local fixed = constants(false)
assert(fixed.first == 1 and fixed.fourth == 4 and fixed.missing == nil and fixed.enabled == false)

local function dynamic(first, second)
    return { first = first, second = second }
end
local supplied = dynamic(false, 7)
assert(supplied.first == false and supplied.second == 7)

local events = {}
local function observe(value)
    events[#events + 1] = value
    return value
end
local function mixed(value)
    return {
        first = 1,
        missing = nil,
        supplied = value,
        before = observe("before"),
        after = observe("after"),
        last = 6,
    }
end
local result = mixed(false)
assert(result.first == 1 and result.missing == nil and result.supplied == false and result.last == 6)
assert(result.before == "before" and result.after == "after")
assert(#events == 2 and events[1] == "before" and events[2] == "after")
result.missing = 5
assert(result.missing == 5)

local function grow(value)
    local result = { a = 1, b = nil, c = value, d = 4 }
    result.e = 5
    return result
end
for key, value in pairs(grow(7)) do
    print("template-growth", key, value)
end
local function grow_functions(value)
    local result = { a = 1, b = nil, c = value, d = 4 }
    result.d = function() return 4 end
    result.e = function() return 5 end
    return result
end
local methods = grow_functions(7)
assert(methods.d() == 4 and methods.e() == 5)
for key in pairs(methods) do
    print("template-function-growth", key)
end
print("regress_513_luau_table_template", fixed.second, fixed.third, supplied.second, table.concat(events, ","))
