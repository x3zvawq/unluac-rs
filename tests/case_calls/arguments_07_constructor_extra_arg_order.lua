-- regress_423_constructor_extra_arg_order: only extra args before a pending constructor handoff need an eventless proof
-- Allocation may keep the table argument explicit; suffix expansion and prefix ordering remain mandatory.
-- unluac: expect-contains [[, __reg423_suffix_values())]]
-- unluac: expect-order [["prefix-table"]] [[__reg423_mark("prefix-extra", 11)]]
-- unluac: expect-contains [[.read()]]
-- unluac: expect-contains [[return callee(value, __reg423_suffix_values())]] [[@debug=retained]]
-- unluac: expect-contains [[total = total + select(i, ...).read()]] [[@debug=retained]]
-- unluac: expect-not-contains [[= select]]
-- unluac: expect-contains [[lookup_events[#lookup_events + 1] = "add" .. right.value]] [[@debug=retained]]
-- unluac: expect-contains [[return left + right.value]] [[@debug=retained]]
-- unluac: expect-contains [[return setmetatable({ value = number }, {]] [[@debug=retained]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=5]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=9]] [[@dialect=lua5.4]]
-- Luau 循环头的 FASTCALL 和循环内的索引调用链共享原控制槽，只声明累加器。
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=9]] [[@dialect=luau]]

local events = {}

function __reg423_mark(label, value)
    events[#events + 1] = label
    return value
end

function __reg423_consume(value, ...)
    return value.read(), select("#", ...), ...
end

function __reg423_consume_prefix(extra, value)
    return extra, value.read()
end

function __reg423_suffix_values()
    __reg423_mark("suffix-extra", true)
    return 9, 10
end

local function suffix_case()
    local callee = __reg423_consume
    local value = { label = "suffix-table" }
    value.read = function()
        return 7
    end
    return callee(value, __reg423_suffix_values())
end

local suffix_value, suffix_count, suffix_first, suffix_second = suffix_case()
assert(suffix_value == 7 and suffix_count == 2 and suffix_first == 9 and suffix_second == 10)
assert(table.concat(events, ",") == "suffix-extra")

events = {}

local function prefix_case()
    local callee = __reg423_consume_prefix
    local value = { label = "prefix-table" }
    value.read = function()
        return 8
    end
    return callee(__reg423_mark("prefix-extra", 11), value)
end

local prefix_extra, prefix_value = prefix_case()
assert(prefix_extra == 11 and prefix_value == 8)
assert(table.concat(events, ",") == "prefix-extra")

-- Many participating locals retain declaration order through the complete handoff.
-- Each argument starts with its final table layout, so capacity checks do not prune it.
function __reg423_collect(...)
    local total = 0
    for i = 1, select("#", ...) do
        total = total + select(i, ...).read()
    end
    return total
end

local function wide_case()
    local callee = __reg423_collect
    local a = { read = function() return 1 end }
    local b = { read = function() return 2 end }
    local c = { read = function() return 3 end }
    local d = { read = function() return 4 end }
    local e = { read = function() return 5 end }
    local f = { read = function() return 6 end }
    local g = { read = function() return 7 end }
    local h = { read = function() return 8 end }
    return callee(a, b, c, d, e, f, g, h)
end

local function repeated_reversed_case()
    local callee = __reg423_collect
    local a = { read = function() return 3 end }
    local b = { read = function() return 5 end }
    return callee(b, a, b)
end

assert(wide_case() == 36)
assert(repeated_reversed_case() == 13)

-- 索引和返回的函数均可产生副作用；累计表达式仍须逐项完成 lookup、CALL、加法。
local lookup_events = {}
local function deferred(number)
    return setmetatable({}, { __index = function(_, key)
        assert(key == "read")
        lookup_events[#lookup_events + 1] = "lookup" .. number
        return function()
            lookup_events[#lookup_events + 1] = "call" .. number
            return setmetatable({ value = number }, { __add = function(left, right)
                lookup_events[#lookup_events + 1] = "add" .. right.value
                return left + right.value
            end })
        end
    end })
end
assert(__reg423_collect(deferred(2), deferred(5)) == 7)
assert(table.concat(lookup_events, ",") == "lookup2,call2,add2,lookup5,call5,add5")

print(
    "regress_423_constructor_extra_arg_order",
    suffix_value,
    suffix_count,
    suffix_first,
    suffix_second,
    prefix_extra,
    prefix_value
)
