-- regress_423_constructor_extra_arg_order: only extra args before a pending constructor handoff need an eventless proof
-- Allocation may keep the table argument explicit; suffix expansion and prefix ordering remain mandatory.
-- unluac: expect-contains [[, __reg423_suffix_values())]]
-- unluac: expect-order [["prefix-table"]] [[__reg423_mark("prefix-extra", 11)]]
-- unluac: expect-contains [[.read = function]]

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

print(
    "regress_423_constructor_extra_arg_order",
    suffix_value,
    suffix_count,
    suffix_first,
    suffix_second,
    prefix_extra,
    prefix_value
)
