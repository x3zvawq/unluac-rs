-- regress_401_constructor_value_arity: a scalar call initializer stays scalar as the final argument
-- unluac: expect-not-contains [[.call_marker = function]]
-- unluac: expect-not-contains [[.if_marker = function]]
-- unluac: expect-not-contains [[.numeric_marker = function]]
-- unluac: expect-not-contains [[.iterator_marker = function]]

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

local function triple()
    return 11, 22, 33
end

local function build_open_tail()
    local tbl = { triple() }
    tbl.get = function()
        return "top"
    end
    return #tbl, tbl[1], tbl[2], tbl[3], tbl.get()
end

local top_count, top_first, top_second, top_third, top_marker = build_open_tail()
assert(top_count == 3, top_count)
assert(top_first == 11 and top_second == 22 and top_third == 33)
assert(top_marker == "top", top_marker)

local function inspect_nested(outer)
    return #outer, outer[1], outer[2], outer[3], outer.extra.get()
end

local function build_nested_open_tail()
    local callee = inspect_nested
    local outer = { triple() }
    local inner = {}
    inner.get = function()
        return "nested"
    end
    outer.extra = inner
    return callee(outer)
end

local nested_count, nested_first, nested_second, nested_third, nested_marker =
    build_nested_open_tail()
assert(nested_count == 3, nested_count)
assert(nested_first == 11 and nested_second == 22 and nested_third == 33)
assert(nested_marker == "nested", nested_marker)

local function consume_call_stmt(tbl)
    assert(tbl.call_marker() == "call")
end

local function build_call_stmt()
    local callee = consume_call_stmt
    local tbl = {}
    tbl.call_marker = function()
        return "call"
    end
    callee(tbl)
end
build_call_stmt()

local function consume_if(tbl)
    return tbl.if_marker() == "if"
end

local function build_if()
    local callee = consume_if
    local tbl = {}
    tbl.if_marker = function()
        return "if"
    end
    if callee(tbl) then
        return true
    end
    return false
end
assert(build_if())

local function consume_numeric(tbl)
    return tbl.numeric_marker()
end

local function build_numeric()
    local callee = consume_numeric
    local tbl = {}
    tbl.numeric_marker = function()
        return 1
    end
    for value = callee(tbl), 1 do
        return value
    end
end
assert(build_numeric() == 1)

local function consume_iterator(tbl)
    local emitted = false
    return function()
        if emitted then
            return
        end
        emitted = true
        return tbl.iterator_marker()
    end
end

local function build_iterator()
    local callee = consume_iterator
    local tbl = {}
    tbl.iterator_marker = function()
        return "iterator"
    end
    for value in callee(tbl) do
        return value
    end
end
assert(build_iterator() == "iterator")

print(
    "regress_401_constructor_value_arity",
    count,
    value,
    marker,
    top_count,
    nested_count
)
