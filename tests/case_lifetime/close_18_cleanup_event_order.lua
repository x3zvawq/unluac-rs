-- Resource exits must precede the observable events that follow their scopes.
-- unluac: expect-contains [[<close>]]
-- unluac: expect-ast-count [[close-binding]] [[15]]
-- unluac: expect-ast-count [[table-list-field]] [[23]] [[@proto=0]]

local function acquire(log, name)
    log[#log + 1] = "open:" .. name
    return setmetatable({ name = name }, {
        __close = function(value)
            log[#log + 1] = "close:" .. value.name
        end,
    })
end

local function expect_log(log, expected)
    local actual = table.concat(log, ",")
    assert(actual == expected, actual)
end

local function empty_scope()
    local log = {}
    do
        local resource <close> = acquire(log, "empty")
    end
    log[#log + 1] = "after"
    expect_log(log, "open:empty,close:empty,after")
end

local function nested_closes()
    local log = {}
    do
        local outer <close> = acquire(log, "outer")
        do
            local inner <close> = acquire(log, "inner")
        end
    end
    log[#log + 1] = "after"
    expect_log(log, "open:outer,open:inner,close:inner,close:outer,after")
end

local function return_after_close()
    local log = {}
    local function callee()
        assert(log[#log] == "close:return", table.concat(log, ","))
        log[#log + 1] = "callee"
        return 42
    end
    local function invoke()
        do
            local resource <close> = acquire(log, "return")
        end
        return callee()
    end
    assert(invoke() == 42)
    expect_log(log, "open:return,close:return,callee")
end

local function repeat_condition()
    local log = {}
    local count = 0
    local function done()
        assert(log[#log] == "close:repeat", table.concat(log, ","))
        log[#log + 1] = "until:" .. count
        return count == 2
    end
    repeat
        count = count + 1
        do
            local resource <close> = acquire(log, "repeat")
        end
    until done()
    expect_log(log, "open:repeat,close:repeat,until:1,open:repeat,close:repeat,until:2")
end

local function iterator_dispatch()
    local log = {}
    local function iterator(_, previous)
        if previous ~= 0 then
            assert(log[#log] == "close:item" .. previous, table.concat(log, ","))
        end
        local next_value = previous + 1
        log[#log + 1] = "iterator:" .. next_value
        if next_value <= 2 then
            return next_value
        end
    end
    for value in iterator, nil, 0 do
        local resource <close> = acquire(log, "item" .. value)
    end
    expect_log(log, "iterator:1,open:item1,close:item1,iterator:2,open:item2,close:item2,iterator:3")
end

local function shared_exit(take_goto)
    local log = {}
    local function callee()
        assert(log[#log] == "close:shared", table.concat(log, ","))
        log[#log + 1] = "callee"
        return 7
    end
    local function invoke()
        do
            local resource <close> = acquire(log, "shared")
            if take_goto then
                log[#log + 1] = "goto"
                goto after
            end
            log[#log + 1] = "normal"
        end
        ::after::
        return callee()
    end
    assert(invoke() == 7)
    local route = take_goto and "goto" or "normal"
    expect_log(log, "open:shared," .. route .. ",close:shared,callee")
end

local cases = {
    { "empty", empty_scope },
    { "nested", nested_closes },
    { "return", return_after_close },
    { "repeat", repeat_condition },
    { "iterator", iterator_dispatch },
    { "goto", function() shared_exit(true) end },
    { "normal", function() shared_exit(false) end },
}
local failures = {}
for _, case in ipairs(cases) do
    local ok, message = pcall(case[2])
    if not ok then
        failures[#failures + 1] = case[1] .. ": " .. tostring(message)
    end
    print("regress_481_cleanup_event_order", case[1], ok)
end
assert(#failures == 0, table.concat(failures, "\n"))

-- RETURN freezes result slots before closing upvalues and running TBC callbacks.
local function closer(action)
    return setmetatable({}, { __close = action })
end

local get_local
local function single_local()
    local x = 1
    get_local = function() return x end
    local r <close> = closer(function() x = 9 end)
    return x
end
assert(single_local() == 1 and get_local() == 9)
print("single_local", 1, get_local())

local box = { value = 2 }
local function table_value()
    local r <close> = closer(function() box.value = 9 end)
    return box.value
end
assert(table_value() == 2 and box.value == 9)
print("table_value", 2, box.value)

box.value = 2
local function table_identity()
    local r <close> = closer(function() box.value = 9 end)
    return box
end
assert(table_identity() == box and box.value == 9)
print("table_identity", box.value)

box.value = 2
local function multiple()
    local x = 1
    get_local = function() return x end
    local r <close> = closer(function() x = 9; box.value = 9 end)
    return x, nil, box.value, box
end
local result = table.pack(multiple())
assert(result.n == 4 and result[1] == 1 and result[2] == nil and result[3] == 2)
assert(result[4] == box and box.value == 9 and get_local() == 9)
print("multiple", result.n, result[1], result[2], result[3], result[4].value)

box.value = 2
local log = {}
local function call_results()
    local x = 1
    local function produce()
        log[#log + 1] = "call"
        return x, nil, box.value
    end
    local r <close> = closer(function()
        log[#log + 1] = "close"
        x = 9
        box.value = 9
    end)
    return produce()
end
result = table.pack(call_results())
assert(result.n == 3 and result[1] == 1 and result[2] == nil and result[3] == 2)
assert(table.concat(log, ",") == "call,close" and box.value == 9)
print("call_results", result.n, result[1], result[2], result[3], table.concat(log, ","))

local external = 1
local function external_upvalue()
    local r <close> = closer(function() external = 9 end)
    return external
end
assert(external_upvalue() == 1 and external == 9)
print("external_upvalue", 1, external)

local function explicit_scope()
    local x = 1
    do
        local r <close> = closer(function() x = 9 end)
    end
    return x
end
assert(explicit_scope() == 9)
print("explicit_scope", 9)

-- Equal returns stay equivalent after the pending cleanup transaction is consumed.
do
    local calls, closes = 0, 0
    local function ordinary(flag)
        if flag then return 42 else return 42 end
    end
    local function closed(predicate)
        local r <close> = closer(function() closes = closes + 1 end)
        if predicate() then return 42 else return 42 end
    end
    for _, flag in ipairs({ false, true }) do
        assert(ordinary(flag) == 42)
        assert(closed(function() calls = calls + 1; return flag end) == 42)
    end
    assert(calls == 2 and closes == 2)
    print("equal_returns", calls, closes)
end
