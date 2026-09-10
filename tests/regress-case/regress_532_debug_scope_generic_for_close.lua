-- 第四返回值的隐式关闭由原生 for 持有，外层 do 只能恢复自己的根结束点。
local function iterator(values, weak, events)
    local guard = setmetatable({}, {
        __close = function()
            events.closed = events.closed + 1
        end,
    })
    weak[guard] = true
    return next, values, nil, guard
end

local function run(values)
    local weak = setmetatable({}, { __mode = "k" })
    local events = { closed = 0 }
    do
        local scoped = {}
        weak[scoped] = true
        scoped.field = 0
        for _, value in iterator(values, weak, events) do
            assert(events.closed == 0, "generic guard closed before body")
            scoped.field = value
        end
        assert(events.closed == 1, "generic guard must close before following code")
        local function use(value) assert(value.field == #values) end
        use(scoped)
    end
    collectgarbage("collect")
    assert(next(weak) == nil, "generic scope retained object or closed guard")
    assert(events.closed == 1, "generic guard closed twice")
end

run({})
run({1, 2, 3})
print("regress_532_debug_scope_generic_for_close", "closed")
