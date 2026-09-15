-- 正常出口中的独立 inner Close 必须先于 observable，只有末端 outer Close 可由退出消费。
-- unluac: expect-ast-count [[close-binding]] [[5]]
-- unluac: expect-ast-min [[goto]] [[3]]
-- unluac: expect-ast-min [[label]] [[3]]
local function linear_tail()
    local log = {}
    local function resource(name)
        return setmetatable({}, { __close = function() log[#log + 1] = name end })
    end
    local function run()
        local n = 0
        ::again::
        do
            local outer <close> = resource("outer" .. n)
            do
                local inner <close> = resource("inner" .. n)
                if n == 0 then n = 1; goto again end
            end
            log[#log + 1] = "after-inner"
        end
    end
    run()
    local actual = table.concat(log, ",")
    assert(actual == "inner0,outer0,inner1,after-inner,outer1", actual)
    return actual
end

-- 正常出口的值选择仍在 outer 生命周期内，不能先把自然回边区物化为 break loop。
local function branching_tail()
    local log, closed = {}, {}
    local function resource(name)
        return setmetatable({}, { __close = function()
            closed[name] = true
            log[#log + 1] = name
        end })
    end
    local function run()
        local n = 0
        ::again::
        do
            local outer <close> = resource("outer" .. n)
            do
                local inner <close> = resource("inner" .. n)
                if n == 0 then n = 1; goto again end
            end
            assert(closed.inner1 and not closed.outer1)
            log[#log + 1] = "after-inner"
        end
    end
    run()
    local actual = table.concat(log, ",")
    assert(actual == "inner0,outer0,inner1,after-inner,outer1", actual)
    return actual
end

-- 内层只有 captured local；其 Close 没有 TBC origin，但外层资源仍须跨过该事件。
local function upvalue_tail()
    local log, snapshots = {}, {}
    local function resource(name)
        return setmetatable({}, { __close = function() log[#log + 1] = name end })
    end
    local function run()
        local n = 0
        ::again::
        do
            local outer <close> = resource("outer" .. n)
            do
                local snapshot = "snapshot" .. n
                snapshots[#snapshots + 1] = function() return snapshot end
                if n == 0 then n = 1; goto again end
            end
            log[#log + 1] = snapshots[2]()
        end
    end
    run()
    assert(snapshots[1]() == "snapshot0")
    assert(snapshots[2]() == "snapshot1")
    local actual = table.concat(log, ",")
    assert(actual == "outer0,snapshot1,outer1", actual)
    return actual
end

local linear_ok, linear_result = pcall(linear_tail)
local branching_ok, branching_result = pcall(branching_tail)
local upvalue_ok, upvalue_result = pcall(upvalue_tail)
assert(linear_ok, linear_result)
assert(branching_ok, branching_result)
assert(upvalue_ok, upvalue_result)
print(linear_result)
print(branching_result)
print(upvalue_result)
