-- 非尾调用保留可观察的 callee 根；无观察的纯闭包不要求固定数量或名字的临时变量。
-- unluac: expect-contains [[return "stable",]]
local function make_outer()
    return function(value)
        return value
    end
end

local function make_inner()
    return function(value)
        return value
    end
end

local function safe(value)
    local outer = make_outer()
    local inner = make_inner()
    return "stable", outer(inner(value), value)
end

local prefix, value = safe(42)
assert(prefix == "stable" and value == 42)

local weak = setmetatable({}, {__mode = "v"})
local function make_observer()
    return function(result)
        collectgarbage("collect")
        collectgarbage("collect")
        assert(type(weak.inner) == "function")
        return result
    end
end
local function make_observed_inner()
    local marker = {value = 1}
    local inner = function(result)
        return result + marker.value - 1
    end
    weak.inner = inner
    return inner
end
local function held(result)
    local outer = make_observer()
    local inner = make_observed_inner()
    return "held", outer(inner(result), result)
end
local function statement(result)
    local outer = make_observer()
    local inner = make_observed_inner()
    assert(outer(inner(result), result) == 42)
end
collectgarbage("stop")
local held_prefix, held_value = held(42)
assert(held_prefix == "held" and held_value == 42)
statement(42)
collectgarbage("restart")
