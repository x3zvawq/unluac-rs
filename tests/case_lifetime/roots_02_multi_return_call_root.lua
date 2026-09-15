-- 非尾调用保留可观察的 callee 根；无观察的纯闭包不要求固定数量或名字的临时变量。
-- unluac: expect-contains [[return "stable",]]
-- unluac: expect-ast-min [[local-decl]] [[2]] [[@proto=16]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=17]]
-- unluac: expect-ast-min [[local-decl]] [[2]] [[@proto=18]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=19]]
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

-- 返回后的 caller 逐步覆写低槽，再在 __index 内观察 GC。原高返回准备区仍可能
-- 保留弱表中的对象，不能仅凭 callee 无 cleanup、末尾只有 COPY 就改为低槽直返。
local function check_return_packet()
    local returned = setmetatable({}, {__mode = "v"})
    local observations = {}
    local function make_value()
        local object = {}
        returned.value = object
        return object
    end
    local methods = setmetatable({}, {__index = function()
        collectgarbage("collect")
        collectgarbage("collect")
        observations[#observations + 1] = type(returned.value)
        return function() end
    end})
    local function copied_pair(x, y)
        local first = x
        local second = y
        return first, second
    end
    local function direct_pair(x, y)
        return x, y
    end
    local function copied_repeated(x, y)
        local first = x
        local second = y
        return first, second, second
    end
    local function direct_repeated(x, y)
        return x, y, y
    end
    local function observe(callback)
        callback(make_value(), nil)
        local a, b, c, d = 1, 1, 1, 1
        methods.observe()
        -- 高槽必须属于 caller 的实际 frame；删除这些局部或缩短构造器会改变观察窗口。
        local reserve = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
        return reserve[1]
    end
    collectgarbage("stop")
    observe(copied_pair)
    observe(direct_pair)
    observe(copied_repeated)
    observe(direct_repeated)
    collectgarbage("restart")
    assert(table.concat(observations, ",") == "table,nil,table,nil")
end
check_return_packet()
