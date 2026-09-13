-- 返回参数区的 COPY 可由原 RETURN 语法重发；删除局部声明不等于删除旧槽覆写。
-- 数字 __call 在原 callee 槽留下函数，接收端稍后通过 __index 强制 GC 观察退休。
local function fixed(left, right, tail)
    (1)()
    return right, left
end

local function open(left, right, tail)
    (1)()
    return left, tail(right)
end

local function probe(build, label, tail, count, first, second, third)
    local weak = setmetatable({}, {__mode = "v"})
    local meta = {}
    meta.__call = function() meta.__call = nil end
    weak.fn = meta.__call
    local original = debug.getmetatable(1)
    debug.setmetatable(1, meta)
    local observed
    local methods = setmetatable({}, {__index = function()
        collectgarbage("collect")
        collectgarbage("collect")
        observed = type(weak.fn)
        return function() end
    end})
    local function check(...)
        assert(select("#", ...) == count)
        local a, b, c = ...
        assert(a == first and b == second and c == third)
    end
    collectgarbage("stop")
    check(build(7, 11, tail))
    methods.observe()
    debug.setmetatable(1, original)
    collectgarbage("restart")
    assert(observed == "nil", "return preparation left the old callee root")
    print(label, observed, count)
end

probe(fixed, "fixed-return", nil, 2, 11, 7)
probe(open, "open-empty", function() end, 1, 7)
probe(open, "open-nil", function(value) return nil, value + 1 end, 3, 7, nil, 12)
