-- SELF 的 callee 覆盖结束低槽 lookup 根，首参仍须活过 method lookup 与参数求值。
-- 显式 local receiver 有独立低槽；各 VM 的根存活由各自源码执行基线比较。
local weak = setmetatable({}, {__mode = "v"})
local label
local function observe(where)
    collectgarbage("collect")
    collectgarbage("collect")
    print(label, where, weak.value ~= nil)
    return 17
end
local methods = setmetatable({}, {__index = function()
    observe("lookup")
    return function(self, value)
        assert(value == 17)
        self = nil
        observe("call")
    end
end})
local provider = setmetatable({}, {__index = function()
    local value = setmetatable({}, {__index = methods})
    weak.value = value
    return value
end})

local function direct()
    provider.worker:touch(observe("argument"), 0)
    observe("after")
end
local function retained()
    local receiver = provider.worker
    receiver:touch(observe("argument"), 0)
    observe("after")
end

collectgarbage("stop")
label = "direct"
direct()
label = "retained"
retained()
collectgarbage("restart")
