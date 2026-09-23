-- 全局 RHS 在原 scratch 求值；收回声明仍须先触发读取，再触发写入，且各执行一次。
-- unluac: expect-contains [[destination = source]]
-- unluac: expect-contains [[_ENV = original.setmetatable({]] [[@debug=retained]]
-- unluac: expect-contains [[_ENV = replacement]] [[@debug=retained]]
-- unluac: expect-ast-count [[local-decl]] [[6]] [[@proto=0]]
-- unluac: expect-ast-count [[do-block]] [[1]] [[@proto=0]]
-- unluac: expect-not-contains [[unluac error]]
local original = _ENV
local events = {}
local previous = getmetatable(original)
setmetatable(original, {
    __index = function(_, key)
        events[#events + 1] = "read:" .. key
        return "payload"
    end,
    __newindex = function(_, key, value)
        events[#events + 1] = "write:" .. key .. ":" .. value
    end,
})
local function write()
    destination = source
end
write()
setmetatable(original, previous)
original.assert(original.table.concat(events, ",") == "read:source,write:destination:payload")

-- 可变的局部环境不一定能归一化成全局目标；保留这条拒绝路径的 cell 读取时点。
do
    local trace = {}
    local replacement = setmetatable({}, {
        __newindex = function(_, key, value)
            trace[#trace + 1] = "write:" .. key .. ":" .. value
        end,
    })
    local _ENV
    _ENV = original.setmetatable({}, {
        __index = function(_, key)
            trace[#trace + 1] = "read:" .. key
            _ENV = replacement
            return "redirected"
        end,
        __newindex = function()
            original.error("write used the old environment")
        end,
    })
    local function write_redirected()
        destination = source
    end
    write_redirected()
    original.assert(original.table.concat(trace, ",") == "read:source,write:destination:redirected")
end
original.print("environment_07_global_assignment_frame", "OK")
