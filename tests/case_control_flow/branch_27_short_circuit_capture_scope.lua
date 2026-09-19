-- 短路条件共享 then/else，then 内闭包跨 scope 退出后仍读取捕获时的 sts。
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-contains [[ or ]]
-- unluac: expect-contains [[ and ]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=1]] [[@dialect=lua5.1]]
local C = {}

C.execSTSTask = function(self, a1, a2)
    if (a1 == nil or a1 == C.ST2) and a2 then
        do
            local sts = C.STS
            local fn = function()
                local a1_1 = 5
                some_fn(a1_1, function()
                    local a = { id = sts }
                    report(a.id)
                end)
            end
            if getCurr() <= 5 then
                fn()
            end
        end
    else
        C.execSTETask(self, a1)
    end
end

local events, pending = {}, {}
local current, expected_self, expected_arg, captured
local config = { ST2 = 7 }
setmetatable(C, { __index = function(_, key)
    events[#events + 1] = key
    return config[key]
end })
function getCurr()
    events[#events + 1] = "current"
    return current
end
function some_fn(value, callback)
    assert(value == 5)
    events[#events + 1] = "queue"
    pending[#pending + 1] = callback
end
function report(value)
    assert(value == captured)
    events[#events + 1] = "capture"
end
C.execSTETask = function(self, value)
    assert(self == expected_self and value == expected_arg)
    events[#events + 1] = "else"
end

local function check(arg, enabled, level, expected)
    events, pending = {}, {}
    current, expected_arg = level, arg
    expected_self, captured = {}, {}
    config.STS = captured
    C.execSTSTask(expected_self, arg, enabled)
    -- 延后执行内层闭包，观察 close 后捕获身份，而非再次从 C.STS 取值。
    config.STS = {}
    for _, callback in ipairs(pending) do callback() end
    local actual = table.concat(events, ",")
    assert(actual == expected, actual)
    print(actual)
end
check(nil, true, 5, "STS,current,queue,capture")
check(7, true, 5, "ST2,STS,current,queue,capture")
check(8, true, 5, "ST2,else")
check(nil, false, 5, "else")
check(7, false, 5, "ST2,else")
check(nil, true, 6, "STS,current")
check(7, true, 6, "ST2,STS,current")
