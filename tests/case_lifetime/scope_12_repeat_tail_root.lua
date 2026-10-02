-- 提前退出 guard 的落入路径不是原声明的词法末端；尾部表写入仍能观察 marker 的物理根。
-- unluac: expect-ast-count [[do-block]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=1]]
local weak = setmetatable({}, {__mode = "v"})
local function run(early, stop)
    local events, rounds = 0, 0
    local trace = setmetatable({}, {__newindex = function(t, k, v)
        collectgarbage("collect")
        assert(weak[1] ~= nil)
        events = events + 1
        rawset(t, k, v)
    end})
    local function tail(value)
        trace[#trace + 1] = "tail"
        return value
    end
    repeat
        rounds = rounds + 1
        if early and rounds == 1 then break end
        local marker = {}
        weak[1] = marker
        assert(marker ~= nil)
        if stop and rounds == 1 then break end
    until tail(rounds == 1)
    return events, rounds
end

local dispatch = {run}
for mask = 0, 3 do
    local events, rounds = dispatch[1](mask % 2 == 1, mask >= 2)
    assert(events == (mask == 0 and 1 or 0) and rounds == 1)
    print("repeat root", mask, events, rounds)
end
