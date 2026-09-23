-- unluac: expect-ast-min [[if]] [[1]]
-- unluac: expect-ast-count [[local-binding]] [[10]] [[@proto=0]]
-- unluac: expect-ast-min [[if]] [[1]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=5]] [[@dialect=luajit]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-contains [[function GFunc.isOpenstor()]]
-- unluac: expect-contains [[function GFunc.isOfficialChannel()]]
local RateUs = {}

RateUs.isAvailable = function()
    if GFunc.isOpenstor() then
    else
        if not GFunc.isOfficialChannel() then
            return false
        end
    end
    return RateUs.status == 1 and 30 <= require("app.main.player").lv()
end

-- 每条路径同时观察结果与短路调用；加载 player 不能越过渠道或 status 的拒绝分支。
local log, open, official, level = {}, false, false, 0
GFunc = {}
function GFunc.isOpenstor()
    log[#log + 1] = "open"
    return open
end
function GFunc.isOfficialChannel()
    log[#log + 1] = "official"
    return official
end
local player = {}
function player.lv()
    log[#log + 1] = "lv"
    return level
end
package.preload["app.main.player"] = function()
    log[#log + 1] = "require"
    return player
end
-- open, official, status, level, expected result, expected call sequence
local cases = {
    { false, false, 1, 30, false, "open,official" },
    { false, true, 0, 30, false, "open,official" },
    { false, true, 2, 30, false, "open,official" },
    { false, true, 1, 29, false, "open,official,require,lv" },
    { false, true, 1, 30, true, "open,official,require,lv" },
    { true, false, 0, 30, false, "open" },
    { true, false, 1, 29, false, "open,require,lv" },
    { true, false, 1, 30, true, "open,require,lv" },
    { true, true, 1, 31, true, "open,require,lv" },
}
for i, case in ipairs(cases) do
    open, official, RateUs.status, level = case[1], case[2], case[3], case[4]
    log = {}
    package.loaded["app.main.player"] = nil
    local result = RateUs.isAvailable()
    assert(result == case[5] and table.concat(log, ",") == case[6])
    print("regress_324#1", i, result, table.concat(log, ","))
end
