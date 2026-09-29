-- regress_20_numeric_for_latch_shared_else#1: numeric-for latch should not become explicit continue/goto
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[all_levels_open]]
-- unluac: expect-contains [[else]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[repeat]]
-- unluac: expect-not-contains [[local r1_0 = r0_1[p1_1]]
-- unluac: expect-contains [[return r0_1[p1_1] or 0]]
-- unluac: expect-not-contains [[unluac error]]
local releaseBuild = true
local last_open = {}
local events = {}
local bought, christmas = false, false

local settingsWrapper = {}

function settingsWrapper:getLastOpenLevel(name)
    assert(self == settingsWrapper)
    events[#events + 1] = "get:" .. name
    return last_open[name] or 0
end

function settingsWrapper:setLastOpenLevel(name, value)
    assert(self == settingsWrapper)
    events[#events + 1] = "set:" .. name .. ":" .. value
    last_open[name] = value
end

function settingsWrapper:isCurrentChristmasBought()
    assert(self == settingsWrapper)
    events[#events + 1] = "buy"
    return bought
end

_G.native = {
    TimeStamp = {
        checkIfDatePassed = function(_year, _month, day)
            assert(_year == 2026 and _month == 12)
            events[#events + 1] = "date:" .. day
            if day == 25 and christmas then
                return 1
            end
            if day <= 2 then
                return 1
            end
            if day == 4 then
                return 2
            end
            return 0
        end,
    },
}

local allLocalEpisodeKeys = { "calendar" }
local episodes = {
    calendar = {
        pages = {
            {
                calendar = { year = 2026, month = 12 },
                useDateLock = false,
                all_levels_open = true,
                levels = {
                    { index = 1 },
                    { index = 2 },
                    { index = 3 },
                },
            },
        },
    },
}

local function getLocalEpisode(name)
    events[#events + 1] = "episode:" .. name
    return episodes[name]
end

local function open_calendar_levels()
    for index = 1, #allLocalEpisodeKeys do
        local key = allLocalEpisodeKeys[index]
        local episode = getLocalEpisode(key)
        if episode.pages and settingsWrapper:getLastOpenLevel(key) < 200 then
            local page = episode.pages[1]
            if page ~= nil and page.calendar and not page.useDateLock then
                if page.all_levels_open then
                    print("opening all calendar levels: all_levels_open")
                    settingsWrapper:setLastOpenLevel(key, 200)
                elseif _G.native.TimeStamp.checkIfDatePassed(page.calendar.year, 12, 25) == 1 or settingsWrapper:isCurrentChristmasBought() or releaseBuild == false then
                    print("opening all calendar levels")
                    settingsWrapper:setLastOpenLevel(key, 200)
                else
                    local open_count = 0
                    for _, level in pairs(page.levels) do
                        local passed = _G.native.TimeStamp.checkIfDatePassed(page.calendar.year, page.calendar.month, level.index)
                        if passed == 1 then
                            open_count = open_count + 1
                        elseif passed == 0 then
                            break
                        end
                    end

                    if open_count ~= settingsWrapper:getLastOpenLevel(key) then
                        settingsWrapper:setLastOpenLevel(key, open_count)
                    end
                end
            end
        end
    end

    return last_open.calendar
end

local opened = open_calendar_levels()
assert(opened == 200)
assert(table.concat(events, ",") == "episode:calendar,get:calendar,set:calendar:200")
print("regress_20_numeric_for_latch_shared_else#1", opened)

local page = episodes.calendar.pages[1]
local function check(initial, expected, order)
    last_open.calendar = initial
    events = {}
    assert(open_calendar_levels() == expected)
    assert(table.concat(events, ",") == order)
end
-- 跳过不同层次的条件时，仍须继续处理 numeric-for 的后续 episode。
allLocalEpisodeKeys = {"skip", "calendar", "after"}
episodes.skip = {pages = false}
episodes.after = {pages = false}
check(200, 200, "episode:skip,episode:calendar,get:calendar,episode:after")
episodes.calendar.pages = nil
check(7, 7, "episode:skip,episode:calendar,episode:after")
episodes.calendar.pages = {}
check(7, 7, "episode:skip,episode:calendar,get:calendar,episode:after")
episodes.calendar.pages = {page}
page.calendar = false
check(7, 7, "episode:skip,episode:calendar,get:calendar,episode:after")
page.calendar = {year = 2026, month = 12}
page.useDateLock = true
check(7, 7, "episode:skip,episode:calendar,get:calendar,episode:after")
page.useDateLock = false
allLocalEpisodeKeys = {"calendar"}
page.all_levels_open = false
christmas = true
check(0, 200, "episode:calendar,get:calendar,date:25,set:calendar:200")
christmas = false
bought = true
check(0, 200, "episode:calendar,get:calendar,date:25,buy,set:calendar:200")
bought = false
releaseBuild = false
check(0, 200, "episode:calendar,get:calendar,date:25,buy,set:calendar:200")
releaseBuild = true
-- 每组 level 的日期相同，观察次数不依赖 pairs 的遍历顺序。
page.levels = {{index = 1}, {index = 1}, {index = 1}}
check(nil, 3, "episode:calendar,get:calendar,date:25,buy,date:1,date:1,date:1,get:calendar,set:calendar:3")
check(3, 3, "episode:calendar,get:calendar,date:25,buy,date:1,date:1,date:1,get:calendar")
page.levels = {{index = 3}, {index = 3}, {index = 3}}
check(5, 0, "episode:calendar,get:calendar,date:25,buy,date:3,get:calendar,set:calendar:0")
page.levels = {{index = 4}, {index = 4}, {index = 4}}
check(0, 0, "episode:calendar,get:calendar,date:25,buy,date:4,date:4,date:4,get:calendar")
page.levels = {}
check(5, 0, "episode:calendar,get:calendar,date:25,buy,get:calendar,set:calendar:0")
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=6]]
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=6]]
-- unluac: expect-ast-count [[break]] [[1]] [[@proto=6]]
-- unluac: expect-ast-count [[while]] [[0]] [[@proto=6]]
-- unluac: expect-ast-count [[local-binding]] [[8]] [[@proto=6]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=7]]
-- unluac: expect-ast-count [[local-binding]] [[13]] [[@proto=0]]
