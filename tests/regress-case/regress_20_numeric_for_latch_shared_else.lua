-- regress_20_numeric_for_latch_shared_else#1: numeric-for latch should not become explicit continue/goto
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[all_levels_open]]
-- unluac: expect-contains [[else]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[repeat]]
-- unluac: expect-not-contains [[unluac error]]
local releaseBuild = true
local last_open = {}

local settingsWrapper = {}

function settingsWrapper:getLastOpenLevel(name)
    return last_open[name] or 0
end

function settingsWrapper:setLastOpenLevel(name, value)
    last_open[name] = value
end

function settingsWrapper:isCurrentChristmasBought()
    return false
end

_G.native = {
    TimeStamp = {
        checkIfDatePassed = function(_year, _month, day)
            if day <= 2 then
                return 1
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

print("regress_20_numeric_for_latch_shared_else#1", open_calendar_levels())
