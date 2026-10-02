-- regress_21_shared_terminal_return#1: shared terminal return should not force label/goto fallback
-- unluac: expect-contains [[return true]]
-- unluac: expect-contains [[return false]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
-- 比较操作数的先后读取需要一个快照，其余分支不应引入布尔控制变量。
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=4]]
-- unluac: expect-ast-count [[if]] [[10]] [[@proto=4]]
-- unluac: expect-ast-count [[local-binding]] [[14]]
-- unluac: expect-ast-count [[local-binding]] [[13]] [[@proto=0]]
local star_calls, feather_calls = 0, 0

local function showRequiredItemsPopup(level, reason)
    print("locked", level.name, reason)
end

local function calculateEpisodeStars(_episode)
    star_calls = star_calls + 1
    return 4
end

local function calculateFeatherScore(_episode)
    feather_calls = feather_calls + 1
    return 8
end

local function level_access_allowed(level, episode)
    if level.calendar or level.useDateLock then
        if not level.useDateLock then
            if episode.last_open_level >= level.index then
                return true
            end

            if level.days[episode.last_open_level + 1] then
                if level.seconds_to_open > 0 then
                    print("calendar locked", level.seconds_to_open)
                    return false
                else
                    return true
                end
            end

            return true
        else
            if level.layout_open then
                return true
            end
            if level.seconds_to_open > 0 then
                print("timer", level.seconds_to_open)
            end
            return false
        end
    else
        if not level.feathers_required then
            if level.stars_required then
                local stars = calculateEpisodeStars(episode)
                if stars < level.stars_required and not level.unlocked then
                    showRequiredItemsPopup(level, "stars")
                    return false
                end
            end
            return true
        else
            local feathers = calculateFeatherScore(episode)
            if feathers < level.feathers_required and not level.unlocked then
                showRequiredItemsPopup(level, "feathers")
                return false
            else
                return true
            end
        end
    end
end

local allowed = level_access_allowed({
    name = "bonus",
    feathers_required = 10,
    unlocked = false,
}, {
    last_open_level = 2,
})
assert(allowed == false)
print(
    "regress_21_shared_terminal_return#1",
    allowed
)

local saved_print, messages = print, {}
print = function(first, second, third)
    messages[#messages + 1] = { first, second, third }
end
local level = { name = "probe" }
local episode = { last_open_level = 2 }
local function check(expected, message, second, third, stars, feathers)
    star_calls, feather_calls, messages = 0, 0, {}
    assert(level_access_allowed(level, episode) == expected)
    assert(star_calls == (stars or 0) and feather_calls == (feathers or 0))
    if message then
        assert(#messages == 1 and messages[1][1] == message)
        assert(messages[1][2] == second and messages[1][3] == third)
    else
        assert(#messages == 0)
    end
end

check(true)
level.stars_required = 5
check(false, "locked", "probe", "stars", 1)
level.unlocked = 0
check(true, nil, nil, nil, 1)
level.unlocked, level.stars_required = false, 4
check(true, nil, nil, nil, 1)
level.stars_required = 0
check(true, nil, nil, nil, 1)
level.feathers_required = 9
check(false, "locked", "probe", "feathers", 0, 1)
level.unlocked = ""
check(true, nil, nil, nil, 0, 1)
level.unlocked, level.feathers_required = nil, 8
check(true, nil, nil, nil, 0, 1)

level.calendar, level.index = true, 2
check(true)
level.index, level.days, level.seconds_to_open = 3, {}, 10
check(true)
level.days[3] = 0
check(false, "calendar locked", 10)
level.seconds_to_open = 0
check(true)
level.seconds_to_open = -1
check(true)
level.calendar, level.useDateLock, level.layout_open = false, true, ""
check(true)
level.layout_open, level.seconds_to_open = false, 10
check(false, "timer", 10)
level.seconds_to_open = 0
check(false)
level.seconds_to_open = -1
check(false)

-- >= 的两个索引读取可触发元方法，不能为了少一个局部变量交换其顺序。
local reads = ""
episode = setmetatable({}, { __index = function(_, key)
    assert(key == "last_open_level")
    reads = reads .. "episode;"
    return 2
end })
level = setmetatable({ calendar = true, useDateLock = false }, { __index = function(_, key)
    assert(key == "index")
    reads = reads .. "level;"
    return 1
end })
check(true)
assert(reads == "episode;level;")

-- 并列字段赋值须保留 Lua 5.1 的逆序写回；空表先准备，末项常量直接写入。
reads = ""
level = setmetatable({}, { __newindex = function(_, key, value)
    if key == "seconds_to_open" then
        assert(reads == "" and value == 10)
    elseif key == "days" then
        assert(reads == "seconds_to_open;" and type(value) == "table" and next(value) == nil)
    else
        assert(key == "index" and reads == "seconds_to_open;days;" and value == 3)
    end
    reads = reads .. key .. ";"
end })
level.index, level.days, level.seconds_to_open = 3, {}, 10
assert(reads == "seconds_to_open;days;index;")
print = saved_print
