-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=1]] [[@dialect=lua5.1]]
local amount = 100
local function award(player, item, a, b, c, d)
    if not player then
        return false, false, false
    end
    if player.dead then
        Message("dead")
        return false, false, false
    end
    if Remote(player.id) then
        Message("remote")
        return false, false, false
    end
    local index = item.index
    if player:Count(5, index) < 1 then
        Message("empty")
        return false, false, false
    end
    local maximum = player:Maximum(CURRENCY.prestige)
    local space = player:Space(CURRENCY.prestige)
    local key = Tasks and Tasks.ranking
    local before = key and Read(player, SEASON, key) or 0
    Advance(player, "ranking", 1)
    if not key or (Read(player, SEASON, key) or 0) <= before then
        if maximum == nil or space == nil or space < amount or maximum < amount + player:Currency(CURRENCY.prestige) then
            Message("full")
            return false, false, false
        else
            player:Add(CURRENCY.prestige, amount, "rank", false)
        end
    end
    return false, true, false
end

CURRENCY = { prestige = 9 }
SEASON = 77
local events, state, phase = {}, {}, "before"
local function event(name)
    events[#events + 1] = name
end
function Remote(id)
    assert(id == 7)
    return false
end
function Message(message) event(message) end
function Read(player, season, key)
    assert(player.id == 7 and season == 77 and key == Tasks.ranking)
    event("read-" .. phase)
    return state[phase]
end
function Advance(player, key, step)
    assert(player.id == 7 and key == "ranking" and step == 1)
    event("advance")
    phase = "after"
end
local player = { id = 7, dead = false }
function player:Count(kind, index)
    assert(kind == 5 and index == 3)
    event("count")
    return 1
end
function player:Maximum(kind)
    assert(kind == 9)
    event("maximum")
    return state.maximum
end
function player:Space(kind)
    assert(kind == 9)
    event("space")
    return state.space
end
function player:Currency(kind)
    assert(kind == 9)
    event("currency")
    return 40
end
function player:Add(kind, value, reason, flag)
    assert(kind == 9 and value == 100 and reason == "rank" and flag == false)
    event("add")
end
local function check(key, before, after, space, maximum, success, expected)
    Tasks = { ranking = key }
    state = { before = before, after = after, space = space, maximum = maximum }
    events, phase = {}, "before"
    local first, second, third = award(player, { index = 3 })
    assert(first == false and second == success and third == false)
    assert(table.concat(events, ",") == expected)
    print("shared-tail-return", tostring(key), tostring(success), table.concat(events, ","))
end
check(nil, 1, 2, 100, 140, true, "count,maximum,space,advance,currency,add")
check(false, 1, 2, 99, 140, false, "count,maximum,space,advance,full")
check(0, 1, 2, 99, nil, true, "count,maximum,space,read-before,advance,read-after")
check("key", 2, 2, 100, 140, true, "count,maximum,space,read-before,advance,read-after,currency,add")
check("key", nil, nil, nil, 140, false, "count,maximum,space,read-before,advance,read-after,full")
check("key", 2, 1, 100, 139, false, "count,maximum,space,read-before,advance,read-after,currency,full")
local comparable = { __le = function(left, right)
    event("compare")
    return left.value <= right.value
end }
check("key", setmetatable({ value = 2 }, comparable), setmetatable({ value = 1 }, comparable), 100, 140, true,
    "count,maximum,space,read-before,advance,read-after,compare,currency,add")
check("key", setmetatable({ value = 1 }, comparable), setmetatable({ value = 2 }, comparable), 0, nil, true,
    "count,maximum,space,read-before,advance,read-after,compare")
