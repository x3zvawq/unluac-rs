-- unluac: expect-ast-count [[table-constructor]] [[1]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[table-list-field]] [[3]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[call]] [[5]] [[@proto=1]] [[@dialect=lua5.1]]
local function emit(a, b)
    local player = Find(a)
    local first = player.GetBuff(1, 1)
    local second = player.GetBuff(2, 1)
    if not first and not second then return end
    local target = Find(b)
    Send(target.id, "sync", player.id, 1, {player.x, player.y, player.z})
end

local events, first, second, middle, calls
local function record(value) events[#events + 1] = value end
local player = setmetatable({
    GetBuff = function(kind, level)
        assert(level == 1)
        record("buff" .. kind)
        if kind == 1 then return first end
        assert(kind == 2)
        return second
    end
}, {
    __index = function(_, key)
        record("player." .. key)
        if key == "id" then return 11 end
        if key == "x" then return 10 end
        if key == "y" then return middle end
        assert(key == "z")
        return 30
    end
})
local target = setmetatable({}, {
    __index = function(_, key)
        assert(key == "id")
        record("target.id")
        return 22
    end
})
function Find(id)
    record("find" .. id)
    if id == 1 then return player end
    assert(id == 2)
    return target
end
function Send(to, event, from, kind, position)
    record("send")
    calls = calls + 1
    assert(to == 22 and event == "sync" and from == 11 and kind == 1)
    assert(position[1] == 10 and position[2] == middle and position[3] == 30)
    assert(position[4] == nil)
end
local function check(left, right, y)
    events, calls, first, second, middle = {}, 0, left, right, y
    emit(1, 2)
    local expected = "find1,buff1,buff2"
    if left or right then
        expected = expected .. ",find2,target.id,player.id,player.x,player.y,player.z,send"
        assert(calls == 1)
    else
        assert(calls == 0)
    end
    assert(table.concat(events, ",") == expected)
    print("eager-prefix", tostring(left), tostring(right), tostring(y), calls, expected)
end
check(true, false, 20)
check(false, true, 20)
check(false, false, 20)
check(nil, nil, nil)
check(true, nil, nil)
