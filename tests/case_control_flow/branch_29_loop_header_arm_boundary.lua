-- 循环 header 是条件臂的完成边界，另一臂的尾部动作仍必须受条件控制。
-- unluac: expect-ast-min [[if]] [[5]] [[@proto=1]] [[@dialect=lua5.1]]

local function worker()
    while true do
        coroutine.yield()
        if enabled() then
            if accepts(1) then
                record(1)
            elseif accepts(2) then
                record(2)
            elseif accepts(3) then
                record(3)
            else
                if not accepts(4) then
                    record(4)
                end
            end
        end
    end
end

local selected, active = 0, true
local checks, actions = {}, {}
function enabled() return active end
function accepts(index)
    checks[#checks + 1] = index
    return selected == index
end
function record(index) actions[#actions + 1] = index end

local thread = coroutine.create(worker)
assert(coroutine.resume(thread))
for index = 0, 4 do
    selected = index
    checks, actions = {}, {}
    assert(coroutine.resume(thread))
    local expected = index == 0 and 4 or index
    assert(#checks == expected)
    for i = 1, expected do assert(checks[i] == i) end
    if index == 4 then
        assert(#actions == 0)
    else
        assert(#actions == 1 and actions[1] == expected)
    end
    print('branch-tail', index, #checks, #actions)
end
active = false
checks, actions = {}, {}
assert(coroutine.resume(thread))
assert(#checks == 0 and #actions == 0)
