-- unluac: expect-contains [[while true do]]
-- unluac: expect-contains [[show_overlay()]]
-- unluac: expect-contains [[hide_overlay()]]
-- unluac: expect-contains [[r0_0 = screen_pressed()]]
-- unluac: expect-not-contains [[goto]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[repeat]]
-- unluac: expect-not-contains [[unluac error]]

local last_pressed = false
local pressed_edge = false

local function run()
    while true do
        if overlay_enabled() then
            if overlay_hidden() then
                hide_overlay()
            else
                show_overlay()
            end
        else
            hide_overlay()
        end

        if screen_pressed() and not last_pressed then
            pressed_edge = true
        else
            pressed_edge = false
        end
        last_pressed = screen_pressed()
    end
end

-- 在下一轮入口暂停，观察上一轮落地的两个 upvalue；原循环体不加入测试出口。
local enabled, hidden, first, second
local calls, action = 0, nil
function overlay_enabled()
    coroutine.yield(last_pressed, pressed_edge)
    return enabled
end
function overlay_hidden()
    return hidden
end
function hide_overlay()
    assert(action == nil)
    action = "hide"
end
function show_overlay()
    assert(action == nil)
    action = "show"
end
function screen_pressed()
    calls = calls + 1
    if calls == 1 then return first end
    assert(calls == 2)
    return second
end
local worker = coroutine.create(run)
local ok, last, edge = coroutine.resume(worker)
assert(ok and last == false and edge == false)
-- enabled, hidden, first read, second read, expected edge, expected action
local cases = {
    { true, false, true, true, true, "show" },
    { true, true, true, false, false, "hide" },
    { false, false, true, false, true, "hide" },
    { true, false, false, true, false, "show" },
    { false, true, false, false, false, "hide" },
}
for i, case in ipairs(cases) do
    enabled, hidden, first, second = case[1], case[2], case[3], case[4]
    calls, action = 0, nil
    ok, last, edge = coroutine.resume(worker)
    assert(ok and calls == 2 and last == second and edge == case[5] and action == case[6])
    assert(coroutine.status(worker) == "suspended")
    print("regress_70#1", i, last, edge, action, calls)
end
