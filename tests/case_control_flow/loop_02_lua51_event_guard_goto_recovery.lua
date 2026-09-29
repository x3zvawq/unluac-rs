-- regress_10_lua51_event_guard_goto_recovery#1: event guard and default-value labels should structure without goto
events = {
    EID_START = "start",
    EID_BIRD = "bird",
    EID_DONE = "done",
}

local delays, cleanups = {}, {}
local function callDelayed(delay, callback)
    delays[#delays + 1] = delay
    print("regress_10_lua51_event_guard_goto_recovery#1", delay)
    callback()
end

local function cleanup(listener)
    cleanups[#cleanups + 1] = listener
    print("regress_10_lua51_event_guard_goto_recovery#1", "cleanup", listener.birdCounter)
end

local function make_listener(config, hud)
    local listener = {}

    function listener.eventTriggered(self, event)
        if event.id == events.EID_START then
            if not (config.activationBirdIndex ~= nil and config.activationBirdIndex > 0) then
                hud.allowPause = false
            end
            return
        end

        if event.id == events.EID_BIRD then
            local counter = self.birdCounter
            if counter then
                self.birdCounter = counter
            else
                self.birdCounter = 1
            end

            if config.activationBirdIndex and self.birdCounter < config.activationBirdIndex then
                self.birdCounter = self.birdCounter + 1
                return
            end

            if hud.powerupButtonShouldBeVisible and hud:powerupButtonShouldBeVisible() then
                local callback = function()
                    hud.allowPause = true
                end
                local delay
                if config.delayFinger ~= nil then
                    local candidate = config.delayFinger
                    if candidate then
                        delay = candidate
                    else
                        delay = 0
                    end
                else
                    delay = 0
                end
                callDelayed(delay, callback)
                return
            end
        end

        if event.id == events.EID_DONE then
            if config.showForEachBird then
                self.firstActivationDone = true
                return
            end
        end

        cleanup(self)
    end

    return listener
end

local function scenario(config, visibility)
    delays, cleanups = {}, {}
    local hud = { allowPause = true, visibilityCalls = 0 }
    if visibility ~= "missing" then
        function hud:powerupButtonShouldBeVisible()
            self.visibilityCalls = self.visibilityCalls + 1
            return visibility
        end
    end
    return make_listener(config, hud), hud
end

local listener, hud = scenario({ delayFinger = false, activationBirdIndex = 2 }, true)
listener:eventTriggered({ id = events.EID_START })
assert(hud.allowPause and listener.birdCounter == nil and #cleanups == 0)
listener:eventTriggered({ id = events.EID_BIRD })
assert(listener.birdCounter == 2 and hud.visibilityCalls == 0 and #delays == 0 and #cleanups == 0)
hud.allowPause = false
listener:eventTriggered({ id = events.EID_BIRD })
assert(listener.birdCounter == 2 and hud.visibilityCalls == 1 and hud.allowPause)
assert(#delays == 1 and delays[1] == 0 and #cleanups == 0)
listener:eventTriggered({ id = events.EID_DONE })
assert(listener.firstActivationDone == nil and #cleanups == 1 and cleanups[1] == listener)

for _, config in ipairs({ {}, {activationBirdIndex = 0}, {activationBirdIndex = -1} }) do
    local item, view = scenario(config, true)
    item:eventTriggered({ id = events.EID_START })
    assert(view.allowPause == false and #delays == 0 and #cleanups == 0)
    item:eventTriggered({ id = events.EID_BIRD })
    assert(item.birdCounter == 1 and view.allowPause and view.visibilityCalls == 1)
    assert(#delays == 1 and delays[1] == 0 and #cleanups == 0)
end

for _, delay in ipairs({false, 0, 2.5}) do
    local item, view = scenario({delayFinger = delay, showForEachBird = true}, true)
    view.allowPause = false
    item.birdCounter = 0 -- Lua 中 0 为真，不能按“未初始化”替换成 1。
    item:eventTriggered({ id = events.EID_BIRD })
    assert(item.birdCounter == 0 and view.allowPause and view.visibilityCalls == 1)
    assert(#delays == 1 and delays[1] == (delay or 0) and #cleanups == 0)
    item:eventTriggered({ id = events.EID_DONE })
    assert(item.firstActivationDone == true and #cleanups == 0)
    item:eventTriggered({ id = "other" })
    assert(#cleanups == 1 and cleanups[1] == item)
end

for _, visibility in ipairs({false, "missing"}) do
    local item, view = scenario({}, visibility)
    item.birdCounter = false
    view.allowPause = false
    item:eventTriggered({ id = events.EID_BIRD })
    assert(item.birdCounter == 1 and view.allowPause == false and #delays == 0)
    assert(view.visibilityCalls == (visibility == "missing" and 0 or 1))
    assert(#cleanups == 1 and cleanups[1] == item)
end
for _, sample in ipairs({
    {first = false, second = 2.5, expected = 2.5, reads = 2},
    {first = true, second = false, expected = 0, reads = 2},
    {first = 0, second = 0, expected = 0, reads = 2},
    {second = 9, expected = 0, reads = 1},
}) do
    local reads = 0
    local config = setmetatable({}, {__index = function(_, key)
        if key == "delayFinger" then
            -- 两个参数、counter、callback 之后是原 delay 槽；条件求值期间仍应为 nil。
            local _, initial = debug.getlocal(2, 5)
            assert(initial == nil)
            reads = reads + 1
            if reads == 1 then return sample.first end
            return sample.second
        end
    end})
    local item, view = scenario(config, true)
    view.allowPause = false
    item:eventTriggered({ id = events.EID_BIRD })
    assert(reads == sample.reads and #delays == 1 and delays[1] == sample.expected)
    assert(view.allowPause and #cleanups == 0)
end
print("event_paths_checked")

-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-ast-count [[while]] [[0]] [[@proto=4]]
-- unluac: expect-ast-count [[repeat]] [[0]] [[@proto=4]]
-- unluac: expect-ast-count [[call]] [[3]] [[@proto=4]]
-- unluac: expect-ast-count [[method-call]] [[1]] [[@proto=4]]
-- unluac: expect-ast-count [[do-block]] [[0]] [[@proto=4]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=4]]
