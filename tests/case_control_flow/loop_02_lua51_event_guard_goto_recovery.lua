-- regress_10_lua51_event_guard_goto_recovery#1: event guard and default-value labels should structure without goto
events = {
    EID_START = "start",
    EID_BIRD = "bird",
    EID_DONE = "done",
}

local function callDelayed(delay, callback)
    print("regress_10_lua51_event_guard_goto_recovery#1", delay)
    callback()
end

local function cleanup(listener)
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

local hud = {
    powerupButtonShouldBeVisible = true,
    allowPause = true,
}

function hud:powerupButtonShouldBeVisible()
    return true
end

local listener = make_listener({ delayFinger = false, activationBirdIndex = 2 }, hud)
listener:eventTriggered({ id = events.EID_BIRD })

-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
