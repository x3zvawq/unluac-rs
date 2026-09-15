-- regress_21_shared_terminal_return#1: shared terminal return should not force label/goto fallback
-- unluac: expect-contains [[return true]]
-- unluac: expect-contains [[return false]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local function showRequiredItemsPopup(level, reason)
    print("locked", level.name, reason)
end

local function calculateEpisodeStars(_episode)
    return 4
end

local function calculateFeatherScore(_episode)
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
