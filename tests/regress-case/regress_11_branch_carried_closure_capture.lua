local function recover_unlock_message(level)
    local needed = 0

    if level.feathers_required and level.feathers_required > 0 then
        local feathers = calculateFeatherScore(level.episode)
        needed = level.feathers_required - feathers
        consume(needed)
    elseif level.stars_required and level.stars_required > 0 then
        local stars = calculateEpisodeStars(level.episode)
        needed = level.stars_required - stars
        consume(needed)
    else
        needed = 0
        consume(needed)
    end

    local function on_unlock()
        return level.name, needed
    end

    return on_unlock
end

return recover_unlock_message

-- unluac: expect-contains [[return function()]]
-- unluac: expect-contains [[return p1_0.name, r1_0]]
-- unluac: expect-not-contains [[unluac error]]
