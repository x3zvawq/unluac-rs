-- regress_31_numeric_for_terminal_branch_coverage#1: numeric-for 体内共享 terminal return 不应让 coverage 回退到 goto
-- unluac: expect-contains [[for]]
-- unluac: expect-contains [[return]]
-- unluac: expect-not-contains [[goto]]
-- unluac: expect-not-contains [[unluac error]]
local objects = {
    world = {
        first = { definition = "BIRD" },
        next = { definition = "BIRD" },
        bait = { definition = "ME_BAIT" },
    },
}

local currentBirdIndex = 0
local disabled = 0

local function getNextBird(index)
    if index == 1 then
        return "first"
    end
    if index == 2 then
        return "next"
    end
    return "bait"
end

local function disableME()
    disabled = disabled + 1
end

local function replace_next_bird()
    for offset = 1, 7 do
        local bird = getNextBird(currentBirdIndex + offset)
        if bird ~= nil and objects.world[bird].definition ~= "ME_BAIT" then
            local next_bird = getNextBird(currentBirdIndex + offset + 1)
            if next_bird == nil or objects.world[next_bird].definition == "ME_BAIT" then
                disableME()
            else
                return next_bird
            end
        end
    end
    disableME()
    return disabled
end

print("regress_31_numeric_for_terminal_branch_coverage#1", replace_next_bird())
