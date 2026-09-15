-- regress_16_numeric_for_terminal_body#1: numeric-for body that only returns should stay structured
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local menu_ready = true

local levels = {
    { name = "first", world = 1 },
    { name = "target", world = 2 },
}

local function leaderboard_names(name)
    if not menu_ready then
        return false
    end

    for index = 1, #levels do
        local level = levels[index]
        if level.name == name then
            local result = {}
            local world_name = "world_" .. level.world
            local total_name = "total"
            if world_name then
                table.insert(result, world_name)
            end
            if total_name then
                table.insert(result, total_name)
            end
            return result
        end
    end

    return false
end

print("regress_16_numeric_for_terminal_body#1", leaderboard_names("target")[1])
