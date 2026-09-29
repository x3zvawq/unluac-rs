-- regress_16_numeric_for_terminal_body#1: numeric-for body that only returns should stay structured
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[numeric-for]] [[1]]
-- unluac: expect-ast-count [[if]] [[4]]
-- unluac: expect-ast-count [[local-binding]] [[9]]
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
local result = leaderboard_names("target")
assert(#result == 2 and result[1] == "world_2" and result[2] == "total")
result = leaderboard_names("first")
assert(#result == 2 and result[1] == "world_1" and result[2] == "total")
assert(leaderboard_names("missing") == false)
menu_ready = false
levels = nil
assert(leaderboard_names("target") == false)
menu_ready = nil
assert(leaderboard_names("target") == false)
menu_ready = 0
levels = {{name = "target", world = 3}}
result = leaderboard_names("target")
assert(#result == 2 and result[1] == "world_3" and result[2] == "total")
levels = {}
assert(leaderboard_names("target") == false)
