-- regress_09_mechanical_call_and_for_inline#1: collapse call and generic-for preparation runs
scriptPath = "base"

function loadLuaFile(path, suffix)
    print("regress_09_mechanical_call_and_for_inline#1", path, suffix)
end

g_episodes = {
    [7] = {
        pages = {
            [3] = {
                levels = {
                    "level-a",
                    "level-b",
                },
            },
        },
    },
}

loadLuaFile(scriptPath .. "/subsystems/eggdefender/EggDefenderSetup.lua", "")

for index, level in _G.ipairs(g_episodes[7].pages[3].levels) do
    print("regress_09_mechanical_call_and_for_inline#1", index, level)
end

-- unluac: expect-contains [[loadLuaFile(scriptPath .. "/subsystems/eggdefender/EggDefenderSetup.lua", "")]]
-- unluac: expect-contains [[in _G.ipairs(g_episodes[7].pages[3].levels) do]]
-- unluac: expect-not-contains [[local r0_]]
