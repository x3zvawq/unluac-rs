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

-- The call/iterator preparation writes reuse homes that still carry escaped table roots.
-- They must not be removed until HIR can preserve the corresponding overwrite endpoints.
