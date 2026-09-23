-- regress_09_mechanical_call_and_for_inline#1: collapse call and generic-for preparation runs
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=0]]
-- unluac: expect-ast-min [[call]] [[3]] [[@proto=0]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=0]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[assign]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=2]]
-- unluac: expect-contains [[for index, level in _G.ipairs(g_episodes[7].pages[3].levels) do]] [[@debug=retained]]
-- unluac: expect-contains [[loadLuaFile(scriptPath .. "/subsystems/eggdefender/EggDefenderSetup.lua", "")]]
scriptPath = "base"

function loadLuaFile(path, suffix)
    -- 快照函数返回后只剩弱引用；撤销全局强引用，观察调用方各层构造 scratch 的覆盖端点。
    local function snapshot(root)
        return setmetatable({ root, root[7], root[7].pages, root[7].pages[3], root[7].pages[3].levels }, { __mode = "v" })
    end
    local weak = snapshot(g_episodes)
    g_episodes = nil
    collectgarbage("collect")
    for i = 1, 5 do
        print("constructor-root", i, weak[i] ~= nil)
    end
    g_episodes = { [7] = { pages = { [3] = { levels = { "level-a", "level-b" } } } } }
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
