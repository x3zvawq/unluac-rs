-- regress_14_generic_for_nested_continue#1: nested generic-for continue edges should stay structured
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-min [[generic-for]] [[3]] [[@proto=1]]
-- unluac: expect-ast-max [[generic-for]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[while]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[repeat]] [[0]] [[@proto=1]]
local episodes = {
    {
        pages = {
            {
                levels = {
                    { name = "first" },
                    { name = "target" },
                },
            },
        },
    },
    false,
    {
        pages = {
            {
                levels = {
                    { name = "after" },
                },
            },
        },
    },
    {pages = {{levels = {}}, {levels = {{name = "last"}}}}},
    {pages = {}},
}

local function get_level_index(name)
    local index = 1
    for _, episode in ipairs(episodes) do
        if episode then
            for _, page in ipairs(episode.pages) do
                for _, level in ipairs(page.levels) do
                    if level.name == name then
                        return index
                    end
                    index = index + 1
                end
            end
        end
    end
    return nil
end

local target, missing = get_level_index("target"), get_level_index("missing")
assert(target == 2 and missing == nil)
assert(get_level_index("first") == 1)
assert(get_level_index("after") == 3)
assert(get_level_index("last") == 4)
assert(get_level_index(nil) == nil)
print("regress_14_generic_for_nested_continue#1", target, missing)
