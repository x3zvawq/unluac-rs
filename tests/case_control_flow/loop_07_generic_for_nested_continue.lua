-- regress_14_generic_for_nested_continue#1: nested generic-for continue edges should stay structured
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-min [[generic-for]] [[3]] [[@proto=1]]
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
    {
        pages = {
            {
                levels = {
                    { name = "after" },
                },
            },
        },
    },
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
print("regress_14_generic_for_nested_continue#1", target, missing)
