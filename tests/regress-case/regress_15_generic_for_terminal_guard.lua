-- regress_15_generic_for_terminal_guard#1: shared terminal guard inside generic-for should not force goto fallback
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-min [[generic-for]] [[2]] [[@proto=1]]
local highscores = {
    first = { completed = true },
    target = { completed = true },
}

local episode = {
    pages = {
        {
            levels = {
                { name = "first" },
                { name = "target", episode_end = true },
            },
        },
    },
}

local function is_episode_complete()
    for _, page in ipairs(episode.pages) do
        for _, level in ipairs(page.levels) do
            if highscores[level.name] then
                local score = highscores[level.name]
                if score.completed then
                    if level.episode_end then
                        return true
                    end
                else
                    return false
                end
            else
                return false
            end
        end
    end
    return false
end

print("regress_15_generic_for_terminal_guard#1", is_episode_complete())
