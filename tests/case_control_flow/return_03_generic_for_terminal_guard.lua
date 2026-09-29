-- regress_15_generic_for_terminal_guard#1: shared terminal guard inside generic-for should not force goto fallback
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[generic-for]] [[2]]
-- unluac: expect-ast-count [[if]] [[3]]
-- unluac: expect-ast-count [[local-binding]] [[9]]
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

local complete = is_episode_complete()
assert(complete == true)
episode.pages[1].levels[3] = {name = "missing"}
assert(is_episode_complete() == true)
highscores.first.completed = false
assert(is_episode_complete() == false)
highscores.first.completed = nil
assert(is_episode_complete() == false)
highscores.first.completed = 0
highscores.target.completed = ""
assert(is_episode_complete() == true)
episode.pages[1].levels[2].episode_end = false
assert(is_episode_complete() == false)
episode.pages[1].levels[2].episode_end = true
highscores.first = nil
assert(is_episode_complete() == false)
highscores.first = {completed = true}
highscores.target = nil
assert(is_episode_complete() == false)
highscores.target = {completed = true}
episode.pages = {{levels = {}}, {levels = {{name = "target", episode_end = true}}}}
assert(is_episode_complete() == true)
episode.pages = {}
assert(is_episode_complete() == false)
episode.pages = {{levels = {}}}
assert(is_episode_complete() == false)
print("regress_15_generic_for_terminal_guard#1", complete)
