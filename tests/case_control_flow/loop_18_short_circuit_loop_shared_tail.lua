-- regress_18_short_circuit_loop_shared_tail#1: short-circuit loop arm should share tail without goto
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local level = {
    name = "bonus",
    display_number = "B-1",
    stars_required = true,
}

local episode = {
    bonus_content = {
        levels = {
            { name = "bonus" },
        },
    },
    pages = {
        { display_number = "1" },
    },
    per_page_level_numbering = false,
}

local function get_level_by_id(id)
    if id == "missing" then
        return nil
    end
    return level, "episode", 1
end

local function get_episode()
    return episode
end

local function get_level_number()
    return "3"
end

local function get_level_index()
    return "9"
end

local function template()
    return "world=%world%;level=%level%"
end

local function display_number(id)
    local current, episode_id, page = get_level_by_id(id)
    if current == nil then
        return "0-0"
    end

    local current_episode = get_episode(episode_id)
    if (current.stars_required or current.feather_required) and current_episode.bonus_content ~= nil then
        for _, bonus in ipairs(current_episode.bonus_content.levels) do
            if bonus.name == current.name and current.display_number ~= nil then
                return current.display_number
            end
        end
    end

    local world_number
    if current.world_number_override then
        world_number = current.world_number_override
    else
        world_number = current_episode.pages[page].display_number
    end

    local level_number
    if current_episode.per_page_level_numbering then
        level_number = get_level_number(id)
    else
        level_number = get_level_index(id)
    end

    return string.gsub(template(episode_id, page, current), "%%(%w+)%%", {
        world = world_number,
        level = level_number,
    })
end

local result = display_number("bonus")
assert(result == "B-1")
print("regress_18_short_circuit_loop_shared_tail#1", result)
