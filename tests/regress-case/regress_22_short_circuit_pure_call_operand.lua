-- regress_22_short_circuit_pure_call_operand#1: method call behind a pure boolean shell should not force goto fallback
-- unluac: expect-contains [[:isNBALevelsBought()]]
-- unluac: expect-contains [[free_levels ~= false]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local settingsWrapper = {
    bought = true,
}

function settingsWrapper:isNBALevelsBought()
    return self.bought
end

local episode = {
    pages = {
        {
            ignoreInThreeStarCalculations = false,
            free_levels = false,
            levels = {
                { stars = 2 },
                { stars = 1 },
            },
        },
        {
            ignoreInThreeStarCalculations = true,
            free_levels = false,
            levels = {
                { stars = 3 },
            },
        },
    },
}

local function count_stars(data)
    local total = 0
    for page_index = 1, #data.pages do
        local page = data.pages[page_index]
        if (not page.ignoreInThreeStarCalculations) and (page.free_levels ~= false or settingsWrapper:isNBALevelsBought()) then
            for level_index = 1, #page.levels do
                total = total + page.levels[level_index].stars
            end
        end
    end
    return total
end

print("regress_22_short_circuit_pure_call_operand#1", count_stars(episode))
