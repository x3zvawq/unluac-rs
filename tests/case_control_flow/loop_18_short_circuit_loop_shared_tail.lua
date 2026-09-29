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

local events = {}
local function get_level_by_id(id)
    events[#events + 1] = "level"
    if id == "missing" then
        return nil
    end
    return level, "episode", 1
end

local function get_episode(id)
    assert(id == "episode")
    events[#events + 1] = "episode"
    return episode
end

local function get_level_number(id)
    assert(id == "bonus")
    events[#events + 1] = "number"
    return "3"
end

local function get_level_index(id)
    assert(id == "bonus")
    events[#events + 1] = "index"
    return "9"
end

local function template(id, page, current)
    assert(id == "episode" and page == 1 and current == level)
    events[#events + 1] = "template"
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

local function check(id, expected, substitutions, order)
    events = {}
    local text, count = display_number(id)
    assert(text == expected and count == substitutions)
    assert(table.concat(events, ",") == order)
end
check("missing", "0-0", nil, "level")
check("bonus", "B-1", nil, "level,episode")
episode.bonus_content.levels = {{name = "other"}, {name = "bonus"}}
level.stars_required, level.feather_required = false, true
check("bonus", "B-1", nil, "level,episode")
level.display_number = nil
check("bonus", "world=1;level=9", 2, "level,episode,index,template")
level.display_number = "B-1"
episode.bonus_content.levels = {{name = "other"}}
episode.per_page_level_numbering = true
level.world_number_override = "W"
check("bonus", "world=W;level=3", 2, "level,episode,number,template")
episode.bonus_content.levels = {}
level.world_number_override = 0
check("bonus", "world=0;level=3", 2, "level,episode,number,template")
episode.bonus_content = nil
level.world_number_override = false
episode.per_page_level_numbering = false
check("bonus", "world=1;level=9", 2, "level,episode,index,template")
episode.bonus_content = {levels = {{name = "bonus"}}}
level.feather_required = nil
check("bonus", "world=1;level=9", 2, "level,episode,index,template")
level.stars_required = 0
check("bonus", "B-1", nil, "level,episode")
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=6]]
-- unluac: expect-ast-count [[while]] [[0]] [[@proto=6]]
-- unluac: expect-ast-count [[repeat]] [[0]] [[@proto=6]]
-- unluac: expect-ast-count [[local-binding]] [[8]] [[@proto=6]]
-- 根函数的并行字段写入与后继调用应保留原声明数量，不能另造 callee/参数复制链。
-- unluac: expect-ast-count [[local-binding]] [[11]] [[@proto=0]]
-- 并列字段写和嵌套构造器都收回原准备区，后继调用不经过 callee/参数别名。
-- unluac: expect-ast-count [[assign]] [[15]] [[@proto=0]]
-- unluac: expect-ast-count [[call]] [[12]] [[@proto=0]]
-- 保留缺失 level 的早退、bonus 循环及两个分支选择，不复制查询与模板调用。
-- unluac: expect-ast-count [[if]] [[5]] [[@proto=6]]
-- unluac: expect-ast-count [[assign]] [[4]] [[@proto=6]]
-- unluac: expect-ast-count [[call]] [[7]] [[@proto=6]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=7]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=7]]
-- unluac: expect-ast-count [[call]] [[4]] [[@proto=7]]
