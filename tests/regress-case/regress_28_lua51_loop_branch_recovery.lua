-- regress_28_lua51_loop_branch_recovery#1: generic-for body guard should not fall back to goto
-- regress_28_lua51_loop_branch_recovery#2: short-circuit guard before while should leave loop header to loop lowering
-- regress_28_lua51_loop_branch_recovery#3: nil-initialized loop-carried value should stay structured
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[while ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local levels = {
    { name = "first", score = 10 },
    { name = "target", score = 20 },
    { name = "last", score = 30 },
}

local function all_levels()
    local function iter(_, index)
        index = index + 1
        local level = levels[index]
        if level then
            return index, level
        end
    end

    return iter, nil, 0
end

local function target_score(target)
    for _, level in all_levels() do
        if level.name == target then
            return level.score
        end
    end

    return false
end

local scan_index = 0

local function count_remaining(start, skip)
    scan_index = start

    if levels[scan_index] and not skip then
        while levels[scan_index] do
            scan_index = scan_index + 1
        end
    end

    return scan_index
end

local function previous_level_name(target)
    local previous = nil

    for _, level in all_levels() do
        if level.name == target then
            if previous then
                return previous.name
            end
            return "none"
        end

        previous = {
            name = level.name,
            score = level.score,
        }
    end

    return "missing"
end

print("regress_28_lua51_loop_branch_recovery#1", target_score("target"), target_score("missing"))
print("regress_28_lua51_loop_branch_recovery#2", count_remaining(1, false), count_remaining(1, true))
print("regress_28_lua51_loop_branch_recovery#3", previous_level_name("target"), previous_level_name("first"))
