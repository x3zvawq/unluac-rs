-- regress_28_lua51_loop_branch_recovery#1: generic-for body guard should not fall back to goto
-- regress_28_lua51_loop_branch_recovery#2: short-circuit guard before while should leave loop header to loop lowering
-- regress_28_lua51_loop_branch_recovery#3: nil-initialized loop-carried value should stay structured
-- regress_28_lua51_loop_branch_recovery#4: entry debug local must be active before iterator setup
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[while ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[local levels =]]
-- unluac: expect-contains [[local function all_levels()]]
-- unluac: expect-contains [[local function target_score(target)]]
-- unluac: expect-contains [[local function count_remaining(start, skip)]]
-- unluac: expect-contains [[local function previous_level_name(target)]]
-- unluac: expect-contains [[for _, level in]]
-- unluac: expect-contains [[local previous = nil]]
-- unluac: expect-contains [[for _, level in all_levels() do]]
-- unluac: expect-order [[local previous = nil]] [[if previous then]]
-- unluac: expect-not-contains [[for _, level in r5_0, r5_1, r5_2 do]]
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

local observed_scope_name = false

local function inspect_caller_iterator()
    observed_scope_name = debug.getlocal(2, 1)
    return function() end
end

local function entry_local_scope_name()
    local previous = nil

    for _ in inspect_caller_iterator() do
    end

    return observed_scope_name
end

print("regress_28_lua51_loop_branch_recovery#1", target_score("target"), target_score("missing"))
print("regress_28_lua51_loop_branch_recovery#2", count_remaining(1, false), count_remaining(1, true))
print("regress_28_lua51_loop_branch_recovery#3", previous_level_name("target"), previous_level_name("first"))
print("regress_28_lua51_loop_branch_recovery#4", entry_local_scope_name())
