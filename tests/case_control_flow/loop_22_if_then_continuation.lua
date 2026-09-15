-- regress_214_loop_if_then_continuation#1: while implicit else must bypass the gated tail
-- regress_214_loop_if_then_continuation#2: generic-for implicit else must bypass the gated tail
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[    continue]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
local function while_case(enabled, choose_first, limit)
    local count, value = 0, 0
    while count < limit do
        count = count + 1
        if enabled then
            local step
            if choose_first then
                step = 1
            else
                step = 2
            end
            value = value + step
        end
    end
    return value, count
end

local function generic_for_case(enabled, choose_first)
    local value = 0
    for _, item in ipairs({ 1, 2, 3 }) do
        if enabled then
            local step
            if choose_first then
                step = item
            else
                step = item + 1
            end
            value = value + step
        end
    end
    return value
end

local while_value, while_count = while_case(true, false, 3)
local skipped_value, skipped_count = while_case(false, true, 4)
local generic_value, generic_skipped = generic_for_case(true, false), generic_for_case(false, true)
assert(while_value == 6 and while_count == 3 and skipped_value == 0 and skipped_count == 4)
assert(generic_value == 9 and generic_skipped == 0)
print("regress_214_loop_if_then_continuation#1", while_value, while_count, skipped_value, skipped_count)
print("regress_214_loop_if_then_continuation#2", generic_value, generic_skipped)
