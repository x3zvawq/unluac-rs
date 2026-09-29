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

while_value, while_count = while_case(true, true, 3)
assert(while_value == 3 and while_count == 3)
while_value, while_count = while_case(nil, true, 2)
assert(while_value == 0 and while_count == 2)
while_value, while_count = while_case(0, "", 2)
assert(while_value == 2 and while_count == 2)
while_value, while_count = while_case(true, nil, 4)
assert(while_value == 8 and while_count == 4)
while_value, while_count = while_case(true, true, 0)
assert(while_value == 0 and while_count == 0)
while_value, while_count = while_case(true, true, -1)
assert(while_value == 0 and while_count == 0)
while_value, while_count = while_case(true, false, 1.5)
assert(while_value == 4 and while_count == 2)
assert(generic_for_case(true, true) == 6)
assert(generic_for_case(nil, true) == 0)
assert(generic_for_case(0, false) == 9)
assert(generic_for_case(true, 0) == 6)
-- 保留原 step 的 nil 初始化及两层条件，不额外物化循环状态。
-- unluac: expect-ast-count [[while]] [[1]]
-- unluac: expect-ast-count [[generic-for]] [[1]]
-- unluac: expect-ast-count [[repeat]] [[0]]
-- unluac: expect-ast-count [[if]] [[4]]
-- unluac: expect-ast-count [[local-binding]] [[15]]
-- unluac: expect-ast-count [[local-binding]] [[8]] [[@proto=0]]
