-- regress_210_repeat_multileaf_backedges#1: all short-circuit leaves own repeat backedges
-- unluac: expect-contains [[repeat]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- LuaJIT reverses child proto numbering; the condition contract does not pin that identity.
-- unluac: expect-contains [[until ]]
-- unluac: expect-contains [[ + 1 <= ]]
-- unluac: expect-contains [[ or p]]
-- unluac: expect-contains [[ > 100]]
local function with_break(enabled, limit)
    local value, count = 4, 0
    repeat
        count = count + 1
        value = value + 1
        if count >= limit then
            break
        end
    until count >= limit + 1 or (enabled and value > 100)
    return value, count
end

local function without_break(enabled, limit)
    local value, count = 4, 0
    repeat
        count = count + 1
        value = value + 1
    until count >= limit + 1 or (enabled and value > 100)
    return value, count
end

local break_value, break_count = with_break(true, 4)
local repeat_value, repeat_count = without_break(false, 5)
assert(break_value == 8 and break_count == 4)
assert(repeat_value == 10 and repeat_count == 6)
print("regress_210_repeat_multileaf_backedges#1 break", break_value, break_count)
print("regress_210_repeat_multileaf_backedges#1 repeat", repeat_value, repeat_count)

local value, count = without_break(false, 97)
assert(value == 102 and count == 98)

value, count = with_break(false, 98)
assert(value == 102 and count == 98)

-- Exercise the other short-circuit leaf before the numeric limit can terminate the loop.
value, count = without_break(true, 200)
assert(value == 101 and count == 97)
value, count = with_break(true, 200)
assert(value == 101 and count == 97)
