-- regress_210_repeat_multileaf_backedges#1: all short-circuit leaves own repeat backedges
-- unluac: expect-contains [[repeat]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[until p2_1 + 1 <= r2_1 or p2_0 and r2_0 > 100]]
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

print("regress_210_repeat_multileaf_backedges#1 break", with_break(true, 4))
print("regress_210_repeat_multileaf_backedges#1 repeat", without_break(false, 5))

local value, count = without_break(false, 97)
assert(value == 102 and count == 98)

value, count = with_break(false, 98)
assert(value == 102 and count == 98)
