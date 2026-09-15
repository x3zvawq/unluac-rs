-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[if ]]
-- unluac: expect-contains [[< 10]]
-- unluac: expect-contains [[while p1_0 do]]
-- unluac: expect-not-contains [[local r1_0 = p1_0]]
-- unluac: expect-contains [[local r2_0 = p2_0]]
-- unluac: expect-contains [[local r3_1 = p3_0]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved(multi-value use]]

local function f(v)
    while v do
        if v < 10 then
            v = 20
        else
            v = nil
        end
    end
end

local remaining = 2
local function preserve_loop_snapshot(value)
    local snapshot = value
    while remaining > 0 do
        print(value)
        snapshot = snapshot + 1
        remaining = remaining - 1
    end
    return snapshot
end

local function preserve_captured_parameter(value)
    local state = value
    local function original()
        return value
    end
    while state do
        state = nil
    end
    return original()
end

assert(preserve_loop_snapshot(10) == 12)
assert(preserve_captured_parameter("original") == "original")
return f
