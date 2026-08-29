-- regress_387_stable_copy_eventless_snapshot: stable-copy may recover eventless truthiness
-- snapshots, but must keep declaration-time snapshots and metamethod evaluation counts
-- unluac: expect-contains [[return not p1_0, not p1_0]]
-- unluac: expect-not-contains [[local r1_0 = not p1_0]]
-- unluac: expect-contains [[return p2_0 and p2_1 or p2_2]]
-- unluac: expect-not-contains [[local r2_0 = p2_0 and]]
-- unluac: expect-contains [[local r3_0 = not p3_0]]
-- unluac: expect-contains [[local r5_0 = p5_0 == p5_1]]

local function stable_not(value, sink)
    local inverted = not value
    sink()
    return inverted, inverted
end

local function stable_choice(flag, left, right, sink)
    local selected = (flag and left) or right
    sink()
    return selected
end

local function written_dependency(value)
    local inverted = not value
    value = true
    return inverted
end

local comparison_hits = 0
local equality = {
    __eq = function()
        comparison_hits = comparison_hits + 1
        return true
    end,
}

local function compared_twice(left, right)
    local equal = left == right
    return equal, equal
end

local function captured_dependency(value)
    local inverted = not value
    local function mutate()
        value = true
    end
    mutate()
    return inverted
end

local function allocated_twice()
    local value = {}
    return value, value
end

local first, second = stable_not(false, function() end)
assert(first == true and second == true)

local left = setmetatable({}, equality)
local right = setmetatable({}, equality)
assert(stable_choice(true, left, right, function() end) == left)
assert(stable_choice(false, left, right, function() end) == right)
assert(written_dependency(false) == true)
assert(captured_dependency(false) == true)

local equal_first, equal_second = compared_twice(left, right)
assert(equal_first == true and equal_second == true)
assert(comparison_hits == 1)

local allocated_first, allocated_second = allocated_twice()
assert(allocated_first == allocated_second)
