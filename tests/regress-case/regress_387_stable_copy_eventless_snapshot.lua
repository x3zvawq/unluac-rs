-- regress_387_stable_copy_eventless_snapshot: stable-copy may recover eventless truthiness
-- snapshots, but must keep declaration-time snapshots and metamethod evaluation counts
-- unluac: expect-contains [[return not p1_0, not p1_0]]
-- unluac: expect-not-contains [[local r1_0 = not p1_0]]
-- unluac: expect-contains [[return p2_0 and p2_1 or p2_2]]
-- unluac: expect-not-contains [[local r2_0 = p2_0 and]]
-- unluac: expect-contains [[local r3_0 = not p3_0]]
-- unluac: expect-contains [[local r5_0 = p5_0 == p5_1]]
-- unluac: expect-contains [[p8_1(not p8_0)]]
-- unluac: expect-not-contains [[local r8_0 = not p8_0]]
-- unluac: expect-contains [[local r9_0 = not p9_0]]
-- unluac: expect-contains [[p10_1[1] = not p10_0]]
-- unluac: expect-not-contains [[local r10_0 = not p10_0]]
-- unluac: expect-contains [[p11_1(p11_0)]]
-- unluac: expect-not-contains [[local r11_0 = p11_0]]
-- An unchanged parameter is itself the declaration-time truthiness snapshot.
-- unluac: expect-contains [[until p13_0]]
-- unluac: expect-not-contains [[r13_0 = p13_0]]
-- unluac: expect-contains [[r14_0 = p14_0]]
-- unluac: expect-contains [[r15_0 = p15_1]]

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

local function write_after_last_use(value, sink)
    local inverted = not value
    sink()
    sink(inverted)
    value = true
end

local function repeated_dependency(value)
    local inverted = not value
    local count = 0
    while inverted and count < 2 do
        count = count + 1
        value = true
    end
    return count
end

local function same_owner_write(value, sink)
    local inverted = not value
    value, sink[1] = true, inverted
end

local function stable_parameter(value, sink)
    local alias = value
    sink()
    sink(alias)
end

local function allocated_twice()
    local value = {}
    return value, value
end

local function local_decl_handoff(seed)
    repeat
        local source = seed
        local alias = source
        local target = alias
        source = {}
    until target
    return true
end

local function parallel_handoff(seed)
    repeat
        local source = seed
        local alias = source
        local target, marker
        target, marker = alias, "parallel"
        source = {}
    until target
    return true
end

local function parameter_handoff(target, seed)
    repeat
        local source = seed
        local alias = source
        target = alias
        source = {}
    until target
    return target
end

local first, second = stable_not(false, function() end)
assert(first == true and second == true)

local left = setmetatable({}, equality)
local right = setmetatable({}, equality)
assert(stable_choice(true, left, right, function() end) == left)
assert(stable_choice(false, left, right, function() end) == right)
assert(written_dependency(false) == true)
assert(captured_dependency(false) == true)

local seen = {}
write_after_last_use(false, function(value)
    if value ~= nil then
        seen[#seen + 1] = value
    end
end)
assert(#seen == 1 and seen[1] == true)
assert(repeated_dependency(false) == 2)
local same_owner_seen = {}
same_owner_write(false, same_owner_seen)
assert(same_owner_seen[1] == true)
stable_parameter("parameter", function(value)
    if value ~= nil then
        seen[#seen + 1] = value
    end
end)
assert(seen[2] == "parameter")

local equal_first, equal_second = compared_twice(left, right)
assert(equal_first == true and equal_second == true)
assert(comparison_hits == 1)

local allocated_first, allocated_second = allocated_twice()
assert(allocated_first == allocated_second)

local handoff_seed = {}
assert(local_decl_handoff(handoff_seed) == true)
assert(parallel_handoff(handoff_seed) == true)
assert(parameter_handoff(nil, handoff_seed) == handoff_seed)
