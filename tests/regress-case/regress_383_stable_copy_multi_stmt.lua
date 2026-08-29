-- regress_383_stable_copy_multi_stmt: a stable local copy can replace every use across multiple
-- top-level statements when the whole rewrite commits atomically; reused primitive concepts stay named
-- unluac: expect-contains [[local r1_0 = 7]]
-- unluac: expect-contains [[return r2_0, r2_0]]
-- unluac: expect-not-contains [[local r2_1 = r2_0]]

local function primitive_copy(sink)
    local alias = 7
    sink(alias)
    return alias
end

local function local_copy(sink)
    local source = {}
    local alias = source
    sink(source)
    sink(alias)
    return source, alias
end

local primitive_seen
assert(primitive_copy(function(value)
    primitive_seen = value
end) == 7)
assert(primitive_seen == 7)

local first_seen
local second_seen
local first, second = local_copy(function(value)
    if first_seen == nil then
        first_seen = value
    else
        second_seen = value
    end
end)
assert(first == second)
assert(first_seen == first)
assert(second_seen == first)
