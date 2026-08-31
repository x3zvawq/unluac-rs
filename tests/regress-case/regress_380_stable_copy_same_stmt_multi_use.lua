-- regress_380_stable_copy_same_stmt_multi_use: stable aliases may replace every use in one statement
-- unluac: expect-contains [[return r1_0, r1_0, r1_0]]
-- unluac: expect-contains [[return p2_0(r2_0, r2_0, r2_0)]]
-- unluac: expect-not-contains [[local r1_1 = r1_0]]
-- unluac: expect-not-contains [[local r2_1 = r2_0]]

local function return_alias()
    local source = {}
    local alias = source
    return source, alias, alias
end

local function call_alias(sink)
    local source = {}
    local alias = source
    return sink(source, alias, alias)
end

local function split_uses(sink)
    local source = {}
    local alias = source
    sink(alias)
    return alias
end

local first, second, third = return_alias()
assert(first == second and second == third)
assert(call_alias(function(a, b, c)
    return a == b and b == c
end))

local observed
local split = split_uses(function(item)
    observed = item
end)
assert(observed == split)
