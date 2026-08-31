-- regress_352_multi_return_call_run_order: a call run may cross stable return prefixes but not observable snapshots
-- unluac: expect-contains [[local r3_0 =]]
-- unluac: expect-contains [[local r3_1 =]]

local observed = 0

local function prepare()
    observed = 1
    return select
end

local function make_first(value)
    return value
end

local function unsafe(value)
    observed = 0
    local picker = prepare()
    local first = make_first(value)
    return observed, picker(2, first, value)
end

local prefix, value = unsafe(43)
assert(prefix == 1 and value == 43)
