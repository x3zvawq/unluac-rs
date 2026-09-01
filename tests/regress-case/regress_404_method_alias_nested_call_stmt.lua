-- regress_404_method_alias_nested_call_stmt: a stable call-statement prefix may own a nested method alias
-- unluac: expect-contains [[:m(41)]]
-- unluac: expect-contains [[:m(1)]]

local owner = { value = 1 }

function owner:m(delta)
    self.value = self.value + delta
    return self.value
end

local observed
local observed_flag
local function consume(value)
    observed = value
end

local function consume_with_prefix(flag, value)
    observed_flag = flag
    observed = value
end

local function run(sink, source)
    local receiver = source
    sink(receiver.m(receiver, 41))
end

run(consume, owner)
assert(observed == 42, observed)

local function run_with_stable_prefix(sink, source, flag)
    local receiver = source
    sink(not flag, receiver.m(receiver, 1))
end

run_with_stable_prefix(consume_with_prefix, owner, false)
assert(observed_flag == true and observed == 43, observed)
print("regress_404_method_alias_nested_call_stmt", observed)
