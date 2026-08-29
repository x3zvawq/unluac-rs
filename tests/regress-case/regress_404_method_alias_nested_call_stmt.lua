-- regress_404_method_alias_nested_call_stmt: a stable call-statement prefix may own a nested method alias
-- unluac: expect-contains [[:m(41)]]

local owner = { value = 1 }

function owner:m(delta)
    self.value = self.value + delta
    return self.value
end

local observed
local function consume(value)
    observed = value
end

local function run(sink, source)
    local receiver = source
    sink(receiver.m(receiver, 41))
end

run(consume, owner)
assert(observed == 42, observed)
print("regress_404_method_alias_nested_call_stmt", observed)
