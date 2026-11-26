-- regress_211_temp_inline_binding_snapshot#1: binding snapshot must stay before an earlier call
local value = 1
local calls = 0

local function mutate()
    assert(value == 1)
    calls = calls + 1
    value = 2
    return 7
end

local snapshot = value
local result = mutate()
assert(result == 7 and snapshot == 1 and value == 2 and calls == 1)
print("regress_211_temp_inline_binding_snapshot#1", result, snapshot, value)
