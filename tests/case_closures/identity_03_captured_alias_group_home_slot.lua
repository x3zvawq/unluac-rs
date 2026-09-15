-- regress_171_captured_alias_group_home_slot#1: phi 别名组必须写回组内已被闭包捕获的 home slot
-- unluac: expect-not-contains [[unluac error]]
local function captured_alias_group(flag)
    local seed = 0
    local reader = function()
        return seed
    end
    local proxy = {}
    seed, proxy.value = flag and 1 or 2, reader()
    return seed, reader(), proxy.value
end

local assigned, captured, prior = captured_alias_group(true)
local expected_prior = _VERSION == "Luau" and 1 or 0
assert(assigned == 1 and captured == 1 and prior == expected_prior)
print("regress_171_captured_alias_group_home_slot#1", assigned, captured, prior)
