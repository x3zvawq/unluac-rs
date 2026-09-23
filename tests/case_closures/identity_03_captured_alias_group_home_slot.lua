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

local next_assigned, next_captured, next_prior = captured_alias_group(false)
assert(next_assigned == 2 and next_captured == 2 and next_prior == (_VERSION == "Luau" and 2 or 0))
print("captured_alias_group_false", next_assigned, next_captured, next_prior)

-- PUC/JIT 须在 reader 调用前保存首项 RHS；Luau 的原字节码先写 seed，再调用 reader。
-- 两种顺序都不需要另存 callee、调用结果或 return COPY。
-- unluac: expect-ast-max [[local-binding]] [[4]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=1]] [[@dialect=luau]]
