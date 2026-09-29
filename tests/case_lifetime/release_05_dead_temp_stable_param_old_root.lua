-- regress_398_dead_temp_stable_param_old_root: copying a stable parameter must still release the target slot's old root
-- unluac: expect-contains [[r2_0 = p2_0]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[local-binding]] [[4]]
-- unluac: expect-ast-count [[function]] [[2]]

local finalized = false
local mt = {
    __gc = function()
        finalized = true
    end,
}

local function run(value)
    local old = setmetatable({}, mt)
    old = value
    collectgarbage("collect")
    return finalized
end

assert(run(false) == true)
finalized = false
assert(run(nil) == true)
finalized = false
assert(run(27) == true)
print("regress_398_dead_temp_stable_param_old_root", finalized)
