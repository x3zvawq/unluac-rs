-- regress_398_dead_temp_stable_param_old_root: copying a stable parameter must still release the target slot's old root
-- unluac: expect-contains [[r2_0 = p2_0]]
-- unluac: expect-not-contains [[unluac error]]

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
print("regress_398_dead_temp_stable_param_old_root", finalized)
