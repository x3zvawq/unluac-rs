-- A parameter overwrite can still be represented as a temp-home write when dead-temp starts.
-- The otherwise unread alias must keep the old parameter value rooted until the function exits.
-- unluac: expect-contains [[local r2_0 = p2_0]]
-- unluac: expect-not-contains [[unluac error]]

local finalized = false
local mt = {
    __gc = function()
        finalized = true
    end,
}

local function run(value)
    local discarded = value
    value = nil
    collectgarbage("collect")
    return not finalized
end

local function invoke()
    return run(setmetatable({}, mt))
end

assert(invoke() == true)
collectgarbage("collect")
assert(finalized == true)
print("regress_377_dead_temp_param_home_lifetime", finalized)
