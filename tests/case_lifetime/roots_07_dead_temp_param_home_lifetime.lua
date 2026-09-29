-- A parameter overwrite can still be represented as a temp-home write when dead-temp starts.
-- The otherwise unread alias must keep the old parameter value rooted until the function exits.
-- unluac: expect-contains [[local r2_0 = p2_0]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[local-binding]] [[6]]
-- unluac: expect-ast-count [[function]] [[3]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=2]]

local finalized = false
local finalizations = 0
local mt = {
    __gc = function()
        finalized = true
        finalizations = finalizations + 1
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
assert(finalizations == 1)
finalized = false
assert(invoke() == true)
collectgarbage("collect")
assert(finalized == true and finalizations == 2)
print("regress_377_dead_temp_param_home_lifetime", finalized)
