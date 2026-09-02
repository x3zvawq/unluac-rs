-- regress_449_call_root_multi_home_overwrite: 一个 call result 覆盖多个旧 root home
-- unluac: expect-not-contains [[unluac error]]

local finalized = 0

local function make_value()
    return setmetatable({}, {
        __gc = function()
            finalized = finalized + 1
        end,
    })
end

local first = make_value()
local second = make_value()
assert(first and second)

local replacement = make_value()
first = replacement
second = replacement
collectgarbage("collect")
collectgarbage("collect")
assert(finalized == 2, "old roots retained")
assert(first == second and first == replacement)
print("regress_449_call_root_multi_home_overwrite", finalized)
