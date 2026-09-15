-- A closure in a nested tail scope must release its captured object before the until condition.
-- unluac: expect-contains [[    do]]

local finalized = false
local observed
local mt = {
    __gc = function()
        finalized = true
    end,
}

local function stop()
    collectgarbage("collect")
    observed = finalized
    return true
end

repeat
    do
        local value = setmetatable({}, mt)
        local function hold()
            return value
        end
    end
until stop()

assert(observed == true)
print("regress_378_repeat_tail_closure_lifetime", observed)
