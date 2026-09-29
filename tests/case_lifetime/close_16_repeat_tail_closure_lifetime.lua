-- A closure in a nested tail scope must release its captured object before the until condition.
-- unluac: expect-contains [[    do]]
-- unluac: expect-ast-count [[local-binding]] [[6]]
-- unluac: expect-ast-count [[repeat]] [[1]]
-- unluac: expect-ast-count [[do-block]] [[1]]
-- unluac: expect-ast-count [[function]] [[3]]

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
        assert(hold() == value)
        collectgarbage("collect")
        assert(not finalized)
    end
until stop()

assert(observed == true)
print("regress_378_repeat_tail_closure_lifetime", observed)
