-- A dead boolean value write can still release the previous parameter value for collection.

local finalized = false
local mt = {
    __gc = function()
        finalized = true
    end,
}

local function run(value, condition)
    setmetatable(value, mt)
    if condition then
        value = true
    else
        value = false
    end
    collectgarbage("collect")
    return finalized
end

assert(run({}, true) == true)
print("regress342-gc", finalized)
