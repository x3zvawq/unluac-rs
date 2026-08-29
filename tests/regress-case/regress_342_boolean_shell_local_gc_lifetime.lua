-- A boolean shell write must release the call result kept in the same local home.

local finalized = false
local mt = {
    __gc = function()
        finalized = true
    end,
}

local function run(condition)
    local value = setmetatable({}, mt)
    collectgarbage("collect")
    local survived_before_write = not finalized
    if condition then
        value = true
    else
        value = false
    end
    collectgarbage("collect")
    return survived_before_write, finalized
end

local before_write, after_write = run(true)
assert(before_write == true and after_write == true)
print("regress342-local-gc", before_write, after_write)
