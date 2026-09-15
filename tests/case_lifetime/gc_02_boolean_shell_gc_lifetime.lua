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

-- Both boolean writes must release the donated argument slot.
finalized = false
assert(run({}, false) == true)

-- Display complexity cannot create an extra caller root for a constructor argument.
finalized = false
assert(run({ a = 1, b = 2, c = 3, d = 4, e = 5, f = 6 }, true) == true)

-- The fixed prefix of an OPEN call pack carries the same argument ownership.
local function condition()
    print("open-condition")
    return true
end
finalized = false
assert(run({}, condition()) == true)

-- A source owner below the call base is independent of the donated argument copy.
local function kept_by_caller()
    local owner = {}
    finalized = false
    assert(run(owner, true) == false)
    assert(owner ~= nil)
end
kept_by_caller()
collectgarbage("collect")
assert(finalized == true)
