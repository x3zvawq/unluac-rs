-- A dead boolean value write can still release the previous parameter value for collection.
-- unluac: expect-ast-count [[table-list-field]] [[3]] [[@proto=0]]
-- unluac: expect-order [[("field", 1)]] [[("condition", true)]]

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

-- Reconstructing an argument pack preserves constructor-field and later-argument order.
local function mark(label, value)
    print("argument-order", label)
    return value
end
finalized = false
assert(run({ mark("field", 1), 2, 3 }, mark("condition", true)) == true)
