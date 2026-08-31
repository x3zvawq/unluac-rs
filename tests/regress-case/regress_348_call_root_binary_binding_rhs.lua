-- regress_348_call_root_binary_binding_rhs: a direct binding RHS does not add an evaluation
-- event between a call result and its same-home binary overwrite.
-- unluac: expect-not-contains [[ = r4_0 + p4_0]]
-- unluac: expect-contains [[() + p4_0]]
local finalized = false

local mt = {
    __add = function(value, increment)
        assert(not finalized)
        collectgarbage("collect")
        assert(not finalized)
        assert(increment == 7)
        return increment + 4
    end,
    __gc = function()
        finalized = true
    end,
}

local function make_value()
    return setmetatable({}, mt)
end

local function run(increment)
    local result = make_value()
    result = result + increment
    return result
end

assert(run(7) == 11)
collectgarbage("collect")
assert(finalized)
print("regress_348_call_root_binary_binding_rhs", finalized)
