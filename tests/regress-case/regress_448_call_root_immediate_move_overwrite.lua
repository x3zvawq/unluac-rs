-- regress_448_call_root_immediate_move_overwrite: call 结果经紧邻 MOVE 覆盖旧 root home
-- unluac: expect-not-contains [[unluac error]]

local finalized = 0

local function make_old_value()
    return setmetatable({}, {
        __gc = function()
            finalized = finalized + 1
        end,
    })
end

local function replacement()
    collectgarbage("collect")
    assert(finalized == 0)
    return "replacement"
end

local value = make_old_value()
assert(value ~= nil)
local sink = {}
value = replacement()
sink.field = value
collectgarbage("collect")
assert(finalized == 1)
assert(sink.field == "replacement")
print("regress_448_call_root_immediate_move_overwrite", finalized, sink.field)
