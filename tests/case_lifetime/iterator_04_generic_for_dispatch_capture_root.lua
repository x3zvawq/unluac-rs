-- A generic-for iterator is called at least once even when its body never runs. The call may
-- publish a captured allocation, whose repeat-body root must remain alive through the condition.
-- unluac: expect-ast-count [[generic-for]] [[1]]
-- unluac: expect-ast-count [[repeat]] [[1]]
-- unluac: expect-ast-count [[local-binding]] [[7]]
-- unluac: expect-ast-count [[function]] [[2]]

local weak = setmetatable({}, { __mode = "v" })
local alive_at_condition = false
local iterations = 0

local function finish_iteration()
    collectgarbage("collect")
    collectgarbage("collect")
    alive_at_condition = weak[1] ~= nil
    assert(alive_at_condition)
    iterations = iterations + 1
    return iterations == 2
end

repeat
    local item = {}
    local function iterator()
        weak[1] = item
        return nil
    end

    for _ in iterator do
        error("iterator must terminate before entering the body")
    end
until finish_iteration()

assert(alive_at_condition)
assert(iterations == 2)
collectgarbage("collect")
assert(weak[1] == nil)
print("regress_453_generic_for_dispatch_capture_root", "OK")
