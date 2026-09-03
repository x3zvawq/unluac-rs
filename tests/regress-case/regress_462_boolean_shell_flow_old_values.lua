-- regress_462_boolean_shell_flow_old_values: 旧值分类沿共享 CFG 的前向入口与回边传播。
-- unluac: expect-not-contains [[not not p1_0]]
-- unluac: expect-not-contains [[if p4_1]]
-- unluac: expect-not-contains [[if not p4_1]]
local function primitive_entry(flag)
    local value
    if flag then
        value = nil
        goto joined
    end
    value = 7
    ::joined::
    if flag then value = true else value = false end
    return "primitive"
end
assert(primitive_entry(true) == "primitive")
assert(primitive_entry(false) == "primitive")

local finalized = 0
local mt = { __gc = function() finalized = finalized + 1 end }
local function resource_backedge(flag)
    local value = nil
    local iteration = 0
    ::again::
    if flag then value = true else value = false end
    collectgarbage("collect")
    collectgarbage("collect")
    assert(finalized == iteration, "backedge shell failed to release old value")
    if iteration == 3 then return end
    value = setmetatable({}, mt)
    collectgarbage("collect")
    collectgarbage("collect")
    assert(finalized == iteration, "backedge value was released before the shell")
    iteration = iteration + 1
    goto again
end
resource_backedge(true)
finalized = 0
resource_backedge(false)

-- 两个入口使 HIR 保留跨 block goto 与回边，不能靠词法顺序或回环 blanket guard 判定。
local function cross_entry(start_inside, turn)
    local value
    local round = 0
    if start_inside then goto joined end
    ::fill::
    value = nil
    ::joined::
    if turn then value = true else value = false end
    round = round + 1
    if round < 3 then goto fill end
    return round
end
assert(cross_entry(true, true) == 3)
assert(cross_entry(false, false) == 3)

print("regress_462_boolean_shell_flow_old_values", "OK")
