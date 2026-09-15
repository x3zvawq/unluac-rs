-- regress_462_boolean_shell_flow_old_values: 旧值分类沿共享 CFG 的前向入口与回边传播。
-- unluac: expect-not-contains [[not not p1_0]]
-- unluac: expect-not-contains [[if p4_1]]
-- unluac: expect-not-contains [[if not p4_1]]
-- unluac: expect-ast-min [[while]] [[1]]
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

-- 并行交换或清除 holder 时，所有 RHS 必须先读取旧 closure 身份。
local function parallel_observers(flag)
    local left, right
    local read_left = function() return left end
    local read_right = function() return right end
    read_left, read_right = read_right, read_left
    if flag then left = true else left = false end
    if flag then right = false else right = true end
    assert(read_left() == not flag)
    assert(read_right() == flag)
    read_right, read_left = read_left, nil
    if flag then right = true else right = false end
    assert(read_right() == flag)
end
parallel_observers(true)
parallel_observers(false)

-- 删除多个 shell 后，保留语句和子块仍按原 occurrence 路径匹配。
local function deletion_paths(flag)
    local trace = {}
    local value = nil
    if flag then value = true else value = false end
    trace[#trace + 1] = "a"
    do
        local nested = nil
        if flag then nested = true else nested = false end
        trace[#trace + 1] = "b"
        if not flag then nested = true else nested = false end
    end
    if flag then trace[#trace + 1] = "T" else trace[#trace + 1] = "F" end
    if not flag then value = true else value = false end
    trace[#trace + 1] = "c"
    return table.concat(trace)
end
assert(deletion_paths(true) == "abTc")
assert(deletion_paths(false) == "abFc")

-- HIR 中没有通向函数出口的边，但协程挂起会观察循环内读取；后向传播不能从出口单独起步。
local function suspended_reader(flag)
    local value = nil
    if flag then value = true else value = false end
    while true do
        coroutine.yield(value)
    end
end
for _, flag in ipairs({false, true}) do
    local reader = coroutine.create(suspended_reader)
    local ok, value = coroutine.resume(reader, flag)
    assert(ok and value == flag)
    ok, value = coroutine.resume(reader)
    assert(ok and value == flag)
    assert(coroutine.status(reader) == "suspended")
end

-- relay 捕获域外 holder cell，再通过该 cell 读取候选；不能在 closure reaching 前裁掉中间 holder。
local function through_holder(flag)
    local value = nil
    local holder = function() return value end
    local relay = function() return holder() end
    if flag then value = true else value = false end
    return relay()
end
assert(through_holder(true) == true)
assert(through_holder(false) == false)

print("regress_462_boolean_shell_flow_old_values", "OK")
