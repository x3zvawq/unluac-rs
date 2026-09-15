-- 完整条件入口包含外层 callee/左全局读取，不能把首个执行的 CALL 当作入口。
-- unluac: expect-ast-min [[numeric-for]] [[1]]
-- unluac: expect-ast-count [[numeric-for]] [[7]]
-- unluac: expect-ast-min [[if]] [[1]]
local weak = setmetatable({}, {__mode = "v"})
local calls = 0
local left_reads = 0
local old = getmetatable(_G)
local function make()
    calls = calls + 1
    if calls == 2 then
        collectgarbage("collect")
        assert(weak[1] == nil, "old scope result remains rooted")
        print("scope-observed-value", weak[1] ~= nil)
    end
    return "9.125"
end
setmetatable(_G, {__index = function(_, key)
    if key == "condition_entry_left" or key == "condition_entry_key" then
        collectgarbage("collect")
        assert(weak[1] ~= nil, "left lookup must precede the old result overwrite")
        left_reads = left_reads + 1
        return "9.125"
    elseif key == "condition_entry_observe" then
        weak[1] = {}
        return weak[1]
    end
end})
local function nested_call()
    for index = make(), 1, 1 do error("entered") end
    do
        local cleared = nil
        local observed = condition_entry_observe
    end
    if 1 < tonumber(make()) then return 1 else return 2 end
end
assert(nested_call() == 1)
calls = 0
local function left_global()
    for index = make(), 1, 1 do error("entered") end
    do
        local cleared = nil
        local observed = condition_entry_observe
    end
    if condition_entry_left == make() then return 1 else return 2 end
end
assert(left_global() == 1)
calls = 0
local function ordered_left_lookup()
    for index = make(), 1, 1 do error("entered") end
    do
        local cleared = nil
        local observed = condition_entry_observe
    end
    if condition_entry_left < make() then return 1 else return 2 end
end
assert(ordered_left_lookup() == 2)
calls = 0
local function reversed_comparison()
    for index = make(), 1, 1 do error("entered") end
    do
        local cleared = nil
        local observed = condition_entry_observe
    end
    if condition_entry_left > make() then return 1 else return 2 end
end
assert(reversed_comparison() == 2)
calls = 0
local function reversed_inclusive_comparison()
    for index = make(), 1, 1 do error("entered") end
    do
        local cleared = nil
        local observed = condition_entry_observe
    end
    if condition_entry_left >= make() then return 1 else return 2 end
end
assert(reversed_inclusive_comparison() == 1)
calls = 0
local function low_parameter(parameter)
    for index = make(), 1, 1 do error("entered") end
    do
        local cleared = nil
        local observed = condition_entry_observe
    end
    if parameter == make() then return 1 else return 2 end
end
assert(low_parameter("9.125") == 1)
calls = 0
local function table_key(object)
    for index = make(), 1, 1 do error("entered") end
    do
        local cleared = nil
        local observed = condition_entry_observe
    end
    if object[condition_entry_key] == make() then return 1 else return 2 end
end
assert(table_key({["9.125"] = "9.125"}) == 1)
assert(left_reads == 5)
setmetatable(_G, old)
