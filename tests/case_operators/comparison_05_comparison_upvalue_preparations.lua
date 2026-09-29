-- 同一上值的两次读取分别配对自己的原槽与 CALL，不能按上值名复用准备证书。
-- unluac: expect-ast-min [[numeric-for]] [[1]]
-- unluac: expect-ast-count [[numeric-for]] [[2]]
-- unluac: expect-ast-min [[if]] [[1]]
-- unluac: expect-ast-count [[function]] [[3]]
-- unluac: expect-ast-count [[if]] [[4]]
-- unluac: expect-ast-max [[local-binding]] [[16]]
-- unluac: expect-ast-count [[local-binding]] [[7]] [[@proto=3]]
-- unluac: expect-count [[ = for_skip_observe]] [[2]]
-- unluac: expect-count [[ = nil]] [[2]]
local captured = 1
local weak = setmetatable({}, {__mode = "v"})
local observed = {}
local calls = 0
local old = getmetatable(_G)
local function make()
    calls = calls + 1
    if calls % 2 == 0 then
        collectgarbage("collect")
        observed[#observed + 1] = tostring(weak[1] ~= nil)
        local snapshot = captured
        captured = captured + 1
        return snapshot
    end
    return "9.125"
end
setmetatable(_G, {__index = function(_, key)
    if key == "for_skip_observe" then
        weak[1] = {}
        return weak[1]
    end
end})
local function followed()
    for index = make(), 1 do error("entered") end
    do
        local cleared = nil
        local value = for_skip_observe
    end
    if captured ~= make() then error("first read snapshot changed") end
    local prefix = 23
    for index = make(), 1 do error("entered") end
    do
        local cleared = nil
        local value = for_skip_observe
    end
    if captured ~= make() then error("second read snapshot changed") end
    return prefix
end
assert(followed() == 23)
local result = table.concat(observed, ",")
print("repeated-upvalue-snapshot", result, captured, calls)
assert(result == "false,false", "old scope result remains rooted")
assert(captured == 3 and calls == 4, "read or call identity changed")
-- 复用同一原函数，验证每次比较都读取本轮上值，而不是复用上次准备的快照。
captured = -2.5
assert(followed() == 23)
assert(captured == -0.5 and calls == 8)
assert(table.concat(observed, ",") == "false,false,false,false")
assert(select("#", followed()) == 1)
assert(captured == 1.5 and calls == 12)
assert(table.concat(observed, ",") == "false,false,false,false,false,false")
setmetatable(_G, old)
assert(getmetatable(_G) == old)
