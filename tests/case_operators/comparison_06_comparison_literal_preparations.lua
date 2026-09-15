-- 非内嵌字面量占原 r0；其后外层 callee r1 必须在内层 CALL 的 GC 前覆盖旧观察结果。
-- unluac: expect-ast-count [[numeric-for]] [[2]]
local weak = setmetatable({}, {__mode = "v"})
local calls = 0
local old = getmetatable(_G)
local function make()
    calls = calls + 1
    if calls == 2 then
        collectgarbage("collect")
        assert(weak[1] == nil, "literal preparation moved the subsequent call frame")
        print("literal-preparation", weak[1] ~= nil)
    end
    return "9.125"
end
setmetatable(_G, {__index = function(_, key)
    if key == "comparison_literal_observe" then
        weak[1] = {}
        return weak[1]
    end
end})
local function large_number()
    for index = make(), 1 do error("entered") end
    do
        local cleared = nil
        local value = comparison_literal_observe
    end
    if 1000 < tonumber(make()) then return 1 else return 2 end
end
assert(large_number() == 2)
calls = 0
local function string_order()
    for index = make(), 1 do error("entered") end
    do
        local cleared = nil
        local value = comparison_literal_observe
    end
    if "1" < make() then return 1 else return 2 end
end
assert(string_order() == 1)
setmetatable(_G, old)
