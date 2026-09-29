-- 常量传播可证明未选的 global arm 仍保留；不能删除字节码中实际存在的检查与声明。
-- unluac: expect-not-contains [[if true then]]
-- unluac: expect-not-contains [[if false then]]
-- unluac: expect-contains [[global dead_value]]
-- unluac: expect-ast-count [[if]] [[1]]
-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-ast-count [[error]] [[0]]

global<const> assert, setmetatable, collectgarbage, rawget

local observed = 0
local root_calls = 0
local weak_values = setmetatable({}, { __mode = "v" })
local function make_root()
    root_calls = root_calls + 1
    return {}
end
local literal = 7
local chosen = literal == 7
if chosen then
    observed = 1
else
    global dead_value = 99
    local root_copy = make_root()
    local function dead_callback()
        return observed
    end
    weak_values.value = root_copy
    collectgarbage("collect")
    assert(weak_values.value ~= nil)
    observed = 99
end

assert(observed == 1)
assert(root_calls == 0 and weak_values.value == nil)
assert(rawget(_ENV, "dead_value") == nil)
