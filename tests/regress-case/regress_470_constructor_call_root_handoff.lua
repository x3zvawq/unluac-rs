-- constructor 在 SSA call result 身份尚未合并前消费整个区域，字段接管已结束的物理根。
-- unluac: expect-not-contains [[unluac error]]
local weak = setmetatable({}, { __mode = "v" })
local calls = 0
local function object(index)
    calls = calls + 1
    collectgarbage("collect")
    collectgarbage("collect")
    for previous = 1, index - 1 do
        assert(weak[previous] ~= nil)
    end
    local value = { index = index }
    weak[index] = value
    return value, index
end
local function build()
    return { object(1), object(2), object(3) }
end
local function build_keyed()
    return { [1] = object(1), [2] = object(2), [3] = object(3) }
end
local result = build()
assert(calls == 3 and result[4] == 3 and result[5] == nil)
for index = 1, 3 do
    assert(result[index] == weak[index] and result[index].index == index)
end
result[1] = nil
collectgarbage("collect")
collectgarbage("collect")
assert(weak[1] == nil and weak[2] ~= nil and weak[3] ~= nil)
result[2] = nil
result[3] = nil
collectgarbage("collect")
collectgarbage("collect")
assert(weak[2] == nil and weak[3] == nil)
result = build_keyed()
assert(calls == 6 and result[4] == nil)
for index = 1, 3 do
    assert(result[index] == weak[index] and result[index].index == index)
end
result[1] = nil
result[2] = nil
result[3] = nil
collectgarbage("collect")
collectgarbage("collect")
assert(weak[1] == nil and weak[2] == nil and weak[3] == nil)
print("regress_470_constructor_call_root_handoff", "OK")
