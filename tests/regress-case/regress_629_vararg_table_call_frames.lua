-- 原同槽临时值应由循环头、开放变参调用与字段写完整消费。
-- unluac: expect-ast-min [[generic-for]] [[1]]
-- unluac: expect-not-contains [[= ipairs]]
-- unluac: expect-contains [[.extra_count = select("#", ...)]]
-- unluac: expect-contains [[.extra_first = select(1, ...)]]
local function collect(values, ...)
    local result = {
        count = #values,
        first = values[1],
        labels = { "raw", "derived" },
    }
    for index, value in ipairs(values) do
        result[value] = index
    end
    result.extra_count = select("#", ...)
    result.extra_first = select(1, ...)
    return result
end

local result = collect({ 4, 16, 5 }, "note", nil, 7)
assert(result.count == 3 and result.first == 4)
assert(result[4] == 1 and result[16] == 2 and result[5] == 3)
assert(result.labels[1] == "raw" and result.labels[2] == "derived")
assert(result.extra_count == 3 and result.extra_first == "note")
local empty = collect({ "labels" })
assert(empty.labels == 1 and empty.extra_count == 0 and empty.extra_first == nil)
-- 不依赖 select 的 builtin 身份：任意函数也只取首个返回值，字段元方法在 CALL 后执行。
local events = {}
local function fill(target, producer, ...)
    target.value = producer(...)
end
local sink = setmetatable({}, {
    __newindex = function(target, key, value)
        events[#events + 1] = "store:" .. value
        rawset(target, key, value)
    end,
})
fill(sink, function(...)
    assert(select("#", ...) == 3)
    events[#events + 1] = "call"
    return ...
end, 17, nil, 23)
assert(sink.value == 17 and table.concat(events, ",") == "call,store:17")
print("regress_629_vararg_table_call_frames", "OK")
