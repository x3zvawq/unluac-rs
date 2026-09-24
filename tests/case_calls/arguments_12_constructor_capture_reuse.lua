-- 数组准备槽稍后复用为捕获变量，不应让早期数组元素残留为独立声明。
-- unluac: expect-not-contains [[ = 4]]
local function collect(values, ...)
    return values
end
local result = collect({4, 16, 5}, "note", nil, 7)
local empty = collect({"labels"})
local events = {}
local function record(value)
    events[#events + 1] = value
    return events
end
assert(result[1] == 4 and result[2] == 16 and result[3] == 5)
assert(empty[1] == "labels")
assert(record("first") == events and record("second") == events)
assert(table.concat(events, ",") == "first,second")
print("constructor_capture_reuse", "OK")
