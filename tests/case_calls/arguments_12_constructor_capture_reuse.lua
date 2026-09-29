-- 数组准备槽稍后复用为捕获变量，不应让早期数组元素残留为独立声明。
-- unluac: expect-not-contains [[ = 4]]
-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-ast-count [[local-binding]] [[5]]
-- unluac: expect-ast-count [[table-constructor]] [[3]]
-- unluac: expect-ast-count [[table-list-field]] [[4]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
local function collect(values, ...)
    if values[1] == 4 then
        assert(select("#", ...) == 3)
        assert((...) == "note" and select(2, ...) == nil and select(3, ...) == 7)
    else
        assert(select("#", ...) == 0)
    end
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
assert(empty[1] == "labels" and #empty == 1 and #result == 3 and empty ~= result)
assert(record("first") == events and record("second") == events)
assert(table.concat(events, ",") == "first,second")
print("constructor_capture_reuse", "OK")
