-- 比较产生 Boolean，但短路的值臂可以是 nil、false 或对象；谓词和字段读取都只能执行一次。
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=3]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=4]]
-- unluac: expect-ast-count [[function]] [[6]]
-- unluac: expect-ast-count [[numeric-for]] [[2]]
-- unluac: expect-ast-max [[local-binding]] [[23]]
local function equal_and(a, b, source)
    return a == b and source.value
end
local function equal_or(a, b, source)
    return a == b or source.value
end
local function unequal_and(a, b, source)
    return a ~= b and source.value
end
local function unequal_or(a, b, source)
    return a ~= b or source.value
end

local comparisons, reads = 0, 0
local matches, selected
local events = ""
local meta = {__eq = function()
    comparisons = comparisons + 1
    events = events .. "eq,"
    return matches
end}
local left, right = setmetatable({}, meta), setmetatable({}, meta)
local source = setmetatable({}, {__index = function(_, key)
    assert(key == "value")
    reads = reads + 1
    events = events .. "read,"
    return selected
end})
local object = {}
local choices = {false, 0, object, "", true}
for truth = 0, 1 do
    matches = truth == 1
    for choice = 0, 5 do
        selected = choices[choice]
        events = ""
        local before_comparisons, before_reads = comparisons, reads
        local a = equal_and(left, right, source)
        local b = equal_or(left, right, source)
        local c = unequal_and(left, right, source)
        local d = unequal_or(left, right, source)
        if matches then
            assert(rawequal(a, selected) and b == true and c == false and rawequal(d, selected))
            assert(events == "eq,read,eq,eq,eq,read,")
        else
            assert(a == false and rawequal(b, selected) and rawequal(c, selected) and d == true)
            assert(events == "eq,eq,read,eq,read,eq,")
        end
        assert(comparisons == before_comparisons + 4 and reads == before_reads + 2)
    end
end
print("predicate-value-tail", comparisons, reads)
assert(comparisons == 48 and reads == 24)
matches, selected = nil, nil
assert(select("#", equal_and(left, right, source)) == 1)
assert(select("#", equal_or(left, right, source)) == 1)
assert(select("#", unequal_and(left, right, source)) == 1)
assert(select("#", unequal_or(left, right, source)) == 1)
assert(comparisons == 52 and reads == 26)
-- 同一对象的原生相等路径不调用 __eq；字段读取仍由 and/or 决定。
assert(equal_and(left, left, source) == nil)
assert(equal_or(left, left, source) == true)
assert(comparisons == 52 and reads == 27)
