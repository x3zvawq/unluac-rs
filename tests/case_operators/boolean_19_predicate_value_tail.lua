-- 比较产生 Boolean，但短路的值臂可以是 nil、false 或对象；谓词和字段读取都只能执行一次。
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=3]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=4]]
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
local meta = {__eq = function()
    comparisons = comparisons + 1
    return matches
end}
local left, right = setmetatable({}, meta), setmetatable({}, meta)
local source = setmetatable({}, {__index = function()
    reads = reads + 1
    return selected
end})
local object = {}
local choices = {false, 0, object}
for truth = 0, 1 do
    matches = truth == 1
    for choice = 0, 3 do
        selected = choices[choice]
        local before_comparisons, before_reads = comparisons, reads
        local a = equal_and(left, right, source)
        local b = equal_or(left, right, source)
        local c = unequal_and(left, right, source)
        local d = unequal_or(left, right, source)
        if matches then
            assert(rawequal(a, selected) and b == true and c == false and rawequal(d, selected))
        else
            assert(a == false and rawequal(b, selected) and rawequal(c, selected) and d == true)
        end
        assert(comparisons == before_comparisons + 4 and reads == before_reads + 2)
    end
end
print("predicate-value-tail", comparisons, reads)
