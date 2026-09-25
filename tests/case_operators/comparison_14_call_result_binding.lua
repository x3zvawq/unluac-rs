-- 调用结果参与比较后，Boolean 绑定供后继多个调用读取；比较返回值保留原求值帧。
-- unluac: expect-contains [[return left.value == right.value]] [[@debug=retained]]
-- unluac: expect-contains [[local matches = factory(7) == expected]] [[@debug=retained]]
-- unluac: expect-contains [[local misses = factory(8) == expected]] [[@debug=retained]]
-- unluac: expect-ast-max [[local-decl]] [[7]] [[@proto=0]]
-- unluac: expect-not-contains [[ = assert]]
-- unluac: expect-not-contains [[ = print]]
local events = ""
local comparisons = 0
local meta = {
    __eq = function(left, right)
        comparisons = comparisons + 1
        events = events .. "eq"
        return left.value == right.value
    end,
}
local expected = setmetatable({ value = 7 }, meta)
local factory = setmetatable({}, {
    __call = function(_, value)
        events = events .. "call"
        return setmetatable({ value = value }, meta)
    end,
})
local matches = factory(7) == expected
assert(matches)
local misses = factory(8) == expected
assert(not misses)
assert(comparisons == 2 and events == "calleqcalleq")
print("call-result-binding", matches, misses, comparisons, events)
