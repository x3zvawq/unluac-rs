-- 调用结果参与比较后，Boolean 绑定供后继多个调用读取；比较返回值保留原求值帧。
-- unluac: expect-contains [[return left.value == right.value]] [[@debug=retained]]
-- unluac: expect-contains [[local matches = factory(7) == expected]] [[@debug=retained]]
-- unluac: expect-contains [[local misses = factory(8) == expected]] [[@debug=retained]]
-- unluac: expect-contains [[matches = factory(9) == expected]] [[@debug=retained]]
-- unluac: expect-contains [[misses = factory(10) ~= expected]] [[@debug=retained]]
-- unluac: expect-ast-max [[local-decl]] [[8]] [[@proto=0]]
-- unluac: expect-ast-max [[local-binding]] [[8]]
-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-ast-count [[if]] [[1]]
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
local replace_expected = false
local factory = setmetatable({}, {
    __call = function(_, value)
        events = events .. "call"
        if replace_expected then
            expected = setmetatable({ value = value }, meta)
        end
        return setmetatable({ value = value }, meta), "extra"
    end,
})
local matches = factory(7) == expected
assert(matches)
local misses = factory(8) == expected
assert(not misses)
assert(comparisons == 2 and events == "calleqcalleq")
print("call-result-binding", matches, misses, comparisons, events)

assert((factory(7) ~= expected) == false)
assert(factory(8) ~= expected)
assert(matches and misses == false)
assert(comparisons == 4 and events == "calleqcalleqcalleqcalleq")
-- RHS 的 expected 必须在 factory 返回后读取，不能提前快照旧对象。
replace_expected = true
matches = factory(9) == expected
misses = factory(10) ~= expected
assert(matches and misses == false)
assert(comparisons == 6 and events == "calleqcalleqcalleqcalleqcalleqcalleq")
replace_expected = false
expected.value = 0
matches = factory(0) == expected
assert(matches)
expected.value = ""
matches = factory("") == expected
assert(matches)
expected.value = false
matches = factory(false) == expected
assert(matches)
expected.value = nil
matches = factory(nil) == expected
assert(matches)
assert(comparisons == 10 and events == "calleqcalleqcalleqcalleqcalleqcalleqcalleqcalleqcalleqcalleq")
assert(select("#", factory(11)) == 2)
assert(comparisons == 10 and events == "calleqcalleqcalleqcalleqcalleqcalleqcalleqcalleqcalleqcalleqcall")
