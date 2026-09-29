-- 参数与 nil/Boolean 的显式比较无元方法观察，共同返回槽可恢复完整短路树。
-- unluac: expect-ast-count [[if]] [[0]]
-- unluac: expect-contains [[== nil]]
-- unluac: expect-contains [[== false]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[function]] [[1]]
-- unluac: expect-ast-max [[local-binding]] [[1]]
local function classify(value)
    return value == nil and "none" or value == false and "false" or "value"
end
assert(classify(nil) == "none")
assert(classify(false) == "false")
assert(classify(true) == "value")
assert(classify(0) == "value")
assert(classify("") == "value")
assert(classify({}) == "value")
print("parameter-comparison-return", "OK")
assert(classify(0 / 0) == "value")
-- 与 nil/false 比较不能调用表的 __eq；若错误调用，error 会使样例直接失败。
assert(classify(setmetatable({}, { __eq = error })) == "value")
assert(classify(nil, "ignored") == "none")
assert(select("#", classify(nil)) == 1)
assert(select("#", classify(false)) == 1)
assert(select("#", classify({})) == 1)
