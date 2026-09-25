-- 参数与 nil/Boolean 的显式比较无元方法观察，共同返回槽可恢复完整短路树。
-- unluac: expect-ast-count [[if]] [[0]]
-- unluac: expect-contains [[== nil]]
-- unluac: expect-contains [[== false]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
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
