-- 参数与 nil/Boolean 的显式比较无元方法观察，共同返回槽可恢复完整短路树。
-- unluac: expect-ast-count [[if]] [[0]]
-- unluac: expect-count [[== nil]] [[1]]
-- unluac: expect-count [[== false]] [[1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[function]] [[1]]
-- unluac: expect-ast-max [[local-binding]] [[1]]
-- O0 的两个零有独立 LOAD 来源；算术恢复不能丢掉原除法或另建参数中转声明。
-- unluac: expect-count [[0 / 0]] [[1]] [[@variant=O0]]
-- O2 恢复现存函数承接完整内联帧；裸常量比较会在下一轮编译时被错误删除。
-- unluac: expect-not-contains [["none" == "none"]] [[@variant=O2]]
-- unluac: expect-not-contains [["false" == "false"]] [[@variant=O2]]
-- unluac: expect-not-contains [["value" == "value"]] [[@variant=O2]]
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
