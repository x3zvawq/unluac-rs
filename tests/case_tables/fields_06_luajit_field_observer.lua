-- unluac: expect-ast-max [[local-binding]] [[5]]
-- unluac: expect-ast-max [[assign]] [[0]] [[@proto=0]]
-- unluac: expect-ast-count [[table-constructor]] [[7]]
-- unluac: expect-ast-count [[function]] [[1]]
-- KCDATA常量有GC锚点，但比较仍可调用元方法；字段key快照须随观察epoch失效。
local key = "left"
local calls = 0
debug.setmetatable(1LL, {__eq = function()
    calls = calls + 1
    key = "right"
    return true
end})
local tree = {branches = {left = {score = 4}, right = {score = 9}}}
local result = {
    first = tree.branches[key],
    flipped = 1LL == 2LL,
    second = tree.branches[key],
}
assert(result.first.score == 4 and result.second.score == 9)
assert(result.flipped and calls == 1 and key == "right")
print("cdata-field-epoch", result.first.score, result.second.score, calls, key)

-- 普通比较也应在字段值槽直接物化，不留下查表与 Boolean 接棒变量。
local unchanged = {
    first = tree.branches[key],
    flipped = key == "right",
    second = tree.branches[key],
}
assert(unchanged.first == result.second and unchanged.second == result.second)
assert(unchanged.flipped and calls == 1 and key == "right")
