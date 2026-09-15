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
