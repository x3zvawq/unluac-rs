-- 完整 CALL 参数帧消费短路结果的前一 COPY 版本，右臂的比较仍只在选中路径执行。
-- unluac: expect-contains [[print("copy-and",]]
-- unluac: expect-contains [[print("copy-or",]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
local function report(subject, left, right)
    print("copy-and", subject and left ~= right)
    print("copy-or", subject or left == right)
end

local comparisons = 0
local meta = {
    __eq = function(left, right)
        comparisons = comparisons + 1
        return left.value == right.value
    end,
}
local left = setmetatable({ value = 1 }, meta)
local right = setmetatable({ value = 2 }, meta)
report(false, left, right)
assert(comparisons == 1)
report(true, left, right)
assert(comparisons == 2)
report("kept", left, right)
assert(comparisons == 3)
report(nil, left, right)
assert(comparisons == 4)
print("comparisons", comparisons)
